module Math.AlgebraicNumbers.CReal where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.Interval
import Math.AlgebraicNumbers.UniPoly
import Data.Ratio
import qualified Data.Vector as V
import Data.Maybe (catMaybes)

newtype CReal = CReal [Interval Rational]

cRealFromIntervals :: [Interval Rational] -> CReal
cRealFromIntervals xs = CReal xs

instance Show CReal where
  show _ = "<CReal>"

instance Num CReal where
  negate (CReal xs)   = CReal (map negate xs)
  CReal xs + CReal ys = CReal (zipWith (+) xs ys)
  CReal xs - CReal ys = CReal (zipWith (-) xs ys)
  CReal xs * CReal ys = CReal (zipWith (*) xs ys)
  abs (CReal xs)      = CReal (map abs xs)
  signum (CReal xs)   = error "signum on CReal is not computable"
  fromInteger n       = CReal $ repeat (fromInteger n)

instance Fractional CReal where
  recip (CReal xs) = CReal $ map recip (dropWhile (\(Iv a b) -> a <= 0 && b <= 0) xs)
  fromRational x = CReal $ repeat (fromRational x)

instance IntegralDomain CReal where
  divide = (/)

-- GCDDomain CReal cannot be implemented because they may not terminate

-- may not terminate
unsafeCompareCReal :: CReal -> CReal -> Ordering
unsafeCompareCReal (CReal xs) (CReal ys) = head $ catMaybes (zipWith maybeCompareInterval xs ys)

class IsCReal a where
  toCReal :: a -> CReal
  toIntervals :: a -> [Interval Rational]

instance IsCReal Integer where
  toCReal = fromInteger
  toIntervals = repeat . fromInteger

instance Integral a => IsCReal (Ratio a) where
  toCReal x = fromRational (toRational x)
  toIntervals x = repeat $ fromRational (toRational x)

instance IsCReal CReal where
  toCReal = id
  toIntervals (CReal xs) = xs

valueAtAsCReal :: (IsCReal a, IsCReal b) => a -> UniPoly b -> CReal
valueAtAsCReal t = valueAtT toCReal (toCReal t)

maxCReal :: CReal -> CReal -> CReal
maxCReal (CReal xs) (CReal ys) = CReal (zipWith maxInterval xs ys)

minCReal :: CReal -> CReal -> CReal
minCReal (CReal xs) (CReal ys) = CReal (zipWith minInterval xs ys)

data RoundingMode = RoundTowardNearest
                  | RoundTowardPositive -- or, upward
                  | RoundTowardNegative -- or, downward
                  | RoundTowardZero
                  deriving (Eq,Show)

data AbsRoundingMode = AbsRoundNearest
                     | AbsRoundUpward
                     | AbsRoundDownward

-- Assuming Double is IEEE754 binary64
toDoubleWithRoundingMode :: (Ord a, IsCReal a, Fractional a) => RoundingMode -> a -> Double
toDoubleWithRoundingMode r x = case compare x 0 of
                                 LT -> let rm = case r of
                                             RoundTowardNearest  -> AbsRoundNearest
                                             RoundTowardPositive -> AbsRoundDownward
                                             RoundTowardNegative -> AbsRoundUpward
                                             RoundTowardZero     -> AbsRoundDownward
                                       in - toDoublePositive rm (-x)
                                 EQ -> 0
                                 GT -> let rm = case r of
                                             RoundTowardNearest  -> AbsRoundNearest
                                             RoundTowardPositive -> AbsRoundUpward
                                             RoundTowardNegative -> AbsRoundDownward
                                             RoundTowardZero     -> AbsRoundDownward
                                       in toDoublePositive rm x
  where
    -- 53 == floatDigits (undefined :: Double)
    -- (-1021,1024) == floatRange (undefined :: Double)

    -- <original x> = 2^i * x
    toDoublePositive !r x = case compare x (1/2) of
      LT -> {- 0 < x < 1/2 -} toDoublePositiveSmall r (-1) (2 * x)
      EQ -> 1/2
      GT -> case compare x 1 of
              LT -> {- 1/2 < x < 1 -} loop r (-53) 53 0 x
              EQ -> 1
              GT -> {- 1 < x -} toDoublePositiveLarge r 1 (x / 2)

    -- <original x> = 2^i * x, 0 < x <= 1
    toDoublePositiveSmall !r (-1022) x = {- subnormal, 0 < x <= 1 -} loop r (-1022 - 52) 52 0 x
    toDoublePositiveSmall !r !i x = case compare x (1/2) of
      LT -> {- 0 < x < 1/2 -}    toDoublePositiveSmall r (i - 1) (2 * x)
      EQ -> {- return 2^(i-1) -} encodeFloat 1 (i - 1)
      GT -> {- 1/2 < x < 1 -}    loop r (i - 53) 53 0 x

    maxFiniteDouble :: Double
    maxFiniteDouble = encodeFloat 0x1fffffffffffff (1023 - 52) -- max finite

    nearInfinity :: AbsRoundingMode -> Double
    nearInfinity AbsRoundNearest  = 1 / 0 -- infinity
    nearInfinity AbsRoundUpward   = 1 / 0 -- infinity
    nearInfinity AbsRoundDownward = maxFiniteDouble

    -- <original x> = 2^i * x, 1/2 < x
    toDoublePositiveLarge !r 1025 x = nearInfinity r
    toDoublePositiveLarge !r !i x = case compare x 1 of
      LT -> {- 1/2 < x < 1 -} loop r (i - 53) 53 0 x
      EQ -> {- return 2^i -}  if i == 1024
                              then nearInfinity r
                              else encodeFloat 1 i
      GT -> {- 1 < x -}       toDoublePositiveLarge r (i + 1) (x / 2)

    -- loop _ i j acc x: <original x> = 2^(i+j) * (acc + x), 0 <= x <= 1
    loop AbsRoundNearest !i 0 !acc x = case compare x (1/2) of
                                         LT -> encodeFloat acc i
                                         EQ -> if even acc
                                               then encodeFloat acc i
                                               else encodeFloat (acc + 1) i
                                         GT -> encodeFloat (acc + 1) i
    loop AbsRoundUpward !i 0 !acc x = if x == 0
                                      then encodeFloat acc i
                                      else encodeFloat (acc + 1) i
    loop AbsRoundDownward !i 0 !acc x = if x == 1
                                        then encodeFloat (acc + 1) i
                                        else encodeFloat acc i
    loop !r !i !j !acc x | x <= 1/2  = loop r i (j - 1) (acc * 2)     (x * 2)
                         | otherwise = loop r i (j - 1) (acc * 2 + 1) (x * 2 - 1)

toDouble, toDoubleTowardPositive, toDoubleTowardNegative, toDoubleTowardZero :: (Ord a, IsCReal a, Fractional a) => a -> Double
toDouble               = toDoubleWithRoundingMode RoundTowardNearest
toDoubleTowardPositive = toDoubleWithRoundingMode RoundTowardPositive
toDoubleTowardNegative = toDoubleWithRoundingMode RoundTowardNegative
toDoubleTowardZero     = toDoubleWithRoundingMode RoundTowardZero

-- TODO: Add sqrt, nthRoot, powRat
