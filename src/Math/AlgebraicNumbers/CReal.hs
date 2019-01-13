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

{-
toDouble :: (Ord a, Fractional a) => a -> Double
toDouble x | x == 0 = 0
           | x > 0 = toDoublePositive x
           | x < 0 = - toDoublePositive (-x)
  where toDoublePositive x | x > 1 = 2 * toDoublePositive (x / 2)
-}

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
                                             RoundTowardNearest -> AbsRoundNearest
                                             RoundTowardPositive -> AbsRoundDownward
                                             RoundTowardNegative -> AbsRoundUpward
                                             RoundTowardZero -> AbsRoundDownward
                                       in - toDoublePositive rm 0 (-x)
                                 EQ -> 0
                                 GT -> let rm = case r of
                                             RoundTowardNearest -> AbsRoundNearest
                                             RoundTowardPositive -> AbsRoundUpward
                                             RoundTowardNegative -> AbsRoundDownward
                                             RoundTowardZero -> AbsRoundDownward
                                       in toDoublePositive rm 0 x
  where
    -- <original x> = 2^i * x
    toDoublePositive !rm !i x = case compare x (1/2) of
                                  LT -> toDoublePositive rm (i - 1) (2 * x)
                                  EQ -> encodeFloat 1 (i - 1)
                                  GT -> case compare x 1 of
                                          LT -> loop rm (i - 53) 53 0 x -- 53 == floatDigits (undefined :: Double)
                                          EQ -> encodeFloat 1 i
                                          GT -> toDoublePositive rm (i + 1) (x / 2)
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
    loop !rm !i !j !acc x | x <= 1/2 = loop rm i (j - 1) (acc * 2) (x * 2)
                          | otherwise = loop rm i (j - 1) (acc * 2 + 1) (x * 2 - 1)

toDouble, toDoubleTowardPositive, toDoubleTowardNegative, toDoubleTowardZero :: (Ord a, IsCReal a, Fractional a) => a -> Double
toDouble               = toDoubleWithRoundingMode RoundTowardNearest
toDoubleTowardPositive = toDoubleWithRoundingMode RoundTowardPositive
toDoubleTowardNegative = toDoubleWithRoundingMode RoundTowardNegative
toDoubleTowardZero     = toDoubleWithRoundingMode RoundTowardZero

-- TODO: Add sqrt, nthRoot, powRat
