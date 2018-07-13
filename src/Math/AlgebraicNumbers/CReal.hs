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
valueAtAsCReal t (UniPoly xs) = V.foldr' (\a b -> toCReal a + toCReal t * b) 0 xs

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

{-
toDouble :: (Ord a, IsCReal a, Fractional a) => a -> Double
toDouble x | x == 0 = 0
           | x > 0 = toDoublePositive x
           | x < 0 = - toDoublePositive (-x)
  where
    toDoublePositive x | x < 1/2 = 1/2 * toDoublePositive (2 * x)
                       | x > 1 = 2 * toDoublePositive (x / 2)
                       | x == 1/2 = 1/2
                       | x == 1 = 1
                       | 
-}

-- TODO: Add sqrt, nthRoot, powRat
