module Math.AlgebraicNumbers.Interval where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class

-- Iv a b represents the interval [a,b]
data Interval a = Iv !a !a
  deriving (Show)

lo (Iv a _) = a
hi (Iv _ b) = b

width :: (Num a) => Interval a -> a
width (Iv a b) = b - a

instance (Num a, Ord a) => Num (Interval a) where
  negate (Iv a b) = Iv (-b) (-a)
  Iv a b + Iv c d = Iv (a + c) (b + d)
  Iv a b - Iv c d = Iv (a - d) (b - c)
  Iv a b * Iv c d = Iv (minimum [a*c,a*d,b*c,b*d]) (maximum [a*c,a*d,b*c,b*d])
  abs x@(Iv a b) | 0 <= a = x
                 | b <= 0 = -x
                 | otherwise = Iv 0 (max (-a) b)
  signum (Iv a b) | 0 < a            = 1
                  | b < 0            = -1
                  | a == 0 && b == 0 = 0
                  | 0 <= a           = Iv 0 1
                  | b <= 0           = Iv (-1) 0
                  | otherwise        = Iv (-1) 1
  fromInteger n = Iv (fromInteger n) (fromInteger n)

instance (Fractional a, Ord a) => Fractional (Interval a) where
  recip (Iv a b) | 0 < a || b < 0 = Iv (recip b) (recip a)
                 | otherwise = error "divide by zero"
  fromRational x = Iv (fromRational x) (fromRational x)

maybeCompareInterval :: (Ord a) => Interval a -> Interval a -> Maybe Ordering
maybeCompareInterval (Iv a b) (Iv c d)
  | b < c = Just LT
  | d < a = Just GT
  | a == d && b == c = Just EQ
  -- b <= c = LE
  -- d <= a = GE
  | otherwise = Nothing

isCompatibleWithZero :: (Num a, Ord a) => Interval a -> Bool
isCompatibleWithZero (Iv a b) = a <= 0 && 0 <= b

compatible :: (Ord a) => Interval a -> Interval a -> Bool
compatible (Iv a b) (Iv a' b') = a <= b' && a' <= b

maxInterval :: (Ord a) => Interval a -> Interval a -> Interval a
maxInterval (Iv a b) (Iv a' b') = Iv (max a a') (max b b')

minInterval :: (Ord a) => Interval a -> Interval a -> Interval a
minInterval (Iv a b) (Iv a' b') = Iv (min a a') (min b b')

-- Assume f preserves the order
unsafeMapInterval :: (a -> b) -> Interval a -> Interval b
unsafeMapInterval f (Iv x y) = Iv (f x) (f y)
