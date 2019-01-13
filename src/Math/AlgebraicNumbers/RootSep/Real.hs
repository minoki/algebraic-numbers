module Math.AlgebraicNumbers.RootSep.Real where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.Resultant

-- | Extended real line
data ExtReal a = NegativeInfinity
               | Finite !a
               | PositiveInfinity
               deriving (Eq,Ord,Show)

clamp :: (Ord a) => a -> a -> ExtReal a -> a
clamp lb ub NegativeInfinity = lb
clamp lb ub (Finite x) | x < lb = lb
                       | ub < x = ub
                       | otherwise = x
clamp lb ub PositiveInfinity = ub

-- | Returns the sign of a polynomial at a given point
signAt :: (Ord a, Num a) => a -> UniPoly a -> Int
signAt x p = sign (valueAt x p)

signAtZQ :: Rational -> UniPoly Integer -> Int
signAtZQ x p = sign (valueAtZQ x p)

-- TODO: Better implementation
isZeroAtZQ :: Rational -> UniPoly Integer -> Bool
isZeroAtZQ x p = valueAtZQ x p == 0

-- | Return the sign of a polynomial at a given point in extended real line
signAtX :: (Ord a, Num a) => ExtReal a -> UniPoly a -> Int
signAtX (Finite x) p = signAt x p
signAtX PositiveInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p)
signAtX NegativeInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p) * (-1)^(degree' p)

signAtZQX :: ExtReal Rational -> UniPoly Integer -> Int
signAtZQX (Finite x) p = signAtZQ x p
signAtZQX PositiveInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p)
signAtZQX NegativeInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p) * (-1)^(degree' p)

-- | Negative polynomial remainder sequence using Euclidean PRS
negativePRS_f :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> [UniPoly a]
negativePRS_f f 0 = [f]
negativePRS_f f g = let r = f `modP` g in f : negativePRS_f g (-r)

-- | Negative polynomial remainder sequence using subresultant PRS
--
-- Assumption: 'degree f > degree g'
negativePRS :: (Ord a, IntegralDomain a) => UniPoly a -> UniPoly a -> [UniPoly a]
-- negativePRS f 0 = [f]
negativePRS f g = f : g : loop 1 f 1 g (subresultantPRS' f g)
  where
    loop !_ _ !_ _ [] = []
    loop !s f !t g ((b,x):xs)
      -- b * (lc g)^(degree f - degree g + 1) * s > 0
      | sign b * (sign $ leadingCoefficient g)^(degree' f - degree' g + 1) * s > 0 = -x : loop t g (-1) x xs
      | otherwise = x : loop t g 1 x xs

variance :: [Int] -> Int
variance = loop 0
  where
    loop :: Int -> [Int] -> Int
    loop !n [] = n
    loop !n [_] = n
    loop !n (x:xs@(y:ys))
      | x == 0 = loop n xs
      | y == 0 = loop n (x:ys)
      | x * y < 0 = loop (n + 1) xs
      | otherwise = loop n xs

varianceAt :: (Ord a, Num a) => a -> [UniPoly a] -> Int
varianceAt x ys = variance $ map (signAt x) ys

varianceAtX :: (Ord a, Num a) => ExtReal a -> [UniPoly a] -> Int
varianceAtX x ys = variance $ map (signAtX x) ys

varianceAtZQ :: Rational -> [UniPoly Integer] -> Int
varianceAtZQ x ys = variance $ map (signAtZQ x) ys

varianceAtZQX :: ExtReal Rational -> [UniPoly Integer] -> Int
varianceAtZQX x ys = variance $ map (signAtZQX x) ys

countRealRootsBetween :: (Ord a, Fractional a, IntegralDomain a) => a -> a -> UniPoly a -> Int
countRealRootsBetween a b f = varianceAt a s - varianceAt b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenX :: (Ord a, Fractional a, IntegralDomain a) => ExtReal a -> ExtReal a -> UniPoly a -> Int
countRealRootsBetweenX a b f = varianceAtX a s - varianceAtX b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenZQ :: Rational -> Rational -> UniPoly Integer -> Int
countRealRootsBetweenZQ a b f = varianceAtZQ a s - varianceAtZQ b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenZQX :: ExtReal Rational -> ExtReal Rational -> UniPoly Integer -> Int
countRealRootsBetweenZQX a b f = varianceAtZQX a s - varianceAtZQX b s
  where s = negativePRS f (diffP f)
