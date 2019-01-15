module Math.AlgebraicNumbers.AReal where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.MultPoly
import Math.AlgebraicNumbers.Resultant
import Math.AlgebraicNumbers.Interval
import Math.AlgebraicNumbers.CReal
import Math.AlgebraicNumbers.Factor.SquareFree
import Math.AlgebraicNumbers.Factor.Integer
import Math.AlgebraicNumbers.RootSep.Real
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Vector as V
import Data.List
import Data.Ratio

-- | Algebraic real number
data AReal = FromRat !Rational
           | MkAReal !(UniPoly Integer) !Int !Rational !Rational
  deriving (Show)

-- TODO: Implement better 'Show' instance

instance IsAlgebraic AReal where
  definingPolynomial (FromRat x) = definingPolynomial x
  definingPolynomial (MkAReal p _ _ _) = p
  algebraicDegree x = degree' (definingPolynomial x)

-- | Isolating interval for the real root
isolatingInterval :: AReal -> Interval Rational
isolatingInterval (FromRat x) = Iv x x
isolatingInterval (MkAReal _ _ x y) = Iv x y

-- | Returns the intervals that converge to a root of polynomial
intervalsWithSign :: UniPoly Integer -> Int -> Rational -> Rational -> [Interval Rational]
intervalsWithSign !f !s !a !b = Iv a b : ivs a b
  where
    ivs !a !b | signAtZQ c f == 0 = repeat (Iv c c)
              | s * signAtZQ c f < 0 = Iv c b : ivs c b
              | s * signAtZQ c f > 0 = Iv a c : ivs a c
      where c = (a + b) / 2

instance IsCReal AReal where
  toCReal x = CReal (toIntervals x)
  toIntervals (FromRat x) = repeat (Iv x x)
  toIntervals (MkAReal f s a b) = intervalsWithSign f s a b

-- | Constructs an algebraic real number from an irreducible polynomial and an isolating interval \((a,b]\)
mkARealWithIrreduciblePoly :: UniPoly Integer -> Rational -> Rational -> AReal
mkARealWithIrreduciblePoly f a b

  -- Error if the interval is empty
  | b < a = error "mkAReal: empty interval"

  -- The root is a rational number if the polynomial is of degree 1
  | degree f == Just 1 = case V.toList (coeff f) of
                           [a,b] -> FromRat (-a % b)

  -- The sign of the isolating interval must be definite
  | otherwise = MkAReal f s a' b'
  where s | signAtZQ b f > 0 = 1
          | signAtZQ b f < 0 = -1
          | otherwise = error "mkAReal: the polynomial is not irreducible"
        Just (Iv a' b') = find (\(Iv x y) -> 0 < x || y < 0) (intervalsWithSign f s a b)

-- | Constructs an algebraic real number from a polynomial and a computable real number
mkARealWithCReal :: UniPoly Integer -> CReal -> AReal
mkARealWithCReal f cr = sieve squareFreeFactors (toIntervals cr)
  where
    squareFreeFactors :: [UniPoly Integer]
    squareFreeFactors = map fst $ yunSFF $ primitivePart f

    sieve :: [UniPoly Integer] -> [Interval Rational] -> AReal
    sieve [] _ = error "invalid real number"
    sieve [g] xs = sieve2 (unsafePerformIO (factorIntegerIO g)) xs -- the order may be random, but it is fine because the result is reduced to one
    sieve gs (x:xs) = sieve (filter (\g -> isCompatibleWithZero (valueAtZ x g)) gs) xs

    sieve2 :: [UniPoly Integer] -> [Interval Rational] -> AReal
    sieve2 [] _ = error "invalid real number"
    sieve2 [g] xs = case dropWhile (\(Iv a b) -> countRealRootsBetweenZQ a b g >= 2) xs of
                      Iv a b : _ -> mkARealWithIrreduciblePoly g a b
    sieve2 gs (x:xs) = sieve2 (filter (\g -> isCompatibleWithZero (valueAtZ x g)) gs) xs

rootBound :: UniPoly Integer -> Rational
rootBound f | f == 0 = error "rootBound: polynomial is zero"
            | otherwise = 1 + (V.maximum $ V.map (abs . (% lc)) $ V.init $ coeff f)
  where lc = leadingCoefficient f

instance Eq AReal where
  -- Rational numbers
  FromRat x == FromRat y = x == y

  -- A rational number and an algebraic real number
  FromRat x == y = False

  -- An algebraic real number and a rational number
  x == FromRat y = False

  -- Algebraic real numbers
  x == y
    | b  <= a' = False  -- The intervals don't overlap
    | b' <= a  = False  -- The intervals don't overlap
    | otherwise = f == f'
    where f = definingPolynomial x
          Iv a b = isolatingInterval x
          f' = definingPolynomial y
          Iv a' b' = isolatingInterval y

instance Ord AReal where
  -- Rational numbers
  compare (FromRat x) (FromRat y) = compare x y

  -- A rational number and an algebraic real number
  compare (FromRat x) y
    | x <= a = LT
    | b <= x = GT
    | countRealRootsBetweenZQ x b f == 1 = LT
    | otherwise = GT
    where f = definingPolynomial y
          Iv a b = isolatingInterval y

  -- An algebraic real number and a rational number
  compare x (FromRat y)
    | y <= a = GT
    | b <= y = LT
    | countRealRootsBetweenZQ y b f == 1 = GT
    | otherwise = LT
    where f = definingPolynomial x
          Iv a b = isolatingInterval x

  -- Algebraic real numbers
  compare x y
    | b  <= a' = LT -- The intervals don't overlap
    | b' <= a  = GT -- The intervals don't overlap

    | countRealRootsBetweenZQ a'' b'' g == 1 = EQ -- Check if they are equal

    -- Now @x@ and @y@ are not equal, so compare them as computable real numbers
    | otherwise = unsafeCompareCReal (toCReal x) (toCReal y)

    where f = definingPolynomial x
          Iv a b = isolatingInterval x
          f' = definingPolynomial y
          Iv a' b' = isolatingInterval y
          g = gcdD f f'
          a'' = max a a'
          b'' = min b b'

instance Num AReal where
  negate (FromRat x) = FromRat (negate x)
  negate (MkAReal f s a b) = MkAReal (compP f (-ind)) (-s) (-b) (-a)

  FromRat x + FromRat y = FromRat (x + y)
  FromRat k + MkAReal f s a b = mkARealWithIrreduciblePoly (primitivePart $ fst $ homogeneousCompP f (definingPolynomial k) (denominator k)) (a + k) (b + k)
  x@(MkAReal _ _ _ _) + y@(FromRat _) = y + x
  x + y = mkARealWithCReal (resultant f_x_y g) (toCReal x + toCReal y)
    where f = mapCoeff constP $ definingPolynomial x
          f_x_y = compP f (constP ind - ind) -- f(x-y)
          g = mapCoeff constP $ definingPolynomial y

  FromRat x - FromRat y = FromRat (x - y)
  FromRat k - MkAReal f s a b = mkARealWithIrreduciblePoly (primitivePart $ fst $ homogeneousCompP f (- definingPolynomial k) (denominator k)) (k - b) (k - a)
  MkAReal f s a b - FromRat k = mkARealWithIrreduciblePoly (primitivePart $ fst $ homogeneousCompP f (definingPolynomial (-k)) (denominator k)) (a - k) (b - k)
  x - y = mkARealWithCReal (resultant f_x_y g) (toCReal x - toCReal y)
    where f = mapCoeff constP $ definingPolynomial x
          f_x_y = compP f (constP ind + ind) -- f(x+y)
          g = mapCoeff constP $ definingPolynomial y

  FromRat x * FromRat y = FromRat (x * y)
  FromRat k * MkAReal f s a b
    | k == 0 = 0
    | k > 0 = MkAReal (primitivePart f_x_k) s (a * k) (b * k)
    | k < 0 = MkAReal (primitivePart f_x_k) (-s) (b * k) (a * k)
    where f_x_k = fst $ homogeneousValueAt (scaleP (denominator k) ind) (fromInteger $ numerator k) (mapCoeff fromInteger f) -- f(x/k)

  x@(MkAReal _ _ _ _) * y@(FromRat _) = y * x
  x * y = mkARealWithCReal (resultant y_f_x_y g) (toCReal x * toCReal y)
    where f = definingPolynomial x
          y_f_x_y = UniPoly $ V.reverse $ V.imap (\i a -> constP a * ind^i) $ coeff f -- y^n f(x/y)
          g = mapCoeff constP $ definingPolynomial y

  abs x | x >= 0 = x
        | otherwise = negate x

  signum x | x > 0 = 1
           | x == 0 = 0
           | x < 0 = -1

  fromInteger n = FromRat (fromInteger n)

instance Fractional AReal where
  recip (FromRat x) = FromRat (recip x)
  recip (MkAReal f s a b) = MkAReal (UniPoly $ V.reverse $ coeff f) s' (recip b) (recip a)
    where s' | even (degree' f) || 0 < a = -s
             | otherwise = s

  fromRational = FromRat

instance IntegralDomain AReal where
  divide = (/)

instance GCDDomain AReal where
  gcdD = fieldGcd
  lcmD = fieldLcm
  contentV = fieldContentV

-- | Square root of a rational number
sqrtQ :: Rational -> AReal
sqrtQ a | a > 0 = case realRootsBetweenQ (ind^2 - constP a) (Finite 0) PositiveInfinity of
            [sqrt_a] -> sqrt_a
            _ -> error "sqrt: none or multiple roots"
        | a == 0 = 0
        | otherwise = error "sqrt: negative"

-- | Square root of an algebraic real number
sqrtA :: AReal -> AReal
sqrtA (FromRat x) = sqrtQ x
sqrtA x = case filter (\y -> FromRat a < y^2 && y^2 <= FromRat b) $ realRootsBetween (compP f (ind^2)) (Finite 0) PositiveInfinity of
                          [sqrtx] -> sqrtx
                          r -> error $ "sqrt: none or multiple roots" ++ show r
    where f = definingPolynomial x
          Iv a b = isolatingInterval x

-- | n-th root of a rational number
nthRootQ :: Int -> Rational -> AReal
nthRootQ !n !a
  | n == 0 = error "0th root"
  | n < 0  = nthRootQ (-n) (recip a)
  | a > 0  = case realRootsBetweenQ (ind^n - constP a) (Finite 0) PositiveInfinity of
               [b] -> b
               l -> error ("nthRoot: none or multiple roots " ++ show l)
  | a == 0 = 0
  | odd n  = case realRootsBetweenQ (ind^n - constP a) NegativeInfinity (Finite 0) of
               [b] -> b
               l -> error ("nthRoot: none or multiple roots " ++ show l)
  | otherwise = error "nthRoot: negative"

-- | n-th root of an algebraic real number
nthRootA :: Int -> AReal -> AReal
nthRootA !n (FromRat x) = nthRootQ n x
nthRootA !n x
  | n == 0 = error "0th root"
  | n < 0  = nthRootA (-n) (recip x)
  -- now n must be positive
  | x == 0 = 0
  | x > 0  = case filter (\x -> FromRat a < x^n && x^n <= FromRat b) $ realRootsBetween (compP f (ind^n)) (Finite 0) PositiveInfinity of
               [rx] -> rx
               _ -> error "nthRoot: none or multiple roots"
  -- x must be negative
  | odd n  = case filter (\x -> FromRat a < x^n && x^n <= FromRat b) $ realRootsBetween (compP f (ind^n)) NegativeInfinity (Finite 0) of
               [rx] -> rx
               _ -> error "nthRoot: none or multiple roots"
  | otherwise = error "nthRoot: negative"
  where f = definingPolynomial x
        Iv a b = isolatingInterval x

-- | Compute the power of an algebraic real number to an integer
powIntA :: AReal -> Int -> AReal
powIntA _ 0 = 1
powIntA x n | n < 0 = recip $ powIntA x (-n)
powIntA (FromRat x) n = FromRat (x^n)
powIntA x n = mkARealWithCReal h ((toCReal x)^n)
  where g = mapCoeff fromInteger $ definingPolynomial x
        h = resultant g (constP ind - ind^n)

powRatA :: AReal -> Rational -> AReal
powRatA x y = nthRootA (fromInteger $ denominator y) (powIntA x (fromInteger $ numerator y))

valueAtA :: AReal -> UniPoly Integer -> AReal
valueAtA (FromRat x) f = FromRat (valueAtZQ x f)
valueAtA x f = mkARealWithCReal h (valueAtAsCReal x f)
  where g = mapCoeff fromInteger $ definingPolynomial x
        h = resultant g (constP ind - mapCoeff fromInteger f)

toMultPoly :: (Eq a, Num a) => UniPoly a -> MultPoly (UniPoly Integer)
toMultPoly 0 = 0
toMultPoly f = sum [multInd i * Scalar (ind^i) | i <- [0..degree' f]]

-- Eliminate algebraic numbers in the coefficients by multiplying conjugates
elimN :: (Eq a, Num a, IsAlgebraic a) => UniPoly a -> UniPoly Integer
elimN f = case multToScalar (foldl' elimOne (toMultPoly f) (coeff f)) of
            Just g -> g
            Nothing -> error "elimN: internal error"
  where
    elimOne :: (IsAlgebraic a) => MultPoly (UniPoly Integer) -> a -> MultPoly (UniPoly Integer)
    elimOne m a = resultant (mapCoeff (Scalar . constP) $ definingPolynomial a) (multToUni m)
-- Specialize for Integer/Rational?

toMultPoly2 :: (Eq a, Num a) => UniPoly (UniPoly a) -> MultPoly (UniPoly (UniPoly Integer))
toMultPoly2 0 = 0
toMultPoly2 f = sum [multInd i * Scalar (ind^i) | i <- [0..degree' f]]

realRoots :: UniPoly Integer -> [AReal]
realRoots f = map fst (realRootsM f)

realRootsM :: UniPoly Integer -> [(AReal,Int)]
realRootsM f = realRootsBetweenM f NegativeInfinity PositiveInfinity

-- | Returns the real roots of a polynomial in an interval
--
-- The polynomial cannot be zero.
realRootsBetweenM :: UniPoly Integer -> ExtReal Rational -> ExtReal Rational -> [(AReal,Int)]
realRootsBetweenM f lb ub
  | f == 0 = error "realRoots: zero"
  | degree' f == 0 = []
  | otherwise = sortOn fst $ do
      (g,i) <- yunSFF (primitivePart f)
      h <- unsafePerformIO (factorIntegerIO g) -- the order of the factors is depends on the global state, but it is fine because it is sorted afterwards
      let seq = negativePRS h (diffP h)
          bound = rootBound h
          lb' = clamp (-bound) bound lb
          ub' = clamp (-bound) bound ub
      a <- bisect h seq (lb',varianceAtZQX lb seq) (ub',varianceAtZQX ub seq)
      return (a,i)
  where
    bisect :: UniPoly Integer -> [UniPoly Integer] -> (Rational,Int) -> (Rational,Int) -> [AReal]
    bisect f seq p@(a,i) q@(b,j)
      | i <= j     = []
      | i == j + 1 = [mkARealWithIrreduciblePoly f a b]
      | otherwise  = bisect f seq p r ++ bisect f seq r q
      where c = (a + b) / 2
            r = (c,varianceAtZQ c seq)

realRootsBetween :: UniPoly Integer -> ExtReal Rational -> ExtReal Rational -> [AReal]
realRootsBetween f lb ub = map fst (realRootsBetweenM f lb ub)

realRootsBetweenQ :: (IsRational a) => UniPoly a -> ExtReal Rational -> ExtReal Rational -> [AReal]
realRootsBetweenQ = realRootsBetween . integralPrimitivePart

realRootsA :: (Ord a, IsAlgebraicReal a, GCDDomain a) => UniPoly a -> [(AReal,Int)]
realRootsA f = [ (x,i)
               | (g,i) <- yunSFF f
               , x <- realRoots (elimN g)
               -- want to test valueAt x g == 0
               , let y' = toIntervals $ valueAtAsCReal x g
               , isCompatibleWithZero (y' !! 5)
               , let Iv x0 x1 = isolatingInterval x
               , let g' = mapCoeff toAReal g
               , signAt (fromRational x0) g' * signAt (fromRational x1) g' <= 0
               ]
-- Specialize for Integer / Rational coefficient polynomials?

realRootsA' :: (Ord a, IsAlgebraicReal a, GCDDomain a) => UniPoly a -> [(AReal,Int)]
realRootsA' f = [ (x,i)
                | (g,i) <- yunSFF f
                , x <- realRoots (elimN g)
                , let Iv x0 x1 = isolatingInterval x
                , let g' = mapCoeff toAReal g
                , signAt (fromRational x0) g' * signAt (fromRational x1) g' <= 0
                ]

algRealToDouble :: AReal -> Double
algRealToDouble x = case (toIntervals x) !! 50 of
  Iv a b -> fromRational (a + b) / 2

algRealToDoubleI :: Interval AReal -> Double
algRealToDoubleI (Iv x y) = case (toIntervals (x {-+ y-})) !! 50 of
  Iv a b -> fromRational (a + b) / 2

-- Should add Ord as a superclass?
class (IsAlgebraic a, IsCReal a) => IsAlgebraicReal a where
  toAReal :: a -> AReal

instance IsAlgebraicReal Integer where
  toAReal = fromInteger

instance (Integral a) => IsAlgebraicReal (Ratio a) where
  toAReal = fromRational . toRational

instance IsAlgebraicReal AReal where
  toAReal = id
