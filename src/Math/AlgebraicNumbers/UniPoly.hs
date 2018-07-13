module Math.AlgebraicNumbers.UniPoly where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import qualified Data.Vector as V
import Data.Vector ((!))
import Data.Ratio
import qualified Prelude

-- | Univariate polynomial
--
-- The polynomial is represented by the vector of coefficients
newtype UniPoly a = UniPoly (V.Vector a)
   deriving (Eq,Show)

mkUniPoly :: (Eq a, Num a) => V.Vector a -> UniPoly a
mkUniPoly xs | V.null xs || V.last xs /= 0 = UniPoly xs
             | otherwise = error "UniPoly: error"

instance (Eq a, Num a) => Num (UniPoly a) where
  negate (UniPoly xs) = UniPoly $ V.map negate xs

  UniPoly xs + UniPoly ys
    | n < m = UniPoly $ V.accumulate (+) ys (V.indexed xs)
    | m < n = UniPoly $ V.accumulate (+) xs (V.indexed ys)
    | n == m = fromCoeff $ V.zipWith (+) xs ys
    where n = V.length xs
          m = V.length ys

  -- multiplication: naive method
  UniPoly xs * UniPoly ys
    | n == 0 || m == 0 = zeroP
    | otherwise = UniPoly $ V.generate (n + m - 1) (\i -> sum [(xs ! j) * (ys ! (i - j)) | j <- [0..i], j < n, i - j < m])
    where n = V.length xs
          m = V.length ys

  fromInteger n = constP $ fromInteger n

  -- these should be kicked out of 'Num' class...
  abs = error "abs of a polynomial is nonsense"
  signum = error "signum of a polynomial is nonsense"

instance (Eq a, IntegralDomain a) => IntegralDomain (UniPoly a) where
  divide f g
    | g == 0 = error "divide: divide by zero"
    | degree f < degree g = zeroP -- f should be zero
    | otherwise = loop zeroP f
    where
      l = degree' f - degree' g + 1
      b = leadingCoefficient g
      -- invariant: f == q * g + r
      loop q r | degree r < degree g = q -- r should be zero
               | otherwise = loop (q + q') (r - q' * g)
        where q' = unscaleP b (UniPoly (V.drop (degree' g) (coeff r)))

gcdWithSubresultantPRS :: (Eq a, IntegralDomain a) => UniPoly a -> UniPoly a -> UniPoly a
gcdWithSubresultantPRS f 0 = f
gcdWithSubresultantPRS f g
  | degree f < degree g = gcdWithSubresultantPRS g f
  | otherwise = case pseudoModP f g of
      0 -> g
      rem -> let !d = degree' f - degree' g
                 !s = (-1)^(d + 1) * rem
             in loop d (-1) g s
  where
    loop !_ _ f 0 = f
    loop !d psi f g = case pseudoModP f g of
      0 -> g
      rem -> let !d' = degree' f - degree' g
                 !c = leadingCoefficient f
                 !psi' | d == 0 = psi
                       | d > 0 = ((-c)^d) `divide` (psi^(d-1))
                 !beta = -c * psi' ^ d'
                 !s = unscaleP beta rem
             in loop d' psi' g s

instance (Eq a, GCDDomain a) => GCDDomain (UniPoly a) where
  gcdD x y = let (xc,xp) = contentAndPrimitivePart x
                 (yc,yp) = contentAndPrimitivePart y
             in scaleP (gcdD xc yc) $ primitivePart (gcdWithSubresultantPRS xp yp)
  contentV xs | V.null xs = 0
              | otherwise = scaleP (contentV (V.map fst ys)) $ gcdV 0 (V.map snd ys)
    where
      ys = V.map contentAndPrimitivePart xs
      gcdV 1 _ = 1
      gcdV a v | V.null v = a
               | otherwise = gcdV (primitivePart $ gcdWithSubresultantPRS (V.last v) a) (V.init v)

instance (Eq a, Fractional a, GCDDomain a) => EuclideanDomain (UniPoly a) where
  divModD = divModP

-- | Zero polynomial
zeroP :: UniPoly a
zeroP = UniPoly V.empty

-- | Constant polynomial
constP :: (Eq a, Num a) => a -> UniPoly a
constP 0 = zeroP
constP a = UniPoly (V.singleton a)

-- | Indeterminate
ind :: (Num a) => UniPoly a
ind = UniPoly (V.fromList [0,1])

-- | Coefficients of a polynomial as a vector, in ascending order
coeff :: UniPoly a -> V.Vector a
coeff (UniPoly xs) = xs

-- | Coefficients of a polynomial as a list, in ascending order
coeffListAsc :: UniPoly a -> [a]
coeffListAsc (UniPoly xs) = V.toList xs

-- | Coefficients of a polynomial as a list, in descending order
coeffListDesc :: UniPoly a -> [a]
coeffListDesc (UniPoly xs) = V.toList (V.reverse xs)

-- | Construct a polynomial from coefficients, in ascending order
fromCoeff :: (Eq a, Num a) => V.Vector a -> UniPoly a
fromCoeff xs
  | V.null xs      = zeroP
  | V.last xs == 0 = fromCoeff (V.init xs)
  | otherwise      = UniPoly xs

-- | Construct a polynomial from coefficients, in ascending order
fromCoeffListAsc :: (Eq a, Num a) => [a] -> UniPoly a
fromCoeffListAsc = fromCoeff . V.fromList

-- | Construct a polynomial from coefficients, in ascending order
fromCoeffListDesc :: (Eq a, Num a) => [a] -> UniPoly a
fromCoeffListDesc = fromCoeff . V.reverse . V.fromList

mapCoeff :: (Eq b, Num b) => (a -> b) -> UniPoly a -> UniPoly b
mapCoeff f = fromCoeff . fmap f . coeff

unsafeMapCoeff :: (a -> b) -> UniPoly a -> UniPoly b
unsafeMapCoeff f = UniPoly . fmap f . coeff

-- | Degree of a polynomial
--
-- Returns @Nothing@ if the polynomial is zero.
degree :: UniPoly a -> Maybe Int
degree (UniPoly xs) = case V.length xs - 1 of
  -1 -> Nothing
  n -> Just n

-- | Degree of a polynomial
--
-- Raises an error if the polynomial is zero
degree' :: UniPoly a -> Int
degree' (UniPoly xs) = case V.length xs of
  0 -> error "degree': zero polynomial"
  n -> n - 1

-- | Leading coefficient
leadingCoefficient :: (Num a) => UniPoly a -> a
leadingCoefficient (UniPoly xs)
  | V.null xs = 0
  | otherwise = V.last xs

-- | Convert a polynomial to monic, by dividing by the leading coefficient
toMonic :: (Fractional a) => UniPoly a -> UniPoly a
toMonic f@(UniPoly xs)
  | V.null xs = zeroP
  | otherwise = UniPoly $ V.map (* recip (leadingCoefficient f)) xs

-- | Scalar multiplication
scaleP :: (Eq a, Num a) => a -> UniPoly a -> UniPoly a
scaleP a (UniPoly xs)
  | a == 0 = zeroP
  | otherwise = UniPoly $ V.map (* a) xs

-- | Division by a scalar
unscaleP :: (Eq a, IntegralDomain a) => a -> UniPoly a -> UniPoly a
unscaleP a f = mapCoeff (`divide` a) f

valueAt :: (Num a) => a -> UniPoly a -> a
valueAt t (UniPoly xs) = V.foldr' (\a b -> a + t * b) 0 xs

valueAtZQ :: Rational -> UniPoly Integer -> Rational
valueAtZQ t (UniPoly xs) = V.foldr' (\a b -> fromInteger a + t * b) 0 xs

valueAtZ :: (Num a) => a -> UniPoly Integer -> a
valueAtZ t (UniPoly xs) = V.foldr' (\a b -> fromInteger a + t * b) 0 xs

valueAtT :: (Num a) => (b -> a) -> a -> UniPoly b -> a
valueAtT f t (UniPoly xs) = V.foldr' (\a b -> f a + t * b) 0 xs

-- homogeneousValueAt x y (a_n X^n + ... + a_1 X + a_0)
-- = (a_n x^n + a_{n-1} x^{n-1} y + ... + a_1 x y^{n-1} + a_0 y^n, y^n)
homogeneousValueAt :: (Eq a, Num a) => a -> a -> UniPoly a -> (a, a)
homogeneousValueAt num den f@(UniPoly coeff)
  | f == 0 = (0, 1)
  | otherwise = (V.foldr' (\x y -> x + num * y) 0 $ V.zipWith (*) coeff denseq, V.head denseq)
  where
    -- numseq = V.iterateN (V.length coeff) (* num) 1
    denseq = V.reverse (V.iterateN (V.length coeff) (* den) 1)

-- @f `compP` g = f(g(x))@
compP :: (Eq a, Num a) => UniPoly a -> UniPoly a -> UniPoly a
compP (UniPoly xs) g = V.foldr' (\a b -> constP a + g * b) 0 xs

-- homogeneousCompP (a_n X^n + ... + a_1 X + a_0) g d
-- = (a_n g^n + a_{n-1} g^{n-1} d + ... + a_1 g d^{n-1} + a_0 d^n, d^n)
homogeneousCompP :: (Eq a, Num a) => UniPoly a -> UniPoly a -> a -> (UniPoly a, a)
homogeneousCompP f@(UniPoly coeff) g den
  | f == 0 = (0, 1)
  | otherwise = (V.foldr' (\x y -> constP x + g * y) 0 $ V.zipWith (*) coeff denseq, V.head denseq)
  where
    denseq = V.reverse (V.iterateN (V.length coeff) (* den) 1)

divModP :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> (UniPoly a, UniPoly a)
divModP f g
  | g == 0    = error "divModP: divide by zero"
  | degree f < degree g = (zeroP, f)
  | otherwise = loop zeroP (scaleP (recip b) f)
  where
    g' = toMonic g
    b = leadingCoefficient g
    -- invariant: f == q * g + scaleP b p
    loop q p | degree p < degree g = (q, scaleP b p)
             | otherwise = let q' = UniPoly (V.drop (degree' g) (coeff p))
                           in loop (q + q') (p - q' * g')

divP f g = fst (divModP f g)
modP f g = snd (divModP f g)

-- | GCD with naive Euclidean algorithm
gcdP :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> UniPoly a
gcdP f g | g == 0    = f
         | otherwise = gcdP g (f `modP` g)

monicGcdP :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> UniPoly a
monicGcdP f g | g == 0    = f
              | otherwise = monicGcdP g (toMonic (f `modP` g))

diffP :: (Eq a, Num a) => UniPoly a -> UniPoly a
diffP (UniPoly xs)
  | null xs = zeroP
  | otherwise = fromCoeff $ V.tail $ V.imap (\i x -> fromIntegral i * x) xs

squareFree :: (Eq a, GCDDomain a) => UniPoly a -> UniPoly a
squareFree f = f `divide` gcdD f (diffP f)

pseudoDivModP :: (Eq a, Num a) => UniPoly a -> UniPoly a -> (UniPoly a, UniPoly a)
pseudoDivModP f g
  | g == 0 = error "pseudoDivModP: divide by zero"
  | degree f < degree g = (zeroP, f)
  | otherwise = case loop 0 zeroP f of
      (i,q,r) -> (scaleP (b^(l-i)) q, scaleP (b^(l-i)) r)
  where
    l = degree' f - degree' g + 1
    b = leadingCoefficient g
    -- invariant: scaleP i f == q * g + r
    loop i q r | degree r < degree g = (i, q, r)
               | otherwise = let q' = UniPoly (V.drop (degree' g) (coeff r))
                             in loop (i + 1) (scaleP b q + q') (scaleP b r - q' * g)

pseudoDivP f g = fst (pseudoDivModP f g)
pseudoModP f g = snd (pseudoDivModP f g)

-- | Returns the content of a polynomial
content :: (GCDDomain a) => UniPoly a -> a
content (UniPoly xs) = contentV xs

-- | Returns the content and primitive part of a polynomial
contentAndPrimitivePart :: (Eq a, GCDDomain a) => UniPoly a -> (a, UniPoly a)
contentAndPrimitivePart f
  | c == 1 = (c, f)
  | otherwise = (c, unscaleP c f)
  where c = content f

-- | Returns the primitive part of a polynomial
primitivePart :: (Eq a, GCDDomain a) => UniPoly a -> UniPoly a
primitivePart = snd . contentAndPrimitivePart

-- | Division by a monic polynomial
monicDivMod :: (Eq a, Num a) => UniPoly a -> UniPoly a -> (UniPoly a, UniPoly a)
monicDivMod f g
  -- leadingCoefficient g must be 1
  | leadingCoefficient g /= 1 = error "monicDivMod: g must be monic"
  | otherwise = loop zeroP f
  where
    -- invariant: f == q * g + r
    loop q r | degree r < degree g = (q, r)
             | otherwise = loop (q + q') (r - q' * g)
      where q' = UniPoly (V.drop (degree' g) (coeff r))

integralPrimitivePart :: (IsRational a) => UniPoly a -> UniPoly Integer
integralPrimitivePart f = let commonDenominator = V.foldl' (\a b -> Prelude.lcm a (denominator (toRational b))) 1 (coeff f)
                          in primitivePart $ mapCoeff (\x -> numerator (toRational x) * (commonDenominator `Prelude.div` denominator (toRational x))) f
{-# RULES
"integralPrimitivePart/Integer" forall f. integralPrimitivePart f = primitivePart f
  #-}

-- | A subset of \(\overline{\mathbf{Q}}\)
class IsAlgebraic a where
  -- | Defining polynomial of the number
  definingPolynomial :: a -> UniPoly Integer
  algebraicDegree :: a -> Int
  algebraicDegree x = degree' (definingPolynomial x)

instance IsAlgebraic Integer where
  definingPolynomial x = UniPoly $ V.fromList [-x, 1]
  algebraicDegree _ = 1

instance (Integral a) => IsAlgebraic (Ratio a) where
  definingPolynomial x = UniPoly $ V.fromList [- Prelude.toInteger (numerator x), Prelude.toInteger (denominator x)]
  algebraicDegree _ = 1
