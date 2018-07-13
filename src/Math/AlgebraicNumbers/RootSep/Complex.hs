module Math.AlgebraicNumbers.RootSep.Complex where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.Resultant
import Math.AlgebraicNumbers.AReal
import Math.AlgebraicNumbers.Interval
import Math.AlgebraicNumbers.CReal
import Math.AlgebraicNumbers.Complex
import Math.AlgebraicNumbers.RootSep.Real
import qualified Data.Vector as V
import Data.Ratio
import qualified Prelude (div,lcm)

negativePRSOnPath :: UniPoly (Complex Integer) -> UniPoly (Complex Integer) -> Complex Integer -> ([UniPoly Integer], UniPoly Integer)
negativePRSOnPath f c d = (s, uv)
  where
    fc = fst $ homogeneousCompP f c d
    u = mapCoeff realPart fc
    v = mapCoeff imagPart fc
    uv = gcdD u v
    u' = u `divide` uv
    v' = v `divide` uv
    s | degree u' > degree v' = negativePRS u' v'
      | otherwise = u' : negativePRS v' (-u')

-- c(t) = t + k * sqrt (-1)
negativePRSOnHorizontalLine :: UniPoly (Complex Integer) -> Rational -> ([UniPoly Integer], UniPoly Integer)
negativePRSOnHorizontalLine f k = negativePRSOnPath f (scaleP (fromReal q) ind + constP (fromImag p)) (fromReal q)
  where p = numerator k
        q = denominator k

-- c(t) = k + t * sqrt (-1)
negativePRSOnVerticalLine :: UniPoly (Complex Integer) -> Rational -> ([UniPoly Integer], UniPoly Integer)
negativePRSOnVerticalLine f k = negativePRSOnPath f (constP (fromReal p) + scaleP (fromImag q) ind) (fromReal q)
  where p = numerator k
        q = denominator k

negateIf :: Num a => Bool -> a -> a
negateIf True = negate
negateIf False = id

-- complexLinearFactor z is @ind - z@ with some scaling
-- @complexLinearFactor z@ は、 @ind - z@ の分母を払ったもの
complexLinearFactor :: Complex Rational -> UniPoly (Complex Integer)
complexLinearFactor (MkComplex x y) = let m = Prelude.lcm (denominator x) (denominator y)
                                          x' = numerator (x * fromInteger m)
                                          y' = numerator (y * fromInteger m)
                                      in scaleP (fromInteger m) ind - constP (MkComplex x' y')
{-
data Edge = Edge (UniPoly Integer) [UniPoly Integer] Bool Bool

makeHorzEdge :: UniPoly (Complex Integer) -> Rational -> Interval Rational -> Edge
makeHorzEdge f y iv = case negativePRSOnHorizontalLine f y of
                        (s,g) -> Edge s g
-}

-- | Counts the number of polynomial roots in the given rectangle.
--
-- Assumes that the polynomial is square-free.
--
-- >>> countRootsInRectangle ind (MkComplex (Iv (-1) 1) (Iv (-1) 1)) True
-- 1
-- >>> countRootsInRectangle ind (MkComplex (Iv 0 1) (Iv 0 1)) True
-- 1
-- >>> countRootsInRectangle ind (MkComplex (Iv 0 1) (Iv 0 1)) False
-- 0
-- >>> countRootsInRectangle ind (MkComplex (Iv (-1) 1) (Iv 0 1)) False
-- 0
-- >>> countRootsInRectangle ind (MkComplex (Iv 0 1) (Iv 0 1)) False
-- 0
-- >>> countRootsInRectangle ind (MkComplex (Iv (-1) 0) (Iv 0 1)) False
-- 0
-- >>> countRootsInRectangle ind (MkComplex (Iv 0 1) (Iv (-1) 0)) False
-- 0
-- >>> countRootsInRectangle ind (MkComplex (Iv (-1) 0) (Iv (-1) 0)) False
-- 1
-- >>> countRootsInRectangle ind (MkComplex (Iv 0 1) (Iv 0 1)) True
-- 1
-- >>> countRootsInRectangle ind (MkComplex (Iv (-1) 0) (Iv 0 1)) True
-- 1
-- >>> countRootsInRectangle ind (MkComplex (Iv 0 1) (Iv (-1) 0)) True
-- 1
-- >>> countRootsInRectangle ind (MkComplex (Iv (-1) 0) (Iv (-1) 0)) True
-- 1
countRootsInRectangle :: UniPoly Integer -> Complex (Interval Rational) -> Bool -> Int
countRootsInRectangle f rect includeLeftAndBottomEdges
  | a == b && c == d = if atTopLeft then 1 else 0
  | a == b = onRightEdge + (if atTopRight then 1 else 0) + (if atBottomRight then 1 else 0)
  | c == d = onTopEdge + (if atTopLeft then 1 else 0) + (if atTopRight then 1 else 0)
  | otherwise = (totalVariation `Prelude.div` 2) + corners
  where
    Iv a b = realPart rect
    Iv c d = imagPart rect
    bottomLeft  = MkComplex a c
    bottomRight = MkComplex b c
    topLeft     = MkComplex a d
    topRight    = MkComplex b d
    atBottomLeft  = valueAt bottomLeft  (mapCoeff fromInteger f) == 0
    atBottomRight = valueAt bottomRight (mapCoeff fromInteger f) == 0
    atTopLeft     = valueAt topLeft     (mapCoeff fromInteger f) == 0
    atTopRight    = valueAt topRight    (mapCoeff fromInteger f) == 0
    cornerFactors = product [ if atBottomLeft  then complexLinearFactor bottomLeft  else 1
                            , if atBottomRight then complexLinearFactor bottomRight else 1
                            , if atTopLeft     then complexLinearFactor topLeft     else 1
                            , if atTopRight    then complexLinearFactor topRight    else 1
                            ]
    corners = length $ filter id [ includeLeftAndBottomEdges && atBottomLeft
                                 , includeLeftAndBottomEdges && atBottomRight
                                 , includeLeftAndBottomEdges && atTopLeft
                                 , atTopRight
                                 ]
    fr :: UniPoly (Complex Integer)
    fr = mapCoeff fromReal f `divide` cornerFactors
    g1, g2, g3, g4 :: UniPoly Integer
    s1, s2, s3, s4 :: [UniPoly Integer]
    (s1,g1) = negativePRSOnHorizontalLine fr c
    (s2,g2) = negativePRSOnVerticalLine   fr b
    (s3,g3) = negativePRSOnHorizontalLine fr d
    (s4,g4) = negativePRSOnVerticalLine   fr a
    onBottomEdge = countRealRootsBetweenZQ a b g1
    onRightEdge  = countRealRootsBetweenZQ c d g2
    onTopEdge    = countRealRootsBetweenZQ a b g3
    onLeftEdge   = countRealRootsBetweenZQ c d g4
    varOnBottomEdge = varianceAtZQ b s1 - varianceAtZQ a s1
    varOnRightEdge  = varianceAtZQ d s2 - varianceAtZQ c s2
    varOnTopEdge    = varianceAtZQ a s3 - varianceAtZQ b s3
    varOnLeftEdge   = varianceAtZQ c s4 - varianceAtZQ d s4
    rootsOnEdges    = onRightEdge + onTopEdge - negateIf includeLeftAndBottomEdges (onBottomEdge + onLeftEdge)
    totalVariation  = varOnBottomEdge + varOnRightEdge + varOnTopEdge + varOnLeftEdge + rootsOnEdges

boolToInt :: Bool -> Int
boolToInt True = 1
boolToInt False = 0

-- | Counts the number of polynomial roots in the given rectangle.
--
-- Assumes that the polynomial is square-free.
countRootsInRectangleIrr :: UniPoly Integer -> Complex (Interval Rational) -> Bool -> Int
countRootsInRectangleIrr f rect includeLeftAndBottomEdges
  | degree f == Nothing = error "countRootsInRectangle: zero polynomial"
  | degree' f == 0 = 0
  | degree' f == 1 = let x = fromRational $ - ((coeff f) V.! 0) % ((coeff f) V.! 1)
                     in boolToInt $ if includeLeftAndBottomEdges
                                    then c <= 0 && 0 <= d && a <= x && x <= b
                                    else c < 0 && 0 <= d && a < x && x <= b
  | degree' f == 2 = let a0 = coeff f V.! 0
                         a1 = coeff f V.! 1
                         a2 = coeff f V.! 2
                         disc = a1 * a1 - 4 * a0 * a2
                         -- (-a1 +- sqrt(a1^2-4*a0*a2))/(2*a2)
                     in if disc < 0
                        then let re = - a1 % (2 * a2) -- real part of the roots
                                 -- im = +- sqrt (-d) / (2*a2)
                                 -- im^2 = (-d) / (2*a2)^2
                                 im2 = -disc % (2 * a2)^2 -- square of the imag part of the roots
                                 incRe | includeLeftAndBottomEdges = a <= re && re <= b
                                       | otherwise = a < re && re <= b
                                 incNegIm | includeLeftAndBottomEdges = c < 0 && (min 0 d)^2 <= im2 && im2 <= c^2
                                          | otherwise = c < 0 && (min 0 d)^2 <= im2 && im2 < c^2
                                 incPosIm | includeLeftAndBottomEdges = 0 < d && (max 0 c)^2 <= im2 && im2 <= d^2
                                          | otherwise = 0 < d && (max 0 c)^2 < im2 && im2 <= d^2
                             in if incRe then boolToInt incNegIm + boolToInt incPosIm else 0
                        else let incIm | includeLeftAndBottomEdges = c <= 0 && 0 <= d
                                       | otherwise = c < 0 && 0 <= d
                                 t = - a1 % (2 * a2)
                                 a' = a - t
                                 b' = b - t
                                 re2t = disc % (2 * a2)^2
                                 incLeft | includeLeftAndBottomEdges = a' < 0 && (min 0 b')^2 <= re2t && re2t <= b'^2
                                         | otherwise = a' < 0 && (min 0 b')^2 <= re2t && re2t < b'^2
                                 incRight | includeLeftAndBottomEdges = 0 < b' && (max 0 a')^2 <= re2t && re2t <= b'^2
                                          | otherwise = 0 < b' && (max 0 a')^2 < re2t && re2t <= b'^2
                             in if incIm then boolToInt incLeft + boolToInt incRight else 0
  | a == b && c == d = 0
  | a == b = onRightEdge
  | c == d = onTopEdge
  | otherwise = totalVariation `Prelude.div` 2
  where
    Iv a b = realPart rect
    Iv c d = imagPart rect
    -- corners
    bottomLeft  = MkComplex a c
    bottomRight = MkComplex b c
    topLeft     = MkComplex a d
    topRight    = MkComplex b d
    fr :: UniPoly (Complex Integer)
    fr = mapCoeff fromReal f
    g1, g2, g3, g4 :: UniPoly Integer
    s1, s2, s3, s4 :: [UniPoly Integer]
    (s1,g1) = negativePRSOnHorizontalLine fr c
    (s2,g2) = negativePRSOnVerticalLine   fr b
    (s3,g3) = negativePRSOnHorizontalLine fr d
    (s4,g4) = negativePRSOnVerticalLine   fr a
    onBottomEdge = countRealRootsBetweenZQ a b g1
    onRightEdge  = countRealRootsBetweenZQ c d g2
    onTopEdge    = countRealRootsBetweenZQ a b g3
    onLeftEdge   = countRealRootsBetweenZQ c d g4
    varOnBottomEdge = varianceAtZQ b s1 - varianceAtZQ a s1
    varOnRightEdge  = varianceAtZQ d s2 - varianceAtZQ c s2
    varOnTopEdge    = varianceAtZQ a s3 - varianceAtZQ b s3
    varOnLeftEdge   = varianceAtZQ c s4 - varianceAtZQ d s4
    rootsOnEdges    = onRightEdge + onTopEdge - negateIf includeLeftAndBottomEdges (onBottomEdge + onLeftEdge)
    totalVariation  = varOnBottomEdge + varOnRightEdge + varOnTopEdge + varOnLeftEdge + rootsOnEdges

type Edge = ([UniPoly Integer],UniPoly Integer) -- deriving (Eq,Show)

countRootsInRectangleIrrWithEdges :: UniPoly Integer -> Edge -> Edge -> Edge -> Edge -> Complex (Interval Rational) -> Bool -> Int
countRootsInRectangleIrrWithEdges f bottomE rightE topE leftE rect includeLeftAndBottomEdges
  | degree f == Nothing = error "countRootsInRectangle: zero polynomial"
  | degree' f == 0 = 0
  | degree' f == 1 = let x = fromRational $ - ((coeff f) V.! 0) % ((coeff f) V.! 1)
                     in boolToInt $ if includeLeftAndBottomEdges
                                    then c <= 0 && 0 <= d && a <= x && x <= b
                                    else c < 0 && 0 <= d && a < x && x <= b
  | degree' f == 2 = let a0 = coeff f V.! 0
                         a1 = coeff f V.! 1
                         a2 = coeff f V.! 2
                         disc = a1 * a1 - 4 * a0 * a2
                     in if disc < 0
                        then let re = - a1 % (2 * a2) -- real part of the roots
                                 -- im = +- sqrt (-d) / a2
                                 -- im^2 = (-d) / a2^2
                                 im2 = -disc % (2 * a2)^2 -- square of the imag part of the roots
                                 incRe | includeLeftAndBottomEdges = a <= re && re <= b
                                       | otherwise = a < re && re <= b
                                 incNegIm | includeLeftAndBottomEdges = c < 0 && (min 0 d)^2 <= im2 && im2 <= c^2
                                          | otherwise = c < 0 && (min 0 d)^2 <= im2 && im2 < c^2
                                 incPosIm | includeLeftAndBottomEdges = 0 < d && (max 0 c)^2 <= im2 && im2 <= d^2
                                          | otherwise = 0 < d && (max 0 c)^2 < im2 && im2 <= d^2
                             in if incRe then boolToInt incNegIm + boolToInt incPosIm else 0
                        else let incIm | includeLeftAndBottomEdges = c <= 0 && 0 <= d
                                       | otherwise = c < 0 && 0 <= d
                                 t = - a1 % (2 * a2)
                                 a' = a - t
                                 b' = b - t
                                 re2t = disc % (2 * a2)^2
                                 incLeft | includeLeftAndBottomEdges = a' < 0 && (min 0 b')^2 <= re2t && re2t <= b'^2
                                         | otherwise = a' < 0 && (min 0 b')^2 <= re2t && re2t < b'^2
                                 incRight | includeLeftAndBottomEdges = 0 < b' && (max 0 a')^2 <= re2t && re2t <= b'^2
                                          | otherwise = 0 < b' && (max 0 a')^2 < re2t && re2t <= b'^2
                             in if incIm then boolToInt incLeft + boolToInt incRight else 0
  | a == b && c == d = 0
  | a == b = onRightEdge
  | c == d = onTopEdge
  | otherwise = totalVariation `Prelude.div` 2
  where
    Iv a b = realPart rect
    Iv c d = imagPart rect
    -- corners
    bottomLeft  = MkComplex a c
    bottomRight = MkComplex b c
    topLeft     = MkComplex a d
    topRight    = MkComplex b d
    fr :: UniPoly (Complex Integer)
    fr = mapCoeff fromReal f
    g1, g2, g3, g4 :: UniPoly Integer
    s1, s2, s3, s4 :: [UniPoly Integer]
    (s1,g1) = bottomE
    (s2,g2) = rightE
    (s3,g3) = topE
    (s4,g4) = leftE
    onBottomEdge = countRealRootsBetweenZQ a b g1
    onRightEdge  = countRealRootsBetweenZQ c d g2
    onTopEdge    = countRealRootsBetweenZQ a b g3
    onLeftEdge   = countRealRootsBetweenZQ c d g4
    varOnBottomEdge = varianceAtZQ b s1 - varianceAtZQ a s1
    varOnRightEdge  = varianceAtZQ d s2 - varianceAtZQ c s2
    varOnTopEdge    = varianceAtZQ a s3 - varianceAtZQ b s3
    varOnLeftEdge   = varianceAtZQ c s4 - varianceAtZQ d s4
    rootsOnEdges    = onRightEdge + onTopEdge - negateIf includeLeftAndBottomEdges (onBottomEdge + onLeftEdge)
    totalVariation  = varOnBottomEdge + varOnRightEdge + varOnTopEdge + varOnLeftEdge + rootsOnEdges

negativePRSOnPathAN :: UniPoly (Complex AReal) -> UniPoly (Complex Integer) -> Complex Integer -> ([UniPoly AReal], UniPoly AReal)
negativePRSOnPathAN f c d = (s, uv)
  where
    fc = fst $ homogeneousCompP f (mapCoeff (fmap fromInteger) c) (fmap fromInteger d)
    u = mapCoeff realPart fc
    v = mapCoeff imagPart fc
    uv = gcdD u v
    u' = u `divide` uv
    v' = v `divide` uv
    s | degree u' > degree v' = negativePRS u' v'
      | otherwise = u' : negativePRS v' (-u')

-- c(t) = t + k * sqrt (-1)
negativePRSOnHorizontalLineAN :: UniPoly (Complex AReal) -> Rational -> ([UniPoly AReal], UniPoly AReal)
negativePRSOnHorizontalLineAN f k = negativePRSOnPathAN f (scaleP (fromReal q) ind + constP (fromImag p)) (fromReal q)
  where p = numerator k
        q = denominator k

-- c(t) = k + t * sqrt (-1)
negativePRSOnVerticalLineAN :: UniPoly (Complex AReal) -> Rational -> ([UniPoly AReal], UniPoly AReal)
negativePRSOnVerticalLineAN f k = negativePRSOnPathAN f (constP (fromReal p) + scaleP (fromImag q) ind) (fromReal q)
  where p = numerator k
        q = denominator k
