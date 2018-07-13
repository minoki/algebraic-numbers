module Math.AlgebraicNumbers.AComplex where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.Resultant
import Math.AlgebraicNumbers.AReal
import Math.AlgebraicNumbers.Interval
import Math.AlgebraicNumbers.CReal
import Math.AlgebraicNumbers.Complex
import Math.AlgebraicNumbers.Factor.SquareFree
import Math.AlgebraicNumbers.Factor.Integer
import Math.AlgebraicNumbers.RootSep.Real
import Math.AlgebraicNumbers.RootSep.Complex
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Vector as V
import Data.List
import Data.Ratio
import GHC.Stack
import Debug.Trace
import qualified Prelude (div)

complexIntToAComplex :: Complex Integer -> AComplex
complexIntToAComplex z = mkComplexA (fromInteger $ realPart z) (fromInteger $ imagPart z)

complexRatToAComplex :: Complex Rational -> AComplex
complexRatToAComplex z = mkComplexA (fromRational $ realPart z) (fromRational $ imagPart z)

algNumToComplexAReal :: AComplex -> Complex AReal
algNumToComplexAReal x = MkComplex (realPartA x) (imagPartA x)

countRootsInRectangleAN :: UniPoly AComplex -> Complex (Interval Rational) -> Bool -> Int
countRootsInRectangleAN f rect includeLeftAndBottomEdges
  | a == b && c == d = if atTopLeft then 1 else 0
  | a == b = onRightEdge + (if atTopRight then 1 else 0) + (if atBottomRight then 1 else 0)
  | c == d = onTopEdge + (if atTopLeft then 1 else 0) + (if atTopRight then 1 else 0)
  | otherwise = (totalVariation `Prelude.div` 2) + corners
  where
    Iv a b = realPart rect
    Iv c d = imagPart rect
    fc = mapCoeff algNumToComplexAReal f
    bottomLeft  = MkComplex a c
    bottomRight = MkComplex b c
    topLeft     = MkComplex a d
    topRight    = MkComplex b d
    atBottomLeft  = valueAt (fmap fromRational bottomLeft)  fc == 0
    atBottomRight = valueAt (fmap fromRational bottomRight) fc == 0
    atTopLeft     = valueAt (fmap fromRational topLeft)     fc == 0
    atTopRight    = valueAt (fmap fromRational topRight)    fc == 0
    cornerFactors = mapCoeff (fmap fromRational) $ product [ if atBottomLeft  then ind - constP bottomLeft  else 1
                                                           , if atBottomRight then ind - constP bottomRight else 1
                                                           , if atTopLeft     then ind - constP topLeft     else 1
                                                           , if atTopRight    then ind - constP topRight    else 1
                                                           ]
    corners = length $ filter id [ includeLeftAndBottomEdges && atBottomLeft
                                 , includeLeftAndBottomEdges && atBottomRight
                                 , includeLeftAndBottomEdges && atTopLeft
                                 , atTopRight
                                 ]
    fr :: UniPoly (Complex AReal)
    fr = fc `divide` cornerFactors
    g1, g2, g3, g4 :: UniPoly AReal
    s1, s2, s3, s4 :: [UniPoly AReal]
    (s1,g1) = negativePRSOnHorizontalLineAN fr c
    (s2,g2) = negativePRSOnVerticalLineAN   fr b
    (s3,g3) = negativePRSOnHorizontalLineAN fr d
    (s4,g4) = negativePRSOnVerticalLineAN   fr a
    onBottomEdge = countRealRootsBetween (fromRational a) (fromRational b) g1
    onRightEdge  = countRealRootsBetween (fromRational c) (fromRational d) g2
    onTopEdge    = countRealRootsBetween (fromRational a) (fromRational b) g3
    onLeftEdge   = countRealRootsBetween (fromRational c) (fromRational d) g4
    varOnBottomEdge = varianceAt (fromRational b) s1 - varianceAt (fromRational a) s1
    varOnRightEdge  = varianceAt (fromRational d) s2 - varianceAt (fromRational c) s2
    varOnTopEdge    = varianceAt (fromRational a) s3 - varianceAt (fromRational b) s3
    varOnLeftEdge   = varianceAt (fromRational c) s4 - varianceAt (fromRational d) s4
    rootsOnEdges    = onRightEdge + onTopEdge - negateIf includeLeftAndBottomEdges (onBottomEdge + onLeftEdge)
    totalVariation  = varOnBottomEdge + varOnRightEdge + varOnTopEdge + varOnLeftEdge + rootsOnEdges

-- | Algebraic number, embedded in the complex plane
data AComplex = FromReal !AReal
              | MkAComplex !(UniPoly Integer) !(Complex CReal)

instance Show AComplex where
  show (FromReal x) = show x
  show (MkAComplex f c) = "MkAComplex (" ++ show f ++ ") (" ++ show (fmap (head . toIntervals) c) ++ ")"

instance IsAlgebraic AComplex where
  definingPolynomial (FromReal x) = definingPolynomial x
  definingPolynomial (MkAComplex f _) = f

isolatingRectangle :: AComplex -> Complex (Interval Rational)
isolatingRectangle (FromReal x) = MkComplex (isolatingInterval x) 0
isolatingRectangle (MkAComplex _ r) = fmap (head . toIntervals) r

isCompatibleWithZeroR :: Complex (Interval Rational) -> Bool
isCompatibleWithZeroR x = isCompatibleWithZero (realPart x) && isCompatibleWithZero (imagPart x)

compatibleRectangles :: Complex (Interval Rational) -> Complex (Interval Rational) -> Bool
compatibleRectangles x y = compatible (realPart x) (realPart y) && compatible (imagPart x) (imagPart y)

isolatingRectToCComplex :: UniPoly Integer -> Complex (Interval Rational) -> Complex CReal
isolatingRectToCComplex f r0@(MkComplex r i)
  | width r == 0 && width i == 0 = MkComplex (fromRational (lo r)) (fromRational (lo i))
  | otherwise = let rectangles = r0 : bisectReal bottomE0 rightE0 topE0 leftE0 r0
                    fr = mapCoeff fromReal f
                    Iv a b = r
                    Iv c d = i
                    bottomE0 = negativePRSOnHorizontalLine fr c
                    rightE0  = negativePRSOnVerticalLine   fr b
                    topE0    = negativePRSOnHorizontalLine fr d
                    leftE0   = negativePRSOnVerticalLine   fr a
                    bisectReal bottomE rightE topE leftE rect =
                      let Iv a b = realPart rect
                          leftHalf  = MkComplex (Iv a ((a + b) / 2)) (imagPart rect)
                          rightHalf = MkComplex (Iv ((a + b) / 2) b) (imagPart rect)
                          midE = negativePRSOnVerticalLine fr ((a + b) / 2)
                      in if countRootsInRectangleIrrWithEdges f bottomE midE topE leftE leftHalf True == 0
                         then bisectImag bottomE rightE topE midE rightHalf
                         else bisectImag bottomE midE topE leftE leftHalf
                    bisectImag bottomE rightE topE leftE rect =
                      let Iv c d = imagPart rect
                          lowerHalf = MkComplex (realPart rect) (Iv c ((c + d) / 2))
                          upperHalf = MkComplex (realPart rect) (Iv ((c + d) / 2) d)
                          midE = negativePRSOnHorizontalLine fr ((c + d) / 2)
                      in if countRootsInRectangleIrrWithEdges f bottomE rightE midE leftE lowerHalf True == 0
                         then upperHalf : bisectReal midE rightE topE leftE upperHalf
                         else lowerHalf : bisectReal bottomE rightE midE leftE lowerHalf
                in MkComplex (cRealFromIntervals $ map realPart rectangles) (cRealFromIntervals $ map imagPart rectangles)

-- the polynomial: primitive, irreducible, leading coefficient > 0
mkAComplexWithIsolatingRectangle :: HasCallStack => UniPoly Integer -> Complex (Interval Rational) -> AComplex
mkAComplexWithIsolatingRectangle f rect
  | degree' f == 1 = fromRational $ - ((coeff f) V.! 0) % ((coeff f) V.! 1) -- rational number
  | isCompatibleWithZero (imagPart rect)
  , Iv a b <- realPart rect
  , signAtZQ a f * signAtZQ b f < 0 = FromReal (mkARealWithIrreduciblePoly f a b)
  | otherwise = MkAComplex f (MkComplex r i')
  where MkComplex r (CReal i) = isolatingRectToCComplex f rect
        i' = CReal $ dropWhile isCompatibleWithZero i

mkAComplexWithCComplex :: UniPoly Integer -> Complex CReal -> AComplex
mkAComplexWithCComplex f x = sieve squareFreeFactors (zipWith MkComplex (toIntervals $ realPart x) (toIntervals $ imagPart x))
  where
    squareFreeFactors :: [UniPoly Integer]
    squareFreeFactors = map fst $ yun $ primitivePart f

    sieve :: [UniPoly Integer] -> [Complex (Interval Rational)] -> AComplex
    sieve [] _ = error "invalid complex number"
    sieve [g] xs = sieve2 ({-# SCC "AComplex/factorization" #-} (unsafePerformIO (factorIntegerIO g))) xs
    sieve gs (x:xs) = sieve (filter (\g -> isCompatibleWithZeroR (valueAtZ x g)) gs) xs

    sieve2 :: [UniPoly Integer] -> [Complex (Interval Rational)] -> AComplex
    sieve2 [] _ = error "invalid complex number"
    sieve2 [g] xs
      | degree g <= Just 0 = error "mkAComplexWithCComplex: minimal polynomial is constant"
      | degree' g == 1 = fromRational $ - ((coeff g) V.! 0) % ((coeff g) V.! 1) -- rational number
      | otherwise = case dropWhile (\r -> countRootsInRectangle g r True >= 2) xs of
                      r : _ -> mkAComplexWithIsolatingRectangle g r
    sieve2 gs (x:xs) = sieve2 (filter (\g -> isCompatibleWithZeroR (valueAtZ x g)) gs) xs

algNumToCComplex :: AComplex -> Complex CReal
algNumToCComplex (FromReal x) = fromReal (toCReal x)
algNumToCComplex (MkAComplex _ c) = c

-- | Real part of an algebraic number
realPartA :: AComplex -> AReal
realPartA (FromReal x) = x
realPartA x = mkARealWithCReal g (realPart (algNumToCComplex x))
  where f = definingPolynomial x
        g = resultant (mapCoeff constP f) (compP (mapCoeff constP f) $ constP (scaleP 2 ind) - ind) -- res_y(f(y),f(2x-y))

-- | Imaginary part of an algebraic number
imagPartA :: AComplex -> AReal
imagPartA (FromReal _) = 0
imagPartA x = mkARealWithCReal h (imagPart (algNumToCComplex x))
  where f = definingPolynomial x
        g = resultant (mapCoeff (constP . fromReal) f) (compP (mapCoeff (constP . fromReal) f) $ ind - constP (scaleP (fromImag 2) ind)) -- res_y(f(y),f(y-2ix))
        h = gcdD (mapCoeff realPart g) (mapCoeff imagPart g)

-- | Algebraic number from its real and imaginary parts
mkComplexA :: AReal -> AReal -> AComplex
mkComplexA x y = mkAComplexWithCComplex h (MkComplex (toCReal x) (toCReal y))
  where f = mapCoeff constP (definingPolynomial x)
        g = mapCoeff (constP . constP) (definingPolynomial y)
        h = resultant f $ resultant g $ (constP (constP ind - ind))^2 + ind^2 -- res_y(f(y),res_z(g(z),(x-y)^2+z^2))

rectangleToSquaredMagnitude :: Complex CReal -> CReal
rectangleToSquaredMagnitude z = (abs (realPart z))^2 + (abs (imagPart z))^2

squaredMagnitudeA :: AComplex -> AReal
squaredMagnitudeA (FromReal x) = x * x
squaredMagnitudeA x = mkARealWithCReal (resultant y_f_x_y g) (rectangleToSquaredMagnitude $ algNumToCComplex x)
  where f = definingPolynomial x
        y_f_x_y = UniPoly $ V.reverse $ V.imap (\i a -> constP a * ind^i) $ coeff f -- y^n f(x/y)
        g = mapCoeff constP $ definingPolynomial x

-- | Magnitude of an algebraic number
magnitudeA :: AComplex -> AReal
magnitudeA (FromReal x) = abs x
magnitudeA x = sqrtA (squaredMagnitudeA x)

-- | Complex conjugate of an algebraic number
complexConjugate :: AComplex -> AComplex
complexConjugate x@(FromReal _) = x
complexConjugate x = mkAComplexWithIsolatingRectangle (definingPolynomial x) (conjugate (isolatingRectangle x))

instance Eq AComplex where
  FromReal x == FromReal y = x == y
  x == y = definingPolynomial x == definingPolynomial y && compatibleRectangles (isolatingRectangle x) (isolatingRectangle y)

instance Num AComplex where
  negate (FromReal x) = FromReal (negate x)
  negate x = mkAComplexWithIsolatingRectangle (primitivePart $ compP (definingPolynomial x) (-ind)) (- isolatingRectangle x)

  FromReal x + FromReal y = FromReal (x + y)
  x + y = mkAComplexWithCComplex ({-# SCC "AComplex.+/resultant" #-} resultant f_x_y g) (algNumToCComplex x + algNumToCComplex y)
    where f = mapCoeff constP $ definingPolynomial x
          f_x_y = compP f (constP ind - ind) -- f(x-y)
          g = mapCoeff constP $ definingPolynomial y

  FromReal x * FromReal y = FromReal (x * y)
  FromReal (FromRat k) * y
    | k == 0 = 0
    | otherwise = mkAComplexWithIsolatingRectangle (primitivePart f_x_k) (isolatingRectangle y * fromRational k)
    where f_x_k = fst $ homogeneousValueAt (scaleP (denominator k) ind) (fromInteger $ numerator k) (mapCoeff fromInteger (definingPolynomial y)) -- f(x/k)
  x * y@(FromReal (FromRat _)) = y * x
  x * y = mkAComplexWithCComplex (resultant y_f_x_y g) (algNumToCComplex x * algNumToCComplex y)
    where f = definingPolynomial x
          y_f_x_y = UniPoly $ V.reverse $ V.imap (\i a -> constP a * ind^i) $ coeff f -- y^n f(x/y)
          g = mapCoeff constP $ definingPolynomial y

  fromInteger n = FromReal (fromInteger n)

  abs x = FromReal (magnitudeA x)
  signum x | x == 0 = x
           | otherwise = x / abs x

instance Fractional AComplex where
  recip (FromReal x) = FromReal (recip x)
  recip x = mkAComplexWithCComplex (UniPoly $ V.reverse $ coeff $ definingPolynomial x) (recip (algNumToCComplex x))

  fromRational x = FromReal (fromRational x)

instance IntegralDomain AComplex where
  divide = (/)

instance GCDDomain AComplex where
  gcdD = fieldGcd
  lcmD = fieldLcm
  contentV = fieldContentV

sqrtAN :: AComplex -> AComplex
sqrtAN (FromReal x)
  | x >= 0 = FromReal (sqrtA x)
  | otherwise = mkComplexA 0 (sqrtA (-x))
sqrtAN x = nthRootAN 2 x

nthRootAN :: Int -> AComplex -> AComplex
nthRootAN n (FromReal x)
  | x >= 0 || odd n = FromReal (nthRootA n x)
  | otherwise = mkComplexA 0 (nthRootA n (-x))
nthRootAN n x
  | n == 0 = error "0th root"
  | n < 0 = nthRootAN (-n) (recip x)
  | x == 0 = 0
  | otherwise = sieve (map (\(y,_) -> (y,algNumToCComplex y)) $ rootsI (compP f (ind^n)))
  where f = definingPolynomial x
        sieve :: [(AComplex,Complex CReal)] -> AComplex
        sieve [] = error "nthRootAN"
        sieve [(y,_)] = y
        sieve ys = sieve $ map (\(y,cz) -> (y,fmap (cRealFromIntervals . tail . toIntervals) cz)) $ filter (\(y,cz) -> isCompatible (fmap (head . toIntervals) cz)) ys
        isCompatible :: Complex (Interval Rational) -> Bool
        isCompatible z = compatibleRectangles (isolatingRectangle x) (z^n) && if isImagPartPositive then b >= 0 else a <= 0
          where Iv a b = imagPart z
        -- x is assumed to be non-real
        isImagPartPositive = unsafeCompareCReal 0 (imagPart (algNumToCComplex x)) == LT

powIntAN :: AComplex -> Int -> AComplex
powIntAN _ 0 = 1
powIntAN (FromReal x) n = FromReal (powIntA x n)
powIntAN x n | n < 0 = recip $ powIntAN x (-n)
powIntAN x n = case (ind^n) `modP` f of
                g -> valueAt x (mapCoeff fromRational g) -- x^n mod f(x) (ind^n `modP` f)
  where f = mapCoeff fromInteger $ definingPolynomial x :: UniPoly Rational

powRatAN :: AComplex -> Rational -> AComplex
powRatAN x y = powIntAN (nthRootAN (fromInteger $ denominator y) x) (fromInteger $ numerator y)

valueAtANR :: AComplex -> UniPoly Integer -> AComplex
valueAtANR (FromReal x) f = FromReal (valueAtA x f)
valueAtANR x f = mkAComplexWithCComplex h (valueAt (algNumToCComplex x) (unsafeMapCoeff (fromReal . toCReal) f))
  where g = mapCoeff fromInteger $ definingPolynomial x
        h = resultant g (constP ind - mapCoeff fromInteger f)

rootsOfIrreduciblePolyInRectangle :: UniPoly Integer -> Complex (Interval Rational) -> Int -> [AComplex]
rootsOfIrreduciblePolyInRectangle f rect expectedNumOfRoots = bisectReal rect expectedNumOfRoots
  where
    bisectReal rect n
      | n == 0 = []
      | n == 1 && countRootsInRectangleIrr f rect True == 1 = [mkAComplexWithIsolatingRectangle f rect]
      | otherwise = let Iv a b = realPart rect
                        leftHalf  = MkComplex (Iv a ((a + b) / 2)) (imagPart rect)
                        rightHalf = MkComplex (Iv ((a + b) / 2) b) (imagPart rect)
                        m = countRootsInRectangleIrr f leftHalf False
                    in if m == 0
                       then bisectImag rightHalf n
                       else if m == n
                            then bisectImag leftHalf n
                            else bisectImag leftHalf m ++ bisectImag rightHalf (n - m)
    bisectImag rect n
      | n == 0 = []
      | n == 1 && countRootsInRectangleIrr f rect True == 1 = [mkAComplexWithIsolatingRectangle f rect]
      | otherwise = let Iv c d = imagPart rect
                        lowerHalf = MkComplex (realPart rect) (Iv c ((c + d) / 2))
                        upperHalf = MkComplex (realPart rect) (Iv ((c + d) / 2) d)
                        m = countRootsInRectangleIrr f lowerHalf False
                     in if m == 0
                        then bisectReal upperHalf n
                        else if m == n
                             then bisectReal lowerHalf n
                             else bisectReal lowerHalf m ++ bisectReal upperHalf (n - m)

rootsI :: UniPoly Integer -> [(AComplex,Int)]
rootsI f | f == 0 = error "rootsI: zero"
         | otherwise = [ (x,i)
                       | (g,i) <- yun (primitivePart f)
                       , h <- sortPolynomials $ unsafePerformIO (factorIntegerIO g)
                       , let bound = rootBound h
                       , x <- rootsOfIrreduciblePolyInRectangle h (MkComplex (Iv (-bound) bound) (Iv (-bound) bound)) (degree' h)
                       ]
  where sortPolynomials :: [UniPoly Integer] -> [UniPoly Integer]
        sortPolynomials = sortOn coeff

rootsQ :: (IsRational a) => UniPoly a -> [(AComplex,Int)]
rootsQ = rootsI . integralPrimitivePart

rootsA :: UniPoly AReal -> [(AComplex,Int)]
rootsA f = [ (x,i)
           | (g,i) <- yun f
           , (x,_) <- rootsI (elimN g)
           , let rect = isolatingRectangle x
           , countRootsInRectangleAN (mapCoeff FromReal g) rect True > 0
           ]

rootsAN :: UniPoly AComplex -> [(AComplex,Int)]
rootsAN f = [ (x,i)
            | (g,i) <- yun f
            , (x,_) <- rootsI (elimN g)
            , let rect = isolatingRectangle x
            , countRootsInRectangleAN g rect True > 0
            ]
