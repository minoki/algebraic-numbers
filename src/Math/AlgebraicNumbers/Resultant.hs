module Math.AlgebraicNumbers.Resultant
  (resultant
  ,subresultantPRS'
  ) where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly

-- | The resultant of polynomials with integral domain coefficients
resultant :: (Eq a, IntegralDomain a) => UniPoly a -> UniPoly a -> a
resultant f g
  | (f == 0 && degree g == Just 0) || (degree f == Just 0 && g == 0) = 1
  | f == 0 || g == 0 = 0
  | degree' f == 0 = leadingCoefficient f ^ degree' g
  | degree' g == 0 = leadingCoefficient g ^ degree' f
  | r == 0 = 0
  | degree' f >= degree' g, l >= 0 = (-1)^(degree' f * degree' g) * lc_g^l * resultant g r
  | degree' f >= degree' g, l < 0  = (-1)^(degree' f * degree' g) * resultant g r `divide` lc_g^(-l)
  | otherwise = (-1)^(degree' f * degree' g) * resultant g f
  where
    r = pseudoModP f g
    lc_g = leadingCoefficient g
    l = degree' f - degree' r - (degree' f - degree' g + 1) * degree' g

pseudoEuclidPRS :: (Eq a, Num a) => UniPoly a -> UniPoly a -> [UniPoly a]
pseudoEuclidPRS _ 0 = []
pseudoEuclidPRS f g = case pseudoModP f g of
  0 -> []
  rem -> rem : pseudoEuclidPRS g rem

primitivePRS :: (Eq a, GCDDomain a) => UniPoly a -> UniPoly a -> [UniPoly a]
primitivePRS _ 0 = []
primitivePRS f g = case pseudoModP f g of
  0 -> []
  rem -> let !r' = primitivePart rem in r' : primitivePRS g r'

reducedPRS :: (Eq a, IntegralDomain a) => UniPoly a -> UniPoly a -> [UniPoly a]
reducedPRS _ 0 = []
reducedPRS f g = case pseudoModP f g of
  0 -> []
  rem -> rem : loop (degree' f) g rem
  where
    loop !deg_h f g = case pseudoModP f g of
      0 -> []
      rem -> let !deg_f = degree' f
                 !beta = leadingCoefficient f ^ (deg_h - deg_f + 1)
                 !mr = unscaleP beta rem
             in mr : loop deg_f g mr

subresultantPRS :: (Eq a, IntegralDomain a) => UniPoly a -> UniPoly a -> [UniPoly a]
subresultantPRS _ 0 = []
subresultantPRS f g = case pseudoModP f g of
  0 -> []
  rem -> let !d = degree' f - degree' g
             !s = (-1)^(d + 1) * rem
         in s : loop d (-1) g s
  where
    loop !_ _ _ 0 = []
    loop !d psi f g = case pseudoModP f g of
      0 -> []
      rem -> let !d' = degree' f - degree' g
                 !c = leadingCoefficient f
                 !psi' = (-c)^d `divide` psi^(d-1)
                 !beta = -c * psi' ^ d'
                 !s = unscaleP beta rem
             in s : loop d' psi' g s

-- subresultantPRS' f g = (b,r) : subresultantPRS' g r
-- where lc(g)^l * f = q * g + b * r, l = deg f - deg g + 1
subresultantPRS' :: (Eq a, IntegralDomain a) => UniPoly a -> UniPoly a -> [(a,UniPoly a)]
subresultantPRS' _ 0 = []
subresultantPRS' f g = case pseudoModP f g of
  0 -> []
  rem -> let !d = degree' f - degree' g
             !s = (-1)^(d + 1) * rem
         in ((-1)^(d + 1), s) : loop d (-1) g s
  where
    loop !_ _ _ 0 = []
    loop d psi f g = case pseudoModP f g of
      0 -> []
      rem -> let !d' = degree' f - degree' g
                 !c = leadingCoefficient f
                 !psi' = (-c)^d `divide` psi^(d-1)
                 !beta = -c * psi' ^ d'
                 !s = unscaleP beta rem
             in (beta,s) : loop d' psi' g s
