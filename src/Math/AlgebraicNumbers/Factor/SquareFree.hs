module Math.AlgebraicNumbers.Factor.SquareFree where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly

-- naive implementation of squarefree factorization
-- >>> naiveSFF ((ind + 1)^2 :: UniPoly Rational)
-- [(UniPoly [1 % 1,1 % 1],2)]
-- >>> naiveSFF ((ind + 1)^2 * (ind + 3)^7 * (ind^2 + 1) * ind :: UniPoly Rational)
-- [(UniPoly [0 % 1,1 % 1,0 % 1,1 % 1],1),(UniPoly [1 % 1,1 % 1],2),(UniPoly [3 % 1,1 % 1],7)]
naiveSFF :: (Eq a, GCDDomain a) => UniPoly a -> [(UniPoly a,Int)]
naiveSFF 0 = [(0,1)]
naiveSFF f = mf (primitivePart f)
  where
    mf f | degree f == Just 0 = [] -- constant
         | degree f == degree p {- t == 1 -} = u
         | otherwise = (t,1) : u
      where r = mf (sqPart f)
            u = map (\(g,i) -> i+1 `seq` (g,i+1)) r
            p = sqPart f * product (map fst r)
            -- p = product (map (uncurry (^)) u)
            t = f `divide` p
    sqPart f = primitivePart $ gcdD f (diffP f)

-- Yun's algorithm
--
-- Input: primitive (?)
yunSFF :: (Eq a, GCDDomain a) => UniPoly a -> [(UniPoly a,Int)]
yunSFF 0 = [(0,1)]
yunSFF f = let f' = diffP f
               u = gcdD f f'
           in loop 1 (f `divide` u) (f' `divide` u)
  where loop !i v w | degree' v == 0 = []
                    | h == 1 = loop (i+1) v s
                    | otherwise = (h,i) : loop (i+1) (v `divide` h) (s `divide` h)
          where s = w - diffP v
                h = gcdD v s
