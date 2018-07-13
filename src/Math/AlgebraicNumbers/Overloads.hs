module Math.AlgebraicNumbers.Overloads where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.AReal
import Math.AlgebraicNumbers.AComplex
import qualified Prelude
import qualified Data.Complex

-- Prelude functions generalized from Integral a to GCDDomain a / EuclideanDomain a

gcd :: (GCDDomain a) => a -> a -> a
gcd = gcdD

lcm :: (GCDDomain a) => a -> a -> a
lcm = lcmD

divMod :: (EuclideanDomain a) => a -> a -> (a, a)
divMod = divModD

infixl 7 `div`, `mod`

div, mod :: (EuclideanDomain a) => a -> a -> a
div = divD
mod = modD

class Sqrt a where
  sqrt :: a -> a
  maybeSqrt :: a -> Maybe a

instance Sqrt Prelude.Float where
  sqrt = Prelude.sqrt
  maybeSqrt x | x >= 0 = Just $ Prelude.sqrt x
              | otherwise = Nothing

instance Sqrt Prelude.Double where
  sqrt = Prelude.sqrt
  maybeSqrt x | x >= 0 = Just $ Prelude.sqrt x
              | otherwise = Nothing

instance (RealFloat a) => Sqrt (Data.Complex.Complex a) where
  sqrt = Prelude.sqrt
  maybeSqrt = Just . Prelude.sqrt

instance Sqrt AReal where
  sqrt = sqrtA
  maybeSqrt x | x >= 0 = Just $ sqrtA x
              | otherwise = Nothing

instance Sqrt AComplex where
  sqrt = sqrtAN
  maybeSqrt = Just . sqrtAN

-- toRational?
