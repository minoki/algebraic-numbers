module Math.AlgebraicNumbers.Fraction where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import qualified Data.Vector as V
import Data.Ratio

infixl 7 %%, :%%

data Fraction a = !a :%% !a deriving (Show)

instance (Eq a, Num a) => Eq (Fraction a) where
  -- TODO: When is @x == x' && y == y'@ usable?
  x :%% y == x' :%% y' = x * y' == y * x'

(%%) :: (GCDDomain a) => a -> a -> Fraction a
(!x) %% (!y) = let !c = contentV (V.fromList [x,y])
               in (x `divide` c) :%% (y `divide` c)

numeratorF, denominatorF :: Fraction a -> a
numeratorF (x :%% _) = x
denominatorF (_ :%% y) = y

instance (Eq a, GCDDomain a) => Num (Fraction a) where
  negate (x :%% y) = (negate x) :%% y
  (x :%% y) + (x' :%% y') = (x * y' + x' * y) %% (y * y')
  (x :%% y) - (x' :%% y') = (x * y' - x' * y) %% (y * y')
  (x :%% y) * (x' :%% y') = (x * x') %% (y * y')
  abs (x :%% y) = abs x %% abs y
  signum (x :%% y) = signum x :%% 1
  fromInteger n = fromInteger n :%% 1

instance (Eq a, GCDDomain a) => Fractional (Fraction a) where
  recip (x :%% y) = y %% x
  (x :%% y) / (x' :%% y') = (x * y') %% (y * x')
  fromRational n = fromInteger (numerator n) :%% fromInteger (denominator n)

fromRational_rat :: Rational -> Fraction Integer
fromRational_rat x = numerator x :%% denominator x
-- Rewrite: fromRational = fromRational_rat

instance (Eq a, GCDDomain a) => IntegralDomain (Fraction a) where
  divide = (/)

instance (Eq a, GCDDomain a) => GCDDomain (Fraction a) where
  gcdD = fieldGcd
  contentV = fieldContentV
