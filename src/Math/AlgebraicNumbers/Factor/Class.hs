module Math.AlgebraicNumbers.Factor.Class where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.Factor.CantorZassenhaus
import Math.AlgebraicNumbers.Factor.Integer
import Math.AlgebraicNumbers.AReal
import Math.AlgebraicNumbers.AComplex
import qualified Prelude
import qualified Data.Vector as V
import Data.Ratio
import Data.FiniteField
import GHC.TypeLits (KnownNat)
import System.IO.Unsafe (unsafePerformIO)

class PolynomialFactorization a where
  -- Assume that the input is non-zero, primitive and square-free
  factorizeSF :: UniPoly a -> [UniPoly a]
  factorizeSFIO :: UniPoly a -> IO [UniPoly a]
  factorizeSFIO = return . factorizeSF

instance PolynomialFactorization Integer where
  factorizeSF = unsafePerformIO . factorIntegerIO
  factorizeSFIO = factorIntegerIO

instance (Integral a, GCDDomain a, PolynomialFactorization a) => PolynomialFactorization (Ratio a) where
  factorizeSF f = do
    let commonDenominator = V.foldl' (\a b -> Prelude.lcm a (denominator b)) 1 (coeff f)
        pp = primitivePart $ mapCoeff (\x -> numerator x * (commonDenominator `Prelude.div` denominator x)) f
    map (toMonic . mapCoeff fromIntegral) $ factorizeSF pp
  factorizeSFIO f = do
    let commonDenominator = V.foldl' (\a b -> Prelude.lcm a (denominator b)) 1 (coeff f)
        pp = primitivePart $ mapCoeff (\x -> numerator x * (commonDenominator `Prelude.div` denominator x)) f
    map (toMonic . mapCoeff fromIntegral) <$> factorizeSFIO pp

instance PolynomialFactorization AReal where
  factorizeSF f = do
    (a,i) <- rootsA f
    case a of
      FromReal a -> return (ind - constP a)
      a | imagPartA a > 0 -> return (ind^2 - scaleP (2 * realPartA a) ind + constP (squaredMagnitudeA a))
        | otherwise -> []

instance PolynomialFactorization AComplex where
  factorizeSF f = do
    (a,i) <- rootsAN f
    -- i must be 1
    return (ind - constP a)

instance (KnownNat p) => PolynomialFactorization (PrimeField p) where
  factorizeSF f = unsafePerformIO (factorCZIO f)
  factorizeSFIO f = factorCZIO f
