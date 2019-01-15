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
import System.Random (RandomGen,getStdRandom,mkStdGen)
import Control.Monad.State (runState,state)

class PolynomialFactorization a where
  -- Assume that the input is non-zero, primitive and square-free
  factorizeSFWithRandomGen :: (RandomGen g) => UniPoly a -> g -> ([UniPoly a], g)
  factorizeSFIO :: UniPoly a -> IO [UniPoly a]
  factorizeSFIO = getStdRandom . factorizeSFWithRandomGen

instance PolynomialFactorization Integer where
  factorizeSFWithRandomGen = factorInteger

instance (Integral a, GCDDomain a, PolynomialFactorization a) => PolynomialFactorization (Ratio a) where
  factorizeSFWithRandomGen f = runState $ do
    let commonDenominator = V.foldl' (\a b -> Prelude.lcm a (denominator b)) 1 (coeff f)
        pp = primitivePart $ mapCoeff (\x -> numerator x * (commonDenominator `Prelude.div` denominator x)) f
    map (toMonic . mapCoeff fromIntegral) <$> state (factorizeSFWithRandomGen pp)

instance PolynomialFactorization AReal where
  factorizeSFWithRandomGen f = runState $ return $ do
    (a,i) <- rootsA f
    case a of
      FromReal a -> return (ind - constP a)
      a | imagPartA a > 0 -> return (ind^2 - scaleP (2 * realPartA a) ind + constP (squaredMagnitudeA a))
        | otherwise -> []

instance PolynomialFactorization AComplex where
  factorizeSFWithRandomGen f = runState $ return $ do
    (a,i) <- rootsA f
    -- i must be 1
    return (ind - constP a)

instance (KnownNat p) => PolynomialFactorization (PrimeField p) where
  factorizeSFWithRandomGen = factorCZ

factorizeSFPure :: (PolynomialFactorization a) => UniPoly a -> [UniPoly a]
factorizeSFPure f = fst (factorizeSFWithRandomGen f (mkStdGen 0xc0ffee))
