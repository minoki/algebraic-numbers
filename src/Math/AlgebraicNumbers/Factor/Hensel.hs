module Math.AlgebraicNumbers.Factor.Hensel where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.Factor.BigPrime (factorCoefficientBound,primeFieldFromInteger,coprimeModP,oneNorm,partitions)
import Math.AlgebraicNumbers.Factor.CantorZassenhaus (factorCZ)
import Data.FiniteField (PrimeField,char,toInteger)
import System.Random (RandomGen,getStdRandom)
import GHC.TypeLits (KnownNat,natVal)
import Data.Reflection (reifyNat)
import Data.Proxy (Proxy)
import Math.NumberTheory.Primes.Sieve (primes)
import Control.Monad (guard)
import Prelude (mod)
import qualified Prelude

-- Assumption:
--   f === g * h  (mod p)
--   h is monic
-- Output (g',h'):
--   f === g' * h'  (mod p^l)
--   h' is monic
henselLifting2 :: (KnownNat p) => Int -> UniPoly Integer -> UniPoly (PrimeField p) -> UniPoly (PrimeField p) -> (UniPoly Integer, UniPoly Integer)
henselLifting2 l f g h =
  let (u,s,t) = exEuclid g h
      -- s * g + t * h == u
      g_ = mapCoeff toInteger g
      h_ = mapCoeff toInteger h
      s_ = mapCoeff toInteger (s `divide` u)
      t_ = mapCoeff toInteger (t `divide` u)
  in loop 1 p g_ h_ s_ t_
  where
    p = char (leadingCoefficient g)
    g0 = mapCoeff toInteger g
    h0 = mapCoeff toInteger h
    loop i m g h s t | i >= l = (g, h)
                     | otherwise = loop (2 * i) (m^2) g' h' s' t'
      where
        -- Hensel step
        -- Assumption:
        --   f - g * h === 0  (mod m)
        --   s * g + t * h === 1  (mod m)
        --   h is monic
        --   degree f = degree g + degree h
        --   degree s < degree h
        --   degree t < degree g
        -- Output:
        --   f - g' * h' === 0  (mod m^2)
        --   s' * g' + t' * h' === 1  (mod m)
        --   h' is monic
        --   g === g', h === h'  (mod m)
        --   s === s', t === t'  (mod m)
        --   degree g == degree g'
        --   degree h == degree h'
        --   degree s' < degree h'
        --   degree t' < degree g'
        e = mapCoeff (`mod` m^2) (f - g * h)
        (q,r) = (s * e) `monicDivMod` h
        g' = mapCoeff (`mod` m^2) (g + t * e + q * g)
        h' = mapCoeff (`mod` m^2) (h + r)
        b = mapCoeff (`mod` m^2) (s * g' + t * h' - 1)
        (c,d) = (s * b) `monicDivMod` h'
        s' = mapCoeff (`mod` m^2) (s - d)
        t' = mapCoeff (`mod` m^2) (t - t * b - c * g')

inverseMod :: Integer -> Integer -> Integer
inverseMod x m = case exEuclid x m of
                   -- s == t * x + _ * m
                   (s,t,_) | s == 1 || s == -1 -> s * t
                           | otherwise -> error (show x ++ " has no inverse modulo " ++ show m)

-- Assumption:
--   f === leadingCoefficient f * product gs  (mod p)
--   gs are monic
-- Output:
--   let gs' = henselLift l f gs
--   f === leadingCoefficient f * product gs'  (mod p^l)
--   gs' are monic
henselLifting :: (KnownNat p) => Int -> UniPoly Integer -> [UniPoly (PrimeField p)] -> [UniPoly Integer]
henselLifting l f [] = [] -- f must be 1
henselLifting l f [g] = [mapCoeff (\a -> inv_lc_f * a `mod` (p^l)) f] -- f == g
  where inv_lc_f = inverseMod (leadingCoefficient f) (p^l)
        p = char (leadingCoefficient g)
henselLifting l f gs =
  let (gs1,gs2) = splitAt (length gs `Prelude.div` 2) gs
      g = fromInteger (leadingCoefficient f) * product gs1
      h = product gs2
      (g',h') = henselLifting2 l f g h
  in henselLifting l g' gs1 ++ henselLifting l h' gs2

-- Input: nonzero, primitive, squarefree
factorHensel :: (RandomGen g) => UniPoly Integer -> g -> ([UniPoly Integer], g)
factorHensel f =
  let lc_f = leadingCoefficient f
      bound = factorCoefficientBound f * lc_f
      p:_ = filter (\p -> lc_f `mod` p /= 0 && reifyNat p coprimeModP f (diffP f)) $ tail primes
  in reifyNat p factorWithPrime bound f

factorHenselIO :: UniPoly Integer -> IO [UniPoly Integer]
factorHenselIO f = getStdRandom (factorHensel f)

-- p must be prime
factorWithPrime :: (KnownNat p, RandomGen g) => Proxy p -> Integer -> UniPoly Integer -> g -> ([UniPoly Integer], g)
factorWithPrime proxy bound f gen =
  let p = natVal proxy
      f' = toMonic $ mapCoeff (primeFieldFromInteger proxy) f -- :: UniPoly (PrimeField p)
      (modularFactorsP, gen') = factorCZ f' gen
      -- Choose l and m so that  m = p^l > 2 * bound + 1
      (l,m) | p^l' > 2 * bound + 1 = (l',p^l')
            | otherwise = head $ filter (\(i,m) -> m > 2 * bound + 1) $ iterate (\(i,m) -> (i + 1, m * p)) (l',p^l')
        where l' = ceiling (log (fromInteger (2 * bound + 1) :: Double) / log (fromInteger p :: Double)) :: Int
      modularFactors = henselLifting l f modularFactorsP
      -- f === leadingCoefficient f * product modularFactors  (mod p^l)
  in (factorCombinationsModulo m bound 1 f modularFactors, gen')

-- m >= 2 * bound + 1
-- f === leadingCoefficient f * product modularFactors  (mod m)
factorCombinationsModulo :: Integer -> Integer -> Int -> UniPoly Integer -> [UniPoly Integer] -> [UniPoly Integer]
factorCombinationsModulo m bound k f modularFactors = loop k f modularFactors
  where loop k f [] = [] -- f must be 1
        loop k f modularFactors
          | 2 * k > length modularFactors = [f] -- f is already irreducible
          | otherwise = case tryFactorCombinations of
              [] -> loop (k+1) f modularFactors
              (g,h,rest):_ -> g : loop k h rest
          where tryFactorCombinations = do
                  (s,rest) <- partitions k modularFactors
                  -- length s == k, s ++ rest == modularFactors (as a set)
                  let lc_f = fromInteger (leadingCoefficient f)
                      g = mapCoeff toInteger_ (lc_f * product s)
                      h = mapCoeff toInteger_ (lc_f * product rest)
                  guard (oneNorm g * oneNorm h <= bound)
                  return (primitivePart g, primitivePart h, rest)

        toInteger_ :: Integer -> Integer
        toInteger_ n = case n `mod` m of
                         k | 2 * k > m -> k - m
                           | otherwise -> k
