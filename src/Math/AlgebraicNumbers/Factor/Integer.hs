module Math.AlgebraicNumbers.Factor.Integer where
import Math.AlgebraicNumbers.Prelude
import Math.AlgebraicNumbers.Class
import Math.AlgebraicNumbers.UniPoly
import Math.AlgebraicNumbers.Factor.Hensel
import System.Random (RandomGen,getStdRandom)

-- Input: nonzero, primitive, squarefree
factorInteger :: (RandomGen g) => UniPoly Integer -> g -> ([UniPoly Integer], g)
factorInteger = factorHensel

factorIntegerIO :: UniPoly Integer -> IO [UniPoly Integer]
factorIntegerIO f = getStdRandom (factorInteger f)
