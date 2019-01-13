{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Math.AlgebraicNumbers.Class where
import Math.AlgebraicNumbers.Prelude
import Data.Ratio
import Data.FiniteField
import qualified Data.Vector as V
import GHC.TypeLits (KnownNat)
import qualified Prelude
import Data.Int
import Data.Word

infixl 7 `divide`
infixl 7 `divD`, `modD`

-- | Integral domain
--
-- An integral domain is a commutative ring with \(1 \ne 0\)
-- and doesn't have a nontrivial zero divisors.
class (Num a) => IntegralDomain a where
  -- | Division
  --
  -- If @a@ is a multiple of @b@, @divide a b@ returns @c@ such that @a = b * c@.
  -- The behavior is undefined if @a@ is not a multiple of @b@.
  divide :: a -> a -> a

-- | GCD domain
class (IntegralDomain a) => GCDDomain a where
  -- | Returns a greatest common divisor
  gcdD :: a -> a -> a

  -- | Returns the content of a polynomial with given coefficients.
  contentV :: V.Vector a -> a
  contentV = V.foldr gcdD 0

  lcmD :: a -> a -> a
  lcmD x y = x * y `divide` gcdD x y

-- | Euclidean domain
class (GCDDomain a) => EuclideanDomain a where
  -- | Euclidean division
  divModD :: a -> a -> (a, a)
  divD, modD :: a -> a -> a
  divD x y = fst (divModD x y)
  modD x y = snd (divModD x y)

class (IntegralDomain a, Fractional a) => Field a where
  characteristicP :: proxy a -> Integer

data WhichPerfectField a where
  CharZero :: (FieldWithCharZero a) => WhichPerfectField a
  PositiveChar :: (PerfectFieldWithPositiveChar a) => WhichPerfectField a

class (Field a) => PerfectField a where
  whichPerfectField :: WhichPerfectField a

class (PerfectField a) => FieldWithCharZero a
class (Field a) => FieldWithPositiveChar a

class (FieldWithPositiveChar a, PerfectField a) => PerfectFieldWithPositiveChar a where
  pthRoot :: a -> a

instance (Integral a) => Field (Ratio a) where
  characteristicP _ = 0
instance (Integral a) => PerfectField (Ratio a) where
  whichPerfectField = CharZero
instance (Integral a) => FieldWithCharZero (Ratio a)

instance (KnownNat p) => Field (PrimeField p) where
  characteristicP _ = char (undefined :: PrimeField p) -- uses ScopedTypeVariables
instance (KnownNat p) => PerfectField (PrimeField p) where
  whichPerfectField = PositiveChar
instance (KnownNat p) => FieldWithPositiveChar (PrimeField p)
instance (KnownNat p) => PerfectFieldWithPositiveChar (PrimeField p) where
  pthRoot = Data.FiniteField.pthRoot



-- | Extended Euclidean algorithm (EEA)
--
-- case exEuclid f g of (g, s, t) ->
--   g == gcdD f g  (up to unit)
--   s * f + t * g == g
--
-- >>> exEuclid 32 63
-- (1,2,-1)
-- >>> exEuclid 28 63
-- (7,-2,1)
exEuclid :: (Eq a, EuclideanDomain a) => a -> a -> (a, a, a)
exEuclid f g = loop 1 0 0 1 f g
  where loop u0 u1 v0 v1 f 0 = (f, u0, v0)
        loop u0 u1 v0 v1 f g =
          case divModD f g of
            (q,r) -> loop u1 (u0 - q * u1) v1 (v0 - q * v1) g r

instance (Integral a) => IntegralDomain (Ratio a) where
  divide = (/)

instance (KnownNat p) => IntegralDomain (PrimeField p) where
  divide = (/)

divideIntegral :: (Integral a) => a -> a -> a
divideIntegral x y = case Prelude.divMod x y of
  (d,0) -> d
  (d,_) -> {-trace ("trying to divide " ++ show x ++ " by " ++ show y)-} d
  --_ -> error ("cannot divide " ++ show x ++ " by " ++ show y)
  -- Just use Prelude.div?

instance IntegralDomain Integer where divide = divideIntegral
instance IntegralDomain Int     where divide = divideIntegral
instance IntegralDomain Int8    where divide = divideIntegral
instance IntegralDomain Int16   where divide = divideIntegral
instance IntegralDomain Int32   where divide = divideIntegral
instance IntegralDomain Int64   where divide = divideIntegral
instance IntegralDomain Word    where divide = divideIntegral
instance IntegralDomain Word8   where divide = divideIntegral
instance IntegralDomain Word16  where divide = divideIntegral
instance IntegralDomain Word32  where divide = divideIntegral
instance IntegralDomain Word64  where divide = divideIntegral

-- | Default implementation of 'gcdD' for fields
fieldGcd :: (Eq a, Fractional a) => a -> a -> a
fieldGcd 0 0 = 0
fieldGcd _ _ = 1

-- | Default implementation of 'lcmD' for fields
fieldLcm :: (Eq a, Fractional a) => a -> a -> a
fieldLcm 0 0 = 0
fieldLcm x y = x * y

-- | Default implementation of 'contentV' for fields
fieldContentV :: (Eq a, Fractional a) => V.Vector a -> a
fieldContentV xs | V.null xs = 0
                 | otherwise = V.last xs

instance (Integral a) => GCDDomain (Ratio a) where
  gcdD = fieldGcd; lcmD = fieldLcm; contentV = fieldContentV

instance (KnownNat p) => GCDDomain (PrimeField p) where
  gcdD = fieldGcd; lcmD = fieldLcm; contentV = fieldContentV

newtype WrappedField a = WrappedField { getField :: a }
  deriving (Eq,Show,Ord,Num,Fractional,Real,Floating,RealFrac,RealFloat)

instance (Fractional a) => IntegralDomain (WrappedField a) where
  divide = (/)

instance (Eq a, Fractional a) => GCDDomain (WrappedField a) where
  gcdD = fieldGcd
  lcmD = fieldLcm
  contentV = fieldContentV

instance (Eq a, Fractional a) => EuclideanDomain (WrappedField a) where
  divModD x y = (x / y, 0)
  divD = (/)
  modD _ _ = 0

contentVIntegral :: (GCDDomain a, Integral a) => V.Vector a -> a
contentVIntegral xs
  | V.null xs = 0
  | V.last xs < 0 = negate (gcdV 0 xs) -- The sign of content reflects that of leading coefficient.
  | otherwise = gcdV 0 xs -- This is equivalent to @foldr gcd 0@ up to short-circuit evaluation.
    where
      gcdV 1 _ = 1
      gcdV a v | V.null v = a
               | otherwise = gcdV (gcdD (V.last v) a) (V.init v)

instance GCDDomain Integer where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Int where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Int8 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Int16 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Int32 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Int64 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Word where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Word8 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Word16 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Word32 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral
instance GCDDomain Word64 where
  gcdD = Prelude.gcd; lcmD = Prelude.lcm; contentV = contentVIntegral

instance EuclideanDomain Integer where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Int where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Int8 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Int16 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Int32 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Int64 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Word where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Word8 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Word16 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Word32 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod
instance EuclideanDomain Word64 where
  divModD = Prelude.divMod; divD = Prelude.div; modD = Prelude.mod

class (Real a) => IsRational a
instance IsRational Integer
instance IsRational Int
instance IsRational Int8
instance IsRational Int16
instance IsRational Int32
instance IsRational Int64
instance IsRational Word
instance IsRational Word8
instance IsRational Word16
instance IsRational Word32
instance IsRational Word64
instance (Integral a) => IsRational (Ratio a)

toRational :: (IsRational a) => a -> Rational
toRational = Prelude.toRational

-- | Returns the sign of a number as 'Int'
sign :: (Ord a, Num a) => a -> Int
sign x = case compare x 0 of
           EQ -> 0
           LT -> -1
           GT -> 1
