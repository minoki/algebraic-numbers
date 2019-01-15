{-# LANGUAGE HexFloatLiterals #-}
import Prelude
import Test.HUnit
import Math.AlgebraicNumbers.CReal
import Math.AlgebraicNumbers.AReal

-- TODO: Consider property-based testing
testToDouble :: Double -> Test
testToDouble x = TestCase $ do
  let x = pi :: Double
  let y = toRational x
  assertEqual "toDouble a = a" x (toDouble y)
  assertEqual "toDoubleTowardPositive a = a" x (toDoubleTowardPositive y)
  assertEqual "toDoubleTowardNegative a = a" x (toDoubleTowardNegative y)
  assertEqual "toDoubleTowardZero a = a" x (toDoubleTowardZero y)

testToDouble2 :: Test
testToDouble2 = TestCase $ do
  assertEqual "0x1.1p-1074 -> 0x1p-1074" 0x1p-1074 (toDouble (0x1.1p-1074 :: Rational))
  assertEqual "0x1.8p-1074 -> 0x1p-1073" 0x1p-1073 (toDouble (0x1.8p-1074 :: Rational))
  assertEqual "0x1.8p-1075 -> 0x1p-1074" 0x1p-1074 (toDouble (0x1.8p-1075 :: Rational))
  assertEqual "0x1.0p-1075 -> 0" 0 (toDouble (0x1.0p-1075 :: Rational))
  assertEqual "0x1.1p-1074 ->[+] 0x1p-1073" 0x1p-1073 (toDoubleTowardPositive (0x1.1p-1074 :: Rational))
  assertEqual "0x1.8p-1074 ->[+] 0x1p-1073" 0x1p-1073 (toDoubleTowardPositive (0x1.8p-1074 :: Rational))
  assertEqual "0x1.8p-1075 ->[+] 0x1p-1074" 0x1p-1074 (toDoubleTowardPositive (0x1.8p-1075 :: Rational))
  assertEqual "0x1.0p-1075 ->[+] 0x1p-1074" 0x1p-1074 (toDoubleTowardPositive (0x1.0p-1075 :: Rational))
  assertEqual "0x1.1p-1074 ->[-] 0x1p-1074" 0x1p-1074 (toDoubleTowardNegative (0x1.1p-1074 :: Rational))
  assertEqual "0x1.8p-1074 ->[-] 0x1p-1074" 0x1p-1074 (toDoubleTowardNegative (0x1.8p-1074 :: Rational))
  assertEqual "0x1.8p-1075 ->[-] 0" 0 (toDoubleTowardNegative (0x1.8p-1075 :: Rational))
  assertEqual "0x1.0p-1075 ->[-] 0" 0 (toDoubleTowardNegative (0x1.0p-1075 :: Rational))
  assertEqual "0x1.1p-1074 ->[0] 0x1p-1074" 0x1p-1074 (toDoubleTowardZero (0x1.1p-1074 :: Rational))
  assertEqual "0x1.8p-1074 ->[0] 0x1p-1074" 0x1p-1074 (toDoubleTowardZero (0x1.8p-1074 :: Rational))
  assertEqual "0x1.8p-1075 ->[0] 0" 0 (toDoubleTowardZero (0x1.8p-1075 :: Rational))
  assertEqual "0x1.0p-1075 ->[0] 0" 0 (toDoubleTowardZero (0x1.0p-1075 :: Rational))
  assertEqual "-0x1.1p-1074 ->[+] -0x1p-1074" (-0x1p-1074) (toDoubleTowardPositive (-0x1.1p-1074 :: Rational))
  assertEqual "-0x1.8p-1074 ->[+] -0x1p-1074" (-0x1p-1074) (toDoubleTowardPositive (-0x1.8p-1074 :: Rational))
  assertBool  "-0x1.8p-1075 ->[+] -0" $ isNegativeZero (toDoubleTowardPositive (-0x1.8p-1075 :: Rational))
  assertBool  "-0x1.0p-1075 ->[+] -0" $ isNegativeZero (toDoubleTowardPositive (-0x1.0p-1075 :: Rational))
  assertEqual "-0x1.1p-1074 ->[-] -0x1p-1073" (-0x1p-1073) (toDoubleTowardNegative (-0x1.1p-1074 :: Rational))
  assertEqual "-0x1.8p-1074 ->[-] -0x1p-1073" (-0x1p-1073) (toDoubleTowardNegative (-0x1.8p-1074 :: Rational))
  assertEqual "-0x1.8p-1075 ->[-] -0x1p-1074" (-0x1p-1074) (toDoubleTowardNegative (-0x1.8p-1075 :: Rational))
  assertEqual "-0x1.0p-1075 ->[-] -0x1p-1074" (-0x1p-1074) (toDoubleTowardNegative (-0x1.0p-1075 :: Rational))
  assertEqual "-0x1.1p-1074 ->[0] -0x1p-1074" (-0x1p-1074) (toDoubleTowardZero (-0x1.1p-1074 :: Rational))
  assertEqual "-0x1.8p-1074 ->[0] -0x1p-1074" (-0x1p-1074) (toDoubleTowardZero (-0x1.8p-1074 :: Rational))
  assertEqual "-0x1.8p-1075 ->[0] 0" 0 (toDoubleTowardZero (-0x1.8p-1075 :: Rational))
  assertEqual "-0x1.0p-1075 ->[0] 0" 0 (toDoubleTowardZero (-0x1.0p-1075 :: Rational))

testToDouble3 :: Test
testToDouble3 = TestCase $ do
  let inf = 1.0 / 0.0 :: Double
  assertEqual "0x1.fffffffffffff7fp1023 -> 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDouble (0x1.fffffffffffff7fp1023 :: Rational)
  assertEqual "0x1.fffffffffffff7fp1023 ->[+] inf" inf $ toDoubleTowardPositive (0x1.fffffffffffff7fp1023 :: Rational)
  assertEqual "0x1.fffffffffffff7fp1023 ->[-] 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDoubleTowardNegative (0x1.fffffffffffff7fp1023 :: Rational)
  assertEqual "0x1.fffffffffffff8p1023  -> inf" inf $ toDouble (0x1.fffffffffffff8p1023 :: Rational)
  assertEqual "0x1.fffffffffffff8p1023  ->[+] inf" inf $ toDoubleTowardPositive (0x1.fffffffffffff8p1023 :: Rational)
  assertEqual "0x1.fffffffffffff8p1023  ->[-] 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDoubleTowardNegative (0x1.fffffffffffff7fp1023 :: Rational)
  assertEqual "0x1p1024 -> inf" inf $ toDouble (0x1p1024 :: Rational)
  assertEqual "0x1p1024 ->[+] inf" inf $ toDoubleTowardPositive (0x1p1024 :: Rational)
  assertEqual "0x1p1024 ->[-] 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDoubleTowardNegative (0x1p1024 :: Rational)
  assertEqual "0x1p1024 ->[0] 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDoubleTowardZero (0x1p1024 :: Rational)
  assertEqual "0x1p1025 -> inf" inf $ toDouble (0x1p1025 :: Rational)
  assertEqual "0x1p1025 ->[+] inf" inf $ toDoubleTowardPositive (0x1p1025 :: Rational)
  assertEqual "0x1p1025 ->[-] 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDoubleTowardNegative (0x1p1025 :: Rational)
  assertEqual "0x1p1025 ->[0] 0x1.fffffffffffffp1023" 0x1.fffffffffffffp1023 $ toDoubleTowardZero (0x1p1025 :: Rational)

testToDouble4 = TestCase $ assertEqual "toDouble (sqrtA 2) == sqrt 2" (sqrt 2) (toDouble (sqrtA 2))

tests = TestList [TestLabel "toDouble with pi" (testToDouble pi)
                 ,TestLabel "toDouble with 1/pi" (testToDouble (1/pi))
                 ,TestLabel "toDouble with -1/pi" (testToDouble (-1/pi))
                 ,TestLabel "toDouble with pi*2^(-1050)" (testToDouble (pi * (1/2)^1050))
                 ,TestLabel "toDouble with 0x1p-1074" (testToDouble 0x1p-1074)
                 ,TestLabel "toDouble with 0x1.fffffffffffffp1023" (testToDouble 0x1.fffffffffffffp1023)
                 ,TestLabel "toDouble with subnormals" testToDouble2
                 ,TestLabel "toDouble with large numbers" testToDouble3
                 ,TestLabel "toDouble with algebraic numbers" testToDouble4
                 ]

main = runTestTT tests
