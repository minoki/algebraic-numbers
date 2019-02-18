import Test.DocTest
main = doctest ["-isrc", "src/", "-XBangPatterns", "-XNoImplicitPrelude", "-Wno-deferred-type-errors", "-Wno-inline-rule-shadowing"]
