-- Some tests with the QuickCheck Haskell library.
-- Here, you can finely integrate Agda code
-- with the functions and random generators of QuickCheck.

-- You can run these tests through `cabal test`.

{-# OPTIONS --erasure #-}
module Test.Haskell.Parity where
{-# FOREIGN AGDA2HS {-# LANGUAGE StandaloneDeriving #-} #-}

open import Haskell.Prelude


open import Logic

{-# FOREIGN AGDA2HS
import Test.QuickCheck
#-}


{-# FOREIGN AGDA2HS
{-
-- We would need an Arbitrary instance for the naturals
-- if we wanted to do tests on them.
instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink = shrinkIntegral

-- See also QuickCheck's documentation
-- for defining generators.
-}
#-}

-- Actually, we can write the functions themselves in Agda.

-- Here, we provide two integers (from generated parameters)
-- which are guaranteed to be even.
prop_correctWithTwoEven : Integer -> Integer -> Bool
prop_correctWithTwoEven x y =
  eitherAddInteger (2 * x) (2 * y)
    == Right (2 * x + 2 * y)
{-# COMPILE AGDA2HS prop_correctWithTwoEven #-}

-- Similarly when one of the parameters is not even.
prop_correctWithOddAndEven : Integer -> Integer -> Bool
prop_correctWithOddAndEven x y =
  eitherAddInteger (2 * x + 1) (2 * y)
    == Left "first parameter is odd"
{-# COMPILE AGDA2HS prop_correctWithOddAndEven #-}

prop_correctWithEvenAndOdd : Integer -> Integer -> Bool
prop_correctWithEvenAndOdd x y =
  eitherAddInteger (2 * x) (2 * y + 1)
    == Left "second parameter is odd"
{-# COMPILE AGDA2HS prop_correctWithEvenAndOdd #-}

prop_correctWithTwoOdd : Integer -> Integer -> Bool
prop_correctWithTwoOdd x y =
  eitherAddInteger (2 * x + 1) (2 * y + 1)
    == Left "first parameter is odd"
{-# COMPILE AGDA2HS prop_correctWithTwoOdd #-}


{-# FOREIGN AGDA2HS
-- This contains all the propositions we would like to test.
-- Actually, this will be called by main.
parityTestAll :: IO Bool
parityTestAll =
  and <$> mapM (isSuccess <$>)
  [ quickCheckResult prop_correctWithTwoEven
  , quickCheckResult prop_correctWithOddAndEven
  , quickCheckResult prop_correctWithEvenAndOdd
  , quickCheckResult prop_correctWithTwoOdd
  ]
#-}

