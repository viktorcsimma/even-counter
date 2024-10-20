-- Some tests with the QuickCheck Haskell library.
-- Here, you can finely integrate Agda code
-- with the functions and random generators of QuickCheck.

-- You can run these tests through `cabal test`.

{-# OPTIONS --erasure #-}
module Test.Haskell.Parity where
{-# FOREIGN AGDA2HS {-# LANGUAGE StandaloneDeriving #-} #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_==_; _+_; _*_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
open import Haskell.Prim.Either
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Show
open import Haskell.Prim using
    (Bool; True; False; List; []; _∷_; fromString; IsTrue; if_then_else_; _$_; _∘_)

-- for some reason, ⊤ and tt are needed for FromNat instances to work
open import Agda.Builtin.Unit

-- also for literals:
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromString
open import Haskell.Prim.String
open import Haskell.Prim.Integer

open import Haskell.Prim.Num

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
prop_correctWithTwoEven : Int -> Int -> Bool
prop_correctWithTwoEven x y =
  eitherAddInt (2 * x) (2 * y)
    == Right (2 * x + 2 * y)
{-# COMPILE AGDA2HS prop_correctWithTwoEven #-}

-- Similarly when one of the parameters is not even.
prop_correctWithOddAndEven : Int -> Int -> Bool
prop_correctWithOddAndEven x y =
  eitherAddInt (2 * x + 1) (2 * y)
    == Left "first parameter is odd"
{-# COMPILE AGDA2HS prop_correctWithOddAndEven #-}

prop_correctWithEvenAndOdd : Int -> Int -> Bool
prop_correctWithEvenAndOdd x y =
  eitherAddInt (2 * x) (2 * y + 1)
    == Left "second parameter is odd"
{-# COMPILE AGDA2HS prop_correctWithEvenAndOdd #-}

prop_correctWithTwoOdd : Int -> Int -> Bool
prop_correctWithTwoOdd x y =
  eitherAddInt (2 * x + 1) (2 * y + 1)
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

