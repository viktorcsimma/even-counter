-- Some simple Agda tests for demonstration.

-- If added to All.agda,
-- the typechecker checks them at every compilation.
{-# OPTIONS --erasure #-}
module Test.Parity where

open import Agda.Builtin.Equality
open import Agda.Builtin.Int
open import Haskell.Prim.Either

open import Haskell.Prelude

open import Logic

-- For now, we just do a few evaluations of eitherAddInt,
-- but you can test anything you wish here.
test1 : eitherAddInteger 2 -10 ≡ Right -8
test1 = refl
test2 : eitherAddInteger 0 0 ≡ Right 0
test2 = refl
test3 : eitherAddInteger -1 0 ≡ Left "first parameter is odd"
test3 = refl
test4 : eitherAddInteger 0 7 ≡ Left "second parameter is odd"
test4 = refl
test5 : eitherAddInteger 9 5 ≡ Left "first parameter is odd"
test5 = refl
