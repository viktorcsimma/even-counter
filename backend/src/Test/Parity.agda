-- Some simple Agda tests for demonstration.

-- If added to All.agda,
-- the typechecker checks them at every compilation.
{-# OPTIONS --erasure #-}
module Test.Parity where

open import Agda.Builtin.Equality
open import Agda.Builtin.Int
open import Haskell.Prim.Either

-- for some reason, ⊤ and tt are needed for FromNat instances to work
open import Agda.Builtin.Unit

-- also for literals:
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromString
open import Haskell.Prim.String
open import Haskell.Prim.Integer

open import Logic

-- For now, we just do a few evaluations of eitherAddInt,
-- but you can test anything you wish here.
test1 : eitherAddInt 2 -10 ≡ Right -8
test1 = refl
test2 : eitherAddInt 0 0 ≡ Right 0
test2 = refl
test3 : eitherAddInt -1 0 ≡ Left "first parameter is odd"
test3 = refl
test4 : eitherAddInt 0 7 ≡ Left "second parameter is odd"
test4 = refl
test5 : eitherAddInt 9 5 ≡ Left "first parameter is odd"
test5 = refl
