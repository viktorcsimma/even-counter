-- An example file
-- containing provably safe logic for an operator
-- keeping a counter even.
{-# OPTIONS --erasure #-}

module Logic where

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Equality

open import Haskell.Prim.Integer
open import Haskell.Prim.Either
open import Agda.Builtin.FromString     -- so that we can use string literals
open import Haskell.Prim.String
open import Haskell.Prim using (if_then_else_)

open import Tool.ErasureProduct

-- The empty type (false statement).
data ⊥ : Set where

-- A statement that a given natural is even.
@0 EvenNat : Nat -> Set
EvenNat zero = ⊤
EvenNat (suc zero) = ⊥
EvenNat (suc (suc n)) = EvenNat n

-- A statement that a given integer is even.
@0 EvenInt : Int -> Set
EvenInt (pos n) = EvenNat n
EvenInt (negsuc n) = EvenNat (suc n)

-- A proof that the sum of two even naturals
-- is also even.
@0 natSumIsEven : (m n : Nat) -> @0 {EvenNat m} -> @0 {EvenNat n} -> EvenNat (m + n)
natSumIsEven zero n {_} {en} = en
-- suc zero is not even; Agda deduces this
natSumIsEven (suc (suc m)) n {e2pm} {en} = natSumIsEven m n {e2pm} {en}

-- A helper identity.
@0 cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

@0 subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl Px = Px

-- A helper identity.
@0 m+sn≡sm+n : (m n : Nat) -> m + suc n ≡ suc m + n
m+sn≡sm+n zero n = refl
m+sn≡sm+n (suc m) n = cong suc (m+sn≡sm+n m n)

@0 symm : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
symm refl = refl

-- A proof that the sum of two even integers
-- is also even.
@0 intSumIsEven : (a b : Int) -> @0 {EvenInt a} -> @0 {EvenInt b} -> EvenInt (addInteger a b)
intSumIsEven (pos m) (pos n) {em} {en} = natSumIsEven m n {em} {en}
-- here, the pattern matchings in the definitions of addInteger and ltNat might help
intSumIsEven (pos zero) (negsuc (suc n)) {_} {en} = en
intSumIsEven (pos (suc (suc m))) (negsuc (suc zero)) {em} {_} = em
intSumIsEven (pos (suc (suc m))) (negsuc (suc (suc n))) {em} {esn} = intSumIsEven (pos m) (negsuc n) {em} {esn}
-- similarly
intSumIsEven (negsuc m) (pos zero) {esm} {_} = esm
intSumIsEven (negsuc (suc zero)) (pos (suc (suc n))) {_} {en} = en
intSumIsEven (negsuc (suc (suc m))) (pos (suc (suc n))) {esm} {en} = intSumIsEven (negsuc m) (pos n) {esm} {en}
-- and here:
intSumIsEven (negsuc m) (negsuc n) {esm} {esn} = subst EvenNat {suc m + suc n} {suc (suc (m + n))} (cong suc (m+sn≡sm+n m n)) (natSumIsEven (suc m) (suc n) {esm} {esn})

-- All callable functions will be private,
-- except the one we really have to call from Haskell.
-- This ensures we do not call an intermediate function
-- by accident.
private
  -- A function calculating whether a given natural is even
  -- and returning a Bool.
  isEvenNat : Nat -> Bool
  isEvenNat zero = true
  isEvenNat (suc zero) = false
  isEvenNat (suc (suc n)) = isEvenNat n
  {-# FOREIGN AGDA2HS
  -- Here, it is better to resort to
  -- Prelude's builtin function,
  -- as it is faster.
  isEvenNat :: Natural -> Bool
  isEvenNat = even
  #-}

  -- A function calculating whether a given integer is even
  -- and returning a Bool.
  isEvenInt : Int -> Bool
  isEvenInt (pos n) = isEvenNat n
  isEvenInt (negsuc n) = isEvenNat (suc n)
  {-# FOREIGN AGDA2HS
  -- Similarly.
  isEvenInt :: Integer -> Bool
  isEvenInt = even
  #-}

  -- A proof that EvenNat x is equivalent to isEvenNat x being true.
  @0 equivToEvenNat : {x : Nat} -> isEvenNat x ≡ true -> EvenNat x
  equivToEvenNat {zero} it = tt
  equivToEvenNat {suc (suc x)} it = equivToEvenNat {x} it

  -- A proof that EvenInt x is equivalent to isEvenInt x being true.
  @0 equivToEvenInt : {x : Int} -> isEvenInt x ≡ true -> EvenInt x
  equivToEvenInt {pos n} it = equivToEvenNat {n} it
  equivToEvenInt {negsuc (suc n)} it = equivToEvenNat {n} it

  -- Adding natural numbers that are guaranteed to be even;
  -- returning the result along with a proof that it is also even.
  addEvenNats : (n m : Nat) -> @0 {EvenNat n} -> @0 {EvenNat m} -> Σ0 Nat EvenNat
  addEvenNats n m {en} {em} = n + m :&: natSumIsEven n m {en} {em}
  {-# COMPILE AGDA2HS addEvenNats #-}

  -- In order to be able to use addInteger here:
  {-# FOREIGN AGDA2HS
  addInteger :: Integer -> Integer -> Integer
  addInteger = (+)
  #-}

  -- Adding integers that are guaranteed to be even;
  -- returning the result along with a proof that it is also even.
  addEvenInts : (x y : Int) -> @0 {EvenInt x} -> @0 {EvenInt y} -> Σ0 Int EvenInt
  addEvenInts x y {ex} {ey} = addInteger x y :&: intSumIsEven x y {ex} {ey}
  {-# COMPILE AGDA2HS addEvenInts #-}

-- Returns an error message in Left if either of the two parameters is odd;
-- otherwise returns the result in Right.
-- This is what we are going to call from Haskell.
-- The if_then_else_ construction of agda2hs allows us
-- to use instances of b ≡ true or b ≡ false in our proofs
-- (but we need those lambdas).
eitherAddInt : Int -> Int -> Either String Int
eitherAddInt x y = if (isEvenInt x) then (λ {{isTrue₁}} → 
                      if (isEvenInt y) then (λ {{isTrue₂}} →
                        Right (proj₁ (addEvenInts x y {equivToEvenInt {x} isTrue₁} {equivToEvenInt {y} isTrue₂}))
                      ) else Left "second parameter is odd"
                  ) else Left "first parameter is odd"
{-# COMPILE AGDA2HS eitherAddInt #-}
