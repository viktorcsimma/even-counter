-- An example file
-- containing provably safe logic for an operator
-- keeping a counter even.
{-# OPTIONS --erasure #-}

module Logic where

open import Agda.Builtin.Nat hiding (_+_; _*_; _-_)
open import Agda.Builtin.Int renaming (Int to Integer)

open import Haskell.Prelude

open import Tool.ErasureProduct

-- A statement that a given natural is even.
@0 EvenNat : Nat -> Set
EvenNat zero = ⊤
EvenNat (suc zero) = ⊥
EvenNat (suc (suc n)) = EvenNat n

-- A statement that a given integer is even.
@0 EvenInteger : Integer -> Set
EvenInteger (pos n) = EvenNat n
EvenInteger (negsuc n) = EvenNat (suc n)

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
@0 intSumIsEven : (a b : Integer) -> @0 {EvenInteger a} -> @0 {EvenInteger b} -> EvenInteger (a + b)
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
  isEvenNat zero = True
  isEvenNat (suc zero) = False
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
  isEvenInteger : Integer -> Bool
  isEvenInteger (pos n) = isEvenNat n
  isEvenInteger (negsuc n) = isEvenNat (suc n)
  {-# FOREIGN AGDA2HS
  -- Similarly.
  isEvenInteger :: Integer -> Bool
  isEvenInteger = even
  #-}

  -- A proof that EvenNat x is equivalent to isEvenNat x being True.
  @0 equivToEvenNat : {x : Nat} -> isEvenNat x ≡ True -> EvenNat x
  equivToEvenNat {zero} it = tt
  equivToEvenNat {suc (suc x)} it = equivToEvenNat {x} it

  -- A proof that EvenInteger x is equivalent to isEvenInteger x being True.
  @0 equivToEvenInteger : {x : Integer} -> isEvenInteger x ≡ True -> EvenInteger x
  equivToEvenInteger {pos n} it = equivToEvenNat {n} it
  equivToEvenInteger {negsuc (suc n)} it = equivToEvenNat {n} it

  -- Adding natural numbers that are guaranteed to be even;
  -- returning the result along with a proof that it is also even.
  addEvenNats : (n m : Nat) -> @0 {EvenNat n} -> @0 {EvenNat m} -> Σ0 Nat EvenNat
  addEvenNats n m {en} {em} = n + m :&: natSumIsEven n m {en} {em}
  {-# COMPILE AGDA2HS addEvenNats #-}

  -- Adding integers that are guaranteed to be even;
  -- returning the result along with a proof that it is also even.
  addEvenIntegers : (x y : Integer) -> @0 {EvenInteger x} -> @0 {EvenInteger y} -> Σ0 Integer EvenInteger
  addEvenIntegers x y {ex} {ey} = x + y :&: intSumIsEven x y {ex} {ey}
  {-# COMPILE AGDA2HS addEvenIntegers #-}

-- Returns an error message in Left if either of the two parameters is odd;
-- otherwise returns the result in Right.
-- This is what we are going to call from Haskell.
-- The if_then_else_ construction of agda2hs allows us
-- to use instances of b ≡ True or b ≡ False in our proofs
-- (but we need those lambdas).
eitherAddInteger : Integer -> Integer -> Either String Integer
eitherAddInteger x y = if (isEvenInteger x) then (λ {{isTrue₁}} →
                      if (isEvenInteger y) then (λ {{isTrue₂}} →
                        Right (proj₁ (addEvenIntegers x y {equivToEvenInteger {x} isTrue₁} {equivToEvenInteger {y} isTrue₂}))
                      ) else Left "second parameter is odd"
                  ) else Left "first parameter is odd"
{-# COMPILE AGDA2HS eitherAddInteger #-}
