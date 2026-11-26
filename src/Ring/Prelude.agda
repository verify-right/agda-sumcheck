{-# OPTIONS --safe --without-K #-}
module Ring.Prelude where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Ring.Verifier using (both)

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} →
  a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

and-left : {a b : Bool} → both a b ≡ true → a ≡ true
and-left {true} p = refl
and-left {false} ()

and-right : {a b : Bool} → both a b ≡ true → b ≡ true
and-right {true} p = p
and-right {false} ()

nat-eq-refl : (x : Nat) → (x == x) ≡ true
nat-eq-refl zero = refl
nat-eq-refl (suc x) = nat-eq-refl x

nat-eq-sound : (x y : Nat) → (x == y) ≡ true → x ≡ y
nat-eq-sound zero zero _ = refl
nat-eq-sound zero (suc y) ()
nat-eq-sound (suc x) zero ()
nat-eq-sound (suc x) (suc y) h = cong suc (nat-eq-sound x y h)

nat-eq-complete : (x y : Nat) → x ≡ y → (x == y) ≡ true
nat-eq-complete x .x refl = nat-eq-refl x
