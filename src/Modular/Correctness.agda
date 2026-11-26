{-# OPTIONS --safe --without-K #-}
open import Data.Nat.Base using (ℕ)
module Modular.Correctness (k : ℕ) where

open import Data.Bool.Base using (true)
open import Data.Nat.Base using (_+_; _*_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Modular.Operations using (normalize; negative; same; operations)
open import Modular.Ring k using (_≈_; commutativeRing; remainder-idem)
open import Ring.Verifier using (interpolate; lagrange)
import Ring.FromRing as FromRing
import Ring.Interpolation as Interpolation

-- Equality modulo p is decided on remainders.
_≟_ : Decidable _≈_
x ≟ y = normalize k x ℕ.≟ normalize k y

-- Operations and proofs derived from the ring; reduction mod p is the
-- certified normalization.
private
  module Derived = FromRing commutativeRing _≟_ (normalize k) remainder-idem

-- The derived dictionary is definitionally the executable one.
derived-operations : Derived.operations ≡ operations k
derived-operations = refl

same-sound : (x y : ℕ) → same k x y ≡ true → x ≈ y
same-sound = Derived.same-sound

same-complete : (x y : ℕ) → x ≈ y → same k x y ≡ true
same-complete = Derived.same-complete

same-cong : {x x' y y' : ℕ} → x ≈ x' → y ≈ y' → same k x y ≡ same k x' y'
same-cong {x} {x'} {y} {y'} = Derived.same-cong {x} {x'} {y} {y'}

ring-interpolation : (a b r : ℕ) →
  (a + ((b + negative k a) * r)) ≈ (((1 + negative k r) * a) + (r * b))
ring-interpolation = Interpolation.linear-interpolation commutativeRing

interpolation-correct : (a b r : ℕ) →
  interpolate (operations k) a b r ≈ lagrange (operations k) a b r
interpolation-correct = Derived.interpolation-correct

interpolation-of-linear : (a b r : ℕ) →
  interpolate (operations k) a (a + b) r ≈ a + (b * r)
interpolation-of-linear = Derived.interpolation-of-linear

interpolation-at-zero : (a b : ℕ) → interpolate (operations k) a b 0 ≈ a
interpolation-at-zero = Derived.interpolation-at-zero

interpolation-at-one : (a b : ℕ) → interpolate (operations k) a b 1 ≈ b
interpolation-at-one = Derived.interpolation-at-one

module Verified = Derived.Verified
