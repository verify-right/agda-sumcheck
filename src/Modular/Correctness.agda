{-# OPTIONS --safe --without-K #-}
open import Data.Nat.Base using (ℕ)
module Modular.Correctness (k : ℕ) where

open import Data.Bool.Base using (true)
open import Data.Bool.Properties using (T-≡)
open import Data.Nat.Base using (_+_; _*_; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Function.Bundles using (module Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Modular.Operations using (normalize; negative; same; operations)
open import Modular.Ring k using (_≈_; commutativeRing; remainder-idem)
open import Ring.Verifier using (interpolate; lagrange)
import Ring.Correctness as VerifierProof
import Ring.Interpolation as Interpolation

same-sound : (x y : ℕ) → same k x y ≡ true → x ≈ y
same-sound x y h = ≡ᵇ⇒≡ (normalize k x) (normalize k y) (Equivalence.from T-≡ h)

same-complete : (x y : ℕ) → x ≈ y → same k x y ≡ true
same-complete x y h = Equivalence.to T-≡ (≡⇒≡ᵇ (normalize k x) (normalize k y) h)

same-cong : {x x' y y' : ℕ} → x ≈ x' → y ≈ y' → same k x y ≡ same k x' y'
same-cong hx hy = cong₂ _≡ᵇ_ hx hy

-- A reusable proof over any commutative ring; specialized here to the
-- standard-library-backed ring of natural-number representatives modulo p.
ring-interpolation : (a b r : ℕ) →
  (a + ((b + negative k a) * r)) ≈ (((1 + negative k r) * a) + (r * b))
ring-interpolation = Interpolation.linear-interpolation commutativeRing

interpolation-correct : (a b r : ℕ) →
  interpolate (operations k) a b r ≈ lagrange (operations k) a b r
interpolation-correct a b r = cong (normalize k) (ring-interpolation a b r)

-- The optimized interpolator recovers the mathematical linear polynomial
-- from its evaluations at 0 and 1, for every modulus and every a, b, r.
interpolation-of-linear : (a b r : ℕ) →
  interpolate (operations k) a (a + b) r ≈ a + (b * r)
interpolation-of-linear a b r =
  trans (remainder-idem (a + (((a + b) + negative k a) * r)))
    (Interpolation.linear-reconstruction commutativeRing a b r)

-- The evaluation-point cases are total, including challenges 0 and 1.
interpolation-at-zero : (a b : ℕ) → interpolate (operations k) a b 0 ≈ a
interpolation-at-zero a b =
  trans (remainder-idem (a + ((b + negative k a) * 0)))
    (Interpolation.linear-at-zero commutativeRing a b)

interpolation-at-one : (a b : ℕ) → interpolate (operations k) a b 1 ≈ b
interpolation-at-one a b =
  trans (remainder-idem (a + ((b + negative k a) * 1)))
    (Interpolation.linear-at-one commutativeRing a b)

module Verified = VerifierProof.Correctness (operations k) _≈_ (λ _ → refl)
  same-sound same-complete (λ {x} {x'} {y} {y'} hx hy → same-cong {x} {x'} {y} {y'} hx hy)
  interpolation-correct
