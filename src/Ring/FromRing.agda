{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- An executable verifier dictionary and its correctness proofs, derived from
-- a commutative ring, decidable equality and a certified normalization
-- (any map that stays in the same equivalence class, e.g. reduction mod p).
module Ring.FromRing (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_)
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Ring.Verifier using (Operations; MkOperations; interpolate; lagrange)
import Ring.Correctness as VerifierProof
import Ring.Interpolation as Interpolation

private
  module I = Interpolation R

operations : Operations Carrier
operations = MkOperations 1# _+_ _*_ -_ normalize (λ x y → does (x ≟ y))

same-sound : (x y : Carrier) → does (x ≟ y) ≡ true → x ≈ y
same-sound x y h with x ≟ y
same-sound x y h  | yes x≈y = x≈y
same-sound x y () | no _

same-complete : (x y : Carrier) → x ≈ y → does (x ≟ y) ≡ true
same-complete x y x≈y with x ≟ y
... | yes _ = ≡-refl
... | no x≉y = ⊥-elim (x≉y x≈y)

same-cong : {x x' y y' : Carrier} → x ≈ x' → y ≈ y' → does (x ≟ y) ≡ does (x' ≟ y')
same-cong {x} {x'} {y} {y'} hx hy with x ≟ y | x' ≟ y'
... | yes _   | yes _    = ≡-refl
... | no _    | no _     = ≡-refl
... | yes x≈y | no x'≉y' = ⊥-elim (x'≉y' (trans (sym hx) (trans x≈y hy)))
... | no x≉y  | yes x'≈y' = ⊥-elim (x≉y (trans hx (trans x'≈y' (sym hy))))

interpolation-correct : (a b r : Carrier) →
  interpolate operations a b r ≈ lagrange operations a b r
interpolation-correct a b r =
  trans (normalize-≈ _) (trans (I.linear-interpolation a b r) (sym (normalize-≈ _)))

-- The optimized interpolator recovers the linear polynomial a + bX from its
-- evaluations at 0 and 1, for every a, b and r.
interpolation-of-linear : (a b r : Carrier) →
  interpolate operations a (a + b) r ≈ a + (b * r)
interpolation-of-linear a b r = trans (normalize-≈ _) (I.linear-reconstruction a b r)

interpolation-at-zero : (a b : Carrier) → interpolate operations a b 0# ≈ a
interpolation-at-zero a b = trans (normalize-≈ _) (I.linear-at-zero a b)

interpolation-at-one : (a b : Carrier) → interpolate operations a b 1# ≈ b
interpolation-at-one a b = trans (normalize-≈ _) (I.linear-at-one a b)

module Verified = VerifierProof.Correctness operations _≈_ (λ _ → refl)
  same-sound same-complete (λ {x} {x'} {y} {y'} → same-cong {x} {x'} {y} {y'})
  interpolation-correct
