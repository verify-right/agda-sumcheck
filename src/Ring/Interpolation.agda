{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
module Ring.Interpolation {c ℓ} (R : CommutativeRing c ℓ) where

open CommutativeRing R
open import Algebra.Properties.Ring ring using (-‿distribˡ-*)
open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup using (x∙yz≈xz∙y; x∙yz≈y∙xz; xy∙z≈xz∙y)
open import Relation.Binary.Reasoning.Setoid setoid

-- Two-point interpolation needs only commutative-ring laws: no division,
-- inverses of field elements, or primality.
linear-interpolation : (a b r : Carrier) →
  a + ((b + - a) * r) ≈ ((1# + - r) * a) + (r * b)
linear-interpolation a b r = begin
  a + ((b + - a) * r)
    ≈⟨ +-congˡ (distribʳ r b (- a)) ⟩
  a + (b * r + (- a) * r)
    ≈⟨ x∙yz≈xz∙y a (b * r) ((- a) * r) ⟩
  (a + (- a) * r) + b * r
    ≈⟨ +-cong (+-congˡ neg-swap) (*-comm b r) ⟩
  (a + (- r) * a) + r * b
    ≈⟨ +-congʳ (+-congʳ (sym (*-identityˡ a))) ⟩
  (1# * a + (- r) * a) + r * b
    ≈⟨ +-congʳ (sym (distribʳ a 1# (- r))) ⟩
  ((1# + - r) * a) + (r * b) ∎
  where
  neg-swap : (- a) * r ≈ (- r) * a
  neg-swap = trans (sym (-‿distribˡ-* a r))
    (trans (-‿cong (*-comm a r)) (-‿distribˡ-* r a))

-- Interpolating the endpoint values of a + bX recovers a + b*r.
linear-reconstruction : (a b r : Carrier) →
  a + (((a + b) + - a) * r) ≈ a + (b * r)
linear-reconstruction a b r = begin
  a + (((a + b) + - a) * r)
    ≈⟨ +-congˡ (*-congʳ (xy∙z≈xz∙y a b (- a))) ⟩
  a + (((a + - a) + b) * r)
    ≈⟨ +-congˡ (*-congʳ (+-congʳ (-‿inverseʳ a))) ⟩
  a + ((0# + b) * r)
    ≈⟨ +-congˡ (*-congʳ (+-identityˡ b)) ⟩
  a + (b * r) ∎

linear-at-zero : (a b : Carrier) → a + ((b + - a) * 0#) ≈ a
linear-at-zero a b = begin
  a + ((b + - a) * 0#) ≈⟨ +-congˡ (zeroʳ (b + - a)) ⟩
  a + 0#                 ≈⟨ +-identityʳ a ⟩
  a ∎

linear-at-one : (a b : Carrier) → a + ((b + - a) * 1#) ≈ b
linear-at-one a b = begin
  a + ((b + - a) * 1#) ≈⟨ +-congˡ (*-identityʳ (b + - a)) ⟩
  a + (b + - a)         ≈⟨ x∙yz≈y∙xz a b (- a) ⟩
  b + (a + - a)         ≈⟨ +-congˡ (-‿inverseʳ a) ⟩
  b + 0#                ≈⟨ +-identityʳ b ⟩
  b ∎
