{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
module Ring.Interpolation {c ℓ} (R : CommutativeRing c ℓ) where

open CommutativeRing R
open import Algebra.Properties.Ring ring using (-‿distribˡ-*)
open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup using (x∙yz≈xz∙y)
open import Algebra.Properties.AbelianGroup +-abelianGroup using (xyx⁻¹≈y)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Function.Bundles using (Inverse)
open import Relation.Binary.Bundles using (Setoid)
import Function.Consequences.Setoid as Consequences
open import Relation.Binary.Reasoning.Setoid setoid

-- Additive cancellation a + (b - a) ≈ b, from stdlib's abelian-group lemma.
add-neg-cancel : (a b : Carrier) → a + (b + - a) ≈ b
add-neg-cancel a b = trans (sym (+-assoc a b (- a))) (xyx⁻¹≈y a b)

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
linear-reconstruction a b r = +-congˡ (*-congʳ (xyx⁻¹≈y a b))

linear-at-zero : (a b : Carrier) → a + ((b + - a) * 0#) ≈ a
linear-at-zero a b = begin
  a + ((b + - a) * 0#) ≈⟨ +-congˡ (zeroʳ (b + - a)) ⟩
  a + 0#                 ≈⟨ +-identityʳ a ⟩
  a ∎

linear-at-one : (a b : Carrier) → a + ((b + - a) * 1#) ≈ b
linear-at-one a b = trans (+-congˡ (*-identityʳ (b + - a))) (add-neg-cancel a b)

------------------------------------------------------------------------
-- Coefficients and endpoint evaluations of a linear polynomial a + bX
-- are isomorphic: evaluation at 0 and 1 is inverted by interpolation.
-- Both sides carry pointwise setoid equality on pairs.

Pairs = ×-setoid setoid setoid

-- The polynomial a + bX, given by its coefficient pair.
evaluate : Carrier × Carrier → Carrier → Carrier
evaluate (a , b) r = a + b * r

-- Coefficients to values at 0 and 1, up to the ring laws (see endpoints).
toEvaluations : Carrier × Carrier → Carrier × Carrier
toEvaluations (a , b) = a , a + b

-- Values at 0 and 1 to coefficients: constant term y0, slope y1 - y0,
-- as used by interpolation.
fromEvaluations : Carrier × Carrier → Carrier × Carrier
fromEvaluations (y0 , y1) = y0 , y1 + - y0

endpoints : (a b : Carrier) →
  evaluate (a , b) 0# ≈ a × evaluate (a , b) 1# ≈ a + b
endpoints a b = trans (+-congˡ (zeroʳ b)) (+-identityʳ a) , +-congˡ (*-identityʳ b)

-- Interpolating from the recovered coefficients is the interpolation formula.
from-interpolates : (y0 y1 r : Carrier) →
  evaluate (fromEvaluations (y0 , y1)) r ≈ y0 + ((y1 + - y0) * r)
from-interpolates y0 y1 r = refl

coefficient-evaluation : Inverse Pairs Pairs
coefficient-evaluation = record
  { to        = toEvaluations
  ; from      = fromEvaluations
  ; to-cong   = to-cong
  ; from-cong = from-cong
  ; inverse   = C.strictlyInverseˡ⇒inverseˡ to-cong (λ { (y0 , y1) → refl , add-neg-cancel y0 y1 })
              , C.strictlyInverseʳ⇒inverseʳ from-cong (λ { (a , b) → refl , xyx⁻¹≈y a b })
  }
  where
  module C = Consequences Pairs Pairs
  open Setoid Pairs using () renaming (_≈_ to _≋_)

  to-cong : {x y : Carrier × Carrier} → x ≋ y → toEvaluations x ≋ toEvaluations y
  to-cong {a , b} {a' , b'} (a≈ , b≈) = a≈ , +-cong a≈ b≈

  from-cong : {x y : Carrier × Carrier} → x ≋ y → fromEvaluations x ≋ fromEvaluations y
  from-cong {y0 , y1} {y0' , y1'} (y0≈ , y1≈) = y0≈ , +-cong y1≈ (-‿cong y0≈)
