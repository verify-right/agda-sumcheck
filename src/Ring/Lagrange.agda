{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)

-- Lagrange interpolation on m = d + 1 nodes over a commutative ring, in
-- the first barycentric form (DLMF §3.3(i)):
--
--   ℓ_i(r) = ∏_{j ≠ i} (r - x_j)        omitted product
--   L_i(r) = w_i · ℓ_i(r)               Lagrange basis
--   p(r)   = Σ_i y_i · L_i(r)
--
-- The weights w_i are inverses of ℓ_i(x_i). They are supplied with a
-- certificate rather than computed, since a commutative ring need not
-- invert differences of distinct elements. Over a field with distinct
-- nodes such weights always exist. Products over j ≠ i are stdlib's
-- removeAt (composition with Fin.punchIn i).
module Ring.Lagrange {c ℓ} (R : CommutativeRing c ℓ) where

open CommutativeRing R hiding (zero)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
import Data.Fin.Properties as Fin
open import Data.Vec.Functional using (Vector; removeAt)
open import Relation.Nullary.Decidable.Core using (does; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Algebra.Properties.Ring ring using (-‿involutive; -1*x≈-x; -0#≈0#; -‿+-comm)
import Algebra.Properties.CommutativeMonoid.Sum as Sum
import Ring.Interpolation as Interpolation
open import Relation.Binary.Reasoning.Setoid setoid

module Σ = Sum +-commutativeMonoid
module Π = Sum *-commutativeMonoid

------------------------------------------------------------------------
-- Definitions

omitted : {d : ℕ} → Vector Carrier (suc d) → Fin (suc d) → Carrier → Carrier
omitted x i r = Π.sum (removeAt (λ j → r - x j) i)

basis : {d : ℕ} → (x w : Vector Carrier (suc d)) → Fin (suc d) → Carrier → Carrier
basis x w i r = w i * omitted x i r

lagrange : {d : ℕ} → (x w y : Vector Carrier (suc d)) → Carrier → Carrier
lagrange x w y r = Σ.sum (λ i → y i * basis x w i r)

-- Each w_i inverts the denominator ℓ_i(x_i).
Certified : {d : ℕ} → (x w : Vector Carrier (suc d)) → Set ℓ
Certified x w = ∀ i → w i * omitted x i (x i) ≈ 1#

------------------------------------------------------------------------
-- Kronecker node law

-- A product with a zero factor is zero (stdlib sum-remove for _*_).
product-zero : {n : ℕ} (v : Vector Carrier (suc n)) (j : Fin (suc n)) →
  v j ≈ 0# → Π.sum v ≈ 0#
product-zero v j h = trans (Π.sum-remove {i = j} v) (trans (*-congʳ h) (zeroˡ _))

basis-own : {d : ℕ} {x w : Vector Carrier (suc d)} → Certified x w →
  (i : Fin (suc d)) → basis x w i (x i) ≈ 1#
basis-own certified i = certified i

basis-other : {d : ℕ} (x w : Vector Carrier (suc d)) (i k : Fin (suc d)) →
  i ≢ k → basis x w i (x k) ≈ 0#
basis-other {zero} x w zero zero i≢k with () ← i≢k P.refl
basis-other {suc d} x w i k i≢k = trans (*-congˡ (product-zero (removeAt (λ j → x k - x j) i) j factor)) (zeroʳ (w i))
  where
  j = punchOut i≢k
  factor : x k - x (punchIn i j) ≈ 0#
  factor = trans (+-congˡ (-‿cong (reflexive (P.cong x (Fin.punchIn-punchOut i≢k)))))
    (-‿inverseʳ (x k))

kronecker : {d : ℕ} {x w : Vector Carrier (suc d)} → Certified x w →
  (i k : Fin (suc d)) → basis x w i (x k) ≈ (if does (i Fin.≟ k) then 1# else 0#)
kronecker {x = x} {w} certified i k with i Fin.≟ k
... | yes P.refl = basis-own certified i
... | no i≢k = basis-other x w i k i≢k

-- The interpolant takes the received value at every node.
lagrange-node : {d : ℕ} {x w : Vector Carrier (suc d)} → Certified x w →
  (y : Vector Carrier (suc d)) (k : Fin (suc d)) → lagrange x w y (x k) ≈ y k
lagrange-node {d} {x} {w} certified y k = begin
  lagrange x w y (x k)                       ≈⟨ Σ.sum-remove {i = k} term ⟩
  term k + Σ.sum (removeAt term k)           ≈⟨ +-cong own (Σ.sum-cong-≋ {d} others) ⟩
  y k + Σ.sum {d} (λ _ → 0#)                 ≈⟨ +-congˡ (Σ.sum-replicate-zero d) ⟩
  y k + 0#                                   ≈⟨ +-identityʳ (y k) ⟩
  y k ∎
  where
  term = λ i → y i * basis x w i (x k)
  own : term k ≈ y k
  own = trans (*-congˡ (basis-own certified k)) (*-identityʳ (y k))
  others : ∀ j → removeAt term k j ≈ 0#
  others j = trans (*-congˡ (basis-other x w (punchIn k j) k (Fin.punchInᵢ≢i k j)))
    (zeroʳ _)

------------------------------------------------------------------------
-- Setoid congruence in nodes, weights, values and evaluation point

lagrange-cong : {d : ℕ} {x x' w w' y y' : Vector Carrier (suc d)} {r r' : Carrier} →
  (∀ i → x i ≈ x' i) → (∀ i → w i ≈ w' i) → (∀ i → y i ≈ y' i) → r ≈ r' →
  lagrange x w y r ≈ lagrange x' w' y' r'
lagrange-cong xx ww yy rr = Σ.sum-cong-≋ λ i →
  *-cong (yy i) (*-cong (ww i) (Π.sum-cong-≋ λ j → +-cong rr (-‿cong (xx (punchIn i j)))))

------------------------------------------------------------------------
-- Degree 0: one node, constant interpolant

lagrange-constant : {x w : Vector Carrier 1} → Certified x w →
  (y : Vector Carrier 1) (r : Carrier) → lagrange x w y r ≈ y zero
lagrange-constant certified y r =
  trans (+-identityʳ _) (trans (*-congˡ (certified zero)) (*-identityʳ (y zero)))

------------------------------------------------------------------------
-- Degree 1: nodes 0, 1 with weights -1, 1 recover Ring.Interpolation

private
  module I = Interpolation R

nodes01 : Vector Carrier 2
nodes01 zero = 0#
nodes01 (suc zero) = 1#

weights01 : Vector Carrier 2
weights01 zero = - 1#
weights01 (suc zero) = 1#

private
  minus-zero : (a : Carrier) → a - 0# ≈ a
  minus-zero a = trans (+-congˡ -0#≈0#) (+-identityʳ a)

  zero-minus-one : - 1# * (0# - 1#) ≈ 1#
  zero-minus-one = begin
    - 1# * (0# - 1#)   ≈⟨ *-congˡ (+-identityˡ (- 1#)) ⟩
    - 1# * - 1#        ≈⟨ -1*x≈-x (- 1#) ⟩
    - - 1#             ≈⟨ -‿involutive 1# ⟩
    1# ∎

certified01 : Certified nodes01 weights01
certified01 zero = trans (*-congˡ (*-identityʳ _)) zero-minus-one
certified01 (suc zero) = trans (*-identityˡ _) (trans (*-identityʳ _) (minus-zero 1#))

-- The two-node interpolant is the existing two-point formula a + (b - a) r.
lagrange01 : (y : Vector Carrier 2) (r : Carrier) →
  lagrange nodes01 weights01 y r ≈ y zero + (y (suc zero) - y zero) * r
lagrange01 y r = begin
  lagrange nodes01 weights01 y r
    ≈⟨ +-congˡ (+-identityʳ _) ⟩
  a * (- 1# * ((r - 1#) * 1#)) + b * (1# * ((r - 0#) * 1#))
    ≈⟨ +-cong (*-congˡ left) (*-congˡ right) ⟩
  a * (1# - r) + b * r
    ≈⟨ +-cong (*-comm a _) (*-comm b r) ⟩
  (1# - r) * a + r * b
    ≈⟨ sym (I.linear-interpolation a b r) ⟩
  a + (b - a) * r ∎
  where
  a = y zero
  b = y (suc zero)
  left : - 1# * ((r - 1#) * 1#) ≈ 1# - r
  left = begin
    - 1# * ((r - 1#) * 1#)   ≈⟨ *-congˡ (*-identityʳ _) ⟩
    - 1# * (r - 1#)          ≈⟨ -1*x≈-x _ ⟩
    - (r - 1#)               ≈⟨ -‿+-comm r (- 1#) ⟨
    - r + - - 1#             ≈⟨ +-congˡ (-‿involutive 1#) ⟩
    - r + 1#                 ≈⟨ +-comm (- r) 1# ⟩
    1# - r ∎
  right : 1# * ((r - 0#) * 1#) ≈ r
  right = trans (*-identityˡ _) (trans (*-identityʳ _) (minus-zero r))
