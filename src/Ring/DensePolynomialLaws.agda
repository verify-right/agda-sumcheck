{-# OPTIONS --safe --without-K #-}
-- Ported unchanged (module names only) from quest28-hqc/DensePolynomialLaws.agda,
-- identical to quest15.13-piccs-source/quest15-prime/DensePolynomialLaws.agda.
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Ring.DensePolynomialLaws (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Ring.DensePolynomial R public
open import Data.Nat.Base using (ℕ; suc; _≤_)
import Data.Nat.Properties as N
import Algebra.Properties.CommutativeSemigroup as CS
import Algebra.Properties.AbelianGroup as AG
import Algebra.Properties.Ring as RP
module Add = CS +-commutativeSemigroup
module Mul = CS *-commutativeSemigroup
module Group = AG +-abelianGroup
module Ring = RP ring
open import Relation.Binary.Reasoning.Setoid setoid

private
  add-step : (a b c d x : Carrier) → (a + b) + x * (c + d) ≈ (a + x * c) + (b + x * d)
  add-step a b c d x = trans (+-cong refl (distribˡ x c d)) (Add.interchange a b (x * c) (x * d))

  scale-step : (a b c x : Carrier) → (a * b) + x * (a * c) ≈ a * (b + x * c)
  scale-step a b c x = trans (+-cong refl (Mul.x∙yz≈y∙xz x a c)) (sym (distribˡ a b (x * c)))

  neg-step : (a b x : Carrier) → (- a) + x * (- b) ≈ - (a + x * b)
  neg-step a b x = trans (+-cong refl (sym (Ring.-‿distribʳ-* x b))) (Group.⁻¹-∙-comm a (x * b))

  multiply-step : (a b c x : Carrier) → a * c + (0# + x * (b * c)) ≈ (a + x * b) * c
  multiply-step a b c x = trans (+-cong refl (trans (+-identityˡ _) (sym (*-assoc x b c))))
    (sym (distribʳ c a (x * b)))

  cancel : (a b : Carrier) → (a + (- b)) + b ≈ a
  cancel a b = trans (+-assoc a (- b) b) (trans (+-cong refl (-‿inverseˡ b)) (+-identityʳ a))

  restore : (x r : Carrier) → r + (x + (- r)) ≈ x
  restore x r = trans (Add.x∙yz≈y∙xz r x (- r))
    (trans (+-cong refl (-‿inverseʳ r)) (+-identityʳ x))

  division-base : (a b r x : Carrier) → a + x * b ≈ (a + r * b) + (x + (- r)) * b
  division-base a b r x = sym (begin
    (a + r * b) + (x + (- r)) * b ≈⟨ +-assoc a (r * b) _ ⟩
    a + (r * b + (x + (- r)) * b) ≈⟨ +-cong refl (sym (distribʳ b r (x + (- r)))) ⟩
    a + ((r + (x + (- r))) * b) ≈⟨ +-cong refl (*-cong (restore x r) refl) ⟩
    a + x * b ∎)

  division-step : (a b c r x : Carrier) →
    a + x * (b + (x + (- r)) * c) ≈ (a + r * b) + (x + (- r)) * (b + x * c)
  division-step a b c r x = begin
    a + x * (b + (x + (- r)) * c) ≈⟨ +-cong refl (distribˡ x b _) ⟩
    a + (x * b + x * ((x + (- r)) * c)) ≈⟨ sym (+-assoc a (x * b) _) ⟩
    (a + x * b) + x * ((x + (- r)) * c) ≈⟨ +-cong (division-base a b r x) (Mul.x∙yz≈y∙xz x (x + (- r)) c) ⟩
    ((a + r * b) + (x + (- r)) * b) + (x + (- r)) * (x * c) ≈⟨ +-assoc (a + r * b) _ _ ⟩
    (a + r * b) + ((x + (- r)) * b + (x + (- r)) * (x * c)) ≈⟨ +-cong refl (sym (distribˡ (x + (- r)) b (x * c))) ⟩
    (a + r * b) + (x + (- r)) * (b + x * c) ∎

add-eval : ∀ {n} (p q : Poly n) (x : Carrier) → eval (addP p q) x ≈ eval p x + eval q x
add-eval (con a) (con b) x = refl
add-eval (a ▹ p) (b ▹ q) x = trans (+-cong refl (*-cong refl (add-eval p q x)))
  (add-step a b (eval p x) (eval q x) x)

scale-eval : ∀ {n} (a : Carrier) (p : Poly n) (x : Carrier) → eval (scale a p) x ≈ a * eval p x
scale-eval a (con b) x = refl
scale-eval a (b ▹ p) x = trans (+-cong refl (*-cong refl (scale-eval a p x)))
  (scale-step a b (eval p x) x)

neg-eval : ∀ {n} (p : Poly n) (x : Carrier) → eval (negP p) x ≈ - eval p x
neg-eval (con a) x = refl
neg-eval (a ▹ p) x = trans (+-cong refl (*-cong refl (neg-eval p x))) (neg-step a (eval p x) x)

plus-eval : ∀ {m n} (p : Poly m) (q : Poly n) (x : Carrier) → eval (plusP p q) x ≈ eval p x + eval q x
plus-eval {m} {n} p q x = trans (add-eval (pad (N.m≤m⊔n m n) p) (pad (N.m≤n⊔m m n) q) x)
  (+-cong (pad-eval (N.m≤m⊔n m n) p x) (pad-eval (N.m≤n⊔m m n) q x))

mul-eval : ∀ {m n} (p : Poly m) (q : Poly n) (x : Carrier) → eval (mulP p q) x ≈ eval p x * eval q x
mul-eval (con a) q x = scale-eval a q x
mul-eval {suc m} {n} (a ▹ p) q x = trans (add-eval (pad (N.m≤n⇒m≤1+n (N.m≤n+m n m)) (scale a q)) (0# ▹ mulP p q) x)
  (trans (+-cong (trans (pad-eval (N.m≤n⇒m≤1+n (N.m≤n+m n m)) (scale a q) x) (scale-eval a q x))
    (+-cong refl (*-cong refl (mul-eval p q x))))
    (multiply-step a (eval p x) (eval q x) x))

-- Constructive remainder theorem, with a quotient one degree smaller.
division : ∀ {n} (p : Poly (suc n)) (r x : Carrier) →
  eval p x ≈ eval p r + (x + (- r)) * eval (quotient p r) x
division (a ▹ con b) r x = division-base a b r x
division (a ▹ (b ▹ p)) r x = trans (+-cong refl (*-cong refl (division (b ▹ p) r x)))
  (division-step a (eval (b ▹ p) r) (eval (quotient (b ▹ p) r) x) r x)

subtract-zero : (a b : Carrier) → a + (- b) ≈ 0# → a ≈ b
subtract-zero a b h = trans (sym (cancel a b)) (trans (+-cong h refl) (+-identityˡ b))

subtract-equal : (a b : Carrier) → a ≈ b → a + (- b) ≈ 0#
subtract-equal a b h = trans (+-cong h refl) (-‿inverseʳ b)
