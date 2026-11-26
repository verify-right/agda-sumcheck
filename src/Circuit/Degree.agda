{-# OPTIONS --safe --without-K #-}
-- The executable degree check implies the usual structural degree bound.
module Circuit.Degree where

open import Data.Bool.Base using (true)
open import Data.Bool.Properties using (∧-conicalˡ; ∧-conicalʳ; T-≡)
open import Data.Nat.Base using (ℕ; suc; _+_; _≤_; _⊔_; s≤s⁻¹)
import Data.Nat.Properties as ℕ
open import Function.Bundles using (module Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Circuit.Protocol

-- The usual structural degree bound: max for addition, sum for products.
structuralDegree : {F : Set} → Univariate F → ℕ
structuralDegree (Value _) = 0
structuralDegree UVar = 1
structuralDegree (UAdd p q) = structuralDegree p ⊔ structuralDegree q
structuralDegree (UMul p q) = structuralDegree p + structuralDegree q
structuralDegree (UNeg p) = structuralDegree p

messageDegree : {F : Set} → Message F → ℕ
messageDegree (Leaf p) = structuralDegree p
messageDegree (Branch p q) = messageDegree p ⊔ messageDegree q

count-is-conservative : {F : Set} (p : Univariate F) → structuralDegree p ≤ degree p
count-is-conservative (Value _) = ℕ.≤-refl
count-is-conservative UVar = ℕ.≤-refl
count-is-conservative (UAdd p q) = ℕ.⊔-lub
  (ℕ.≤-trans (count-is-conservative p) (ℕ.m≤m+n (degree p) (degree q)))
  (ℕ.≤-trans (count-is-conservative q) (ℕ.m≤n+m (degree q) (degree p)))
count-is-conservative (UMul p q) = ℕ.+-mono-≤ (count-is-conservative p) (count-is-conservative q)
count-is-conservative (UNeg p) = count-is-conservative p

accepted-degree : {F : Set} (d : ℕ) (m : Message F) → degreeOK d m ≡ true → messageDegree m ≤ d
accepted-degree d (Leaf p) h = ℕ.≤-trans (count-is-conservative p)
  (s≤s⁻¹ (ℕ.<ᵇ⇒< (degree p) (suc d) (Equivalence.from T-≡ h)))
accepted-degree d (Branch p q) h = ℕ.⊔-lub
  (accepted-degree d p (∧-conicalˡ _ _ h))
  (accepted-degree d q (∧-conicalʳ _ _ h))
