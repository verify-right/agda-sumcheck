{-# OPTIONS --safe --without-K #-}
-- Pointwise-equivalent final oracles give the same verdict.
module Circuit.Oracle where

open import Data.Bool.Base using (_∧_)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Ring.Verifier using (Operations; one; same)
open import Circuit.Protocol

-- Quest 12's per-query oracle agreement, specialized to the one final query
-- of this transcript verifier; it is not the full stateful composition proof.
module Agreement {F : Set} (op : Operations F) (z : F) (_≈_ : F → F → Set)
  (≈-refl : (a : F) → a ≈ a)
  (same-cong : {a b c d : F} → a ≈ b → c ≈ d → same op a c ≡ same op b d) where

  oracle-cong : (left right : List F → F) → ((point : List F) → left point ≈ right point) →
    (d : ℕ) (prefix : List F) (claim : F) (messages : List (Message F)) (challenges : List F) →
    verifyWith op z left d prefix claim messages challenges ≡
    verifyWith op z right d prefix claim messages challenges
  oracle-cong left right h d prefix claim [] [] = same-cong (≈-refl claim) (h prefix)
  oracle-cong left right h d prefix claim [] (_ ∷ _) = refl
  oracle-cong left right h d prefix claim (_ ∷ _) [] = refl
  oracle-cong left right h d prefix claim (m ∷ ms) (r ∷ rs) =
    cong (λ rest → degreeOK d m ∧
      (same op claim (plus op (evaluateMessage op m z) (evaluateMessage op m (one op))) ∧ rest))
      (oracle-cong left right h d (prefix ∷ʳ r) (evaluateMessage op m r) ms rs)

  verify-oracle-cong : (left right : List F → F) → ((point : List F) → left point ≈ right point) →
    (n d : ℕ) (claim : F) (messages : List (Message F)) (challenges : List F) →
    verify op z left n d claim messages challenges ≡ verify op z right n d claim messages challenges
  verify-oracle-cong left right h n d claim messages challenges =
    cong ((n ≡ᵇ length messages) ∧_) (oracle-cong left right h d [] claim messages challenges)
