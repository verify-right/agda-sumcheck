{-# OPTIONS --safe --without-K #-}
module Ring.Correctness where

open import Data.Bool.Base using (true; _∧_)
open import Data.Bool.Properties using (∧-conicalˡ; ∧-conicalʳ; T-≡)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.List.Base using (List; []; _∷_; length; reverse)
open import Function.Bundles using (module Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Ring.Verifier

-- All hypotheses are explicit and discharged by the modular instance.
module Correctness {F : Set} (op : Operations F) (_≈_ : F → F → Set)
  (≈-refl : (x : F) → x ≈ x)
  (same-sound : (x y : F) → same op x y ≡ true → x ≈ y)
  (same-complete : (x y : F) → x ≈ y → same op x y ≡ true)
  (same-cong : {x x' y y' : F} → x ≈ x' → y ≈ y' → same op x y ≡ same op x' y')
  (interpolation-correct : (a b r : F) → interpolate op a b r ≈ lagrange op a b r)
  where

  agree : (oracle : List F → F) (seen : List F) (left right : F) →
    left ≈ right → (rounds : List (Round F)) (challenges : List F) →
    verifyWith op (interpolate op) oracle seen left rounds challenges ≡
    verifyWith op (lagrange op) oracle seen right rounds challenges
  agree oracle seen left right left≈right [] [] = same-cong left≈right (≈-refl (oracle (reverse seen)))
  agree oracle seen left right left≈right [] (_ ∷ _) = refl
  agree oracle seen left right left≈right (_ ∷ _) [] = refl
  agree oracle seen left right left≈right (MkRound y0 y1 ∷ rest) (r ∷ rs) =
    cong₂ _∧_ (same-cong left≈right (≈-refl (add op y0 y1)))
      (agree oracle (r ∷ seen) (interpolate op y0 y1 r) (lagrange op y0 y1 r)
        (interpolation-correct y0 y1 r) rest rs)

  data Checks (oracle : List F → F) : List F → F → List (Round F) → List F → Set where
    final : {seen : List F} {claim : F} → claim ≈ oracle (reverse seen) →
      Checks oracle seen claim [] []
    step : {seen : List F} {claim y0 y1 r : F}
      {rounds : List (Round F)} {challenges : List F} →
      claim ≈ add op y0 y1 →
      Checks oracle (r ∷ seen) (lagrange op y0 y1 r) rounds challenges →
      Checks oracle seen claim (MkRound y0 y1 ∷ rounds) (r ∷ challenges)

  record Accepts (oracle : List F → F) (n : ℕ) (claim : F)
    (rounds : List (Round F)) (challenges : List F) : Set where
    constructor accepted
    field
      expected-length : n ≡ length rounds
      checked-rounds : Checks oracle [] claim rounds challenges

  spec-sound : (oracle : List F → F) (seen : List F) (claim : F)
    (rounds : List (Round F)) (challenges : List F) →
    verifyWith op (lagrange op) oracle seen claim rounds challenges ≡ true →
    Checks oracle seen claim rounds challenges
  spec-sound oracle seen claim [] [] h = final (same-sound claim (oracle (reverse seen)) h)
  spec-sound oracle seen claim [] (_ ∷ _) ()
  spec-sound oracle seen claim (_ ∷ _) [] ()
  spec-sound oracle seen claim (MkRound y0 y1 ∷ rest) (r ∷ rs) h =
    step (same-sound claim (add op y0 y1) (∧-conicalˡ _ _ h))
      (spec-sound oracle (r ∷ seen) (lagrange op y0 y1 r) rest rs (∧-conicalʳ _ _ h))

  spec-complete : {oracle : List F → F} {seen : List F} {claim : F}
    {rounds : List (Round F)} {challenges : List F} →
    Checks oracle seen claim rounds challenges →
    verifyWith op (lagrange op) oracle seen claim rounds challenges ≡ true
  spec-complete (final h) = same-complete _ _ h
  spec-complete (step h rest) = cong₂ _∧_ (same-complete _ _ h) (spec-complete rest)

  verify-sound : (oracle : List F → F) (n : ℕ) (claim : F)
    (rounds : List (Round F)) (challenges : List F) →
    verify op oracle n claim rounds challenges ≡ true → Accepts oracle n claim rounds challenges
  verify-sound oracle n claim rounds challenges h = accepted
    (≡ᵇ⇒≡ n (length rounds) (Equivalence.from T-≡ (∧-conicalˡ _ _ h)))
    (spec-sound oracle [] claim rounds challenges
      (trans (sym (agree oracle [] claim claim (≈-refl claim) rounds challenges)) (∧-conicalʳ _ _ h)))

  verify-complete : (oracle : List F → F) (n : ℕ) (claim : F)
    (rounds : List (Round F)) (challenges : List F) →
    Accepts oracle n claim rounds challenges → verify op oracle n claim rounds challenges ≡ true
  verify-complete oracle n claim rounds challenges (accepted count checked) = cong₂ _∧_
    (Equivalence.to T-≡ (≡⇒≡ᵇ n (length rounds) count))
    (trans (agree oracle [] claim claim (≈-refl claim) rounds challenges) (spec-complete checked))

  -- Quest 12's per-query agreement, specialized to the single final oracle
  -- query. This is not the full stateful free-monad composition theorem.
  oracle-cong : (left right : List F → F) →
    ((point : List F) → left point ≈ right point) →
    (seen : List F) (claim : F) (rounds : List (Round F)) (challenges : List F) →
    verifyWith op (interpolate op) left seen claim rounds challenges ≡
    verifyWith op (interpolate op) right seen claim rounds challenges
  oracle-cong left right pointwise seen claim [] [] =
    same-cong (≈-refl claim) (pointwise (reverse seen))
  oracle-cong left right pointwise seen claim [] (_ ∷ _) = refl
  oracle-cong left right pointwise seen claim (_ ∷ _) [] = refl
  oracle-cong left right pointwise seen claim (MkRound y0 y1 ∷ rest) (r ∷ rs) =
    cong (same op claim (add op y0 y1) ∧_)
      (oracle-cong left right pointwise (r ∷ seen) (interpolate op y0 y1 r) rest rs)

  verify-oracle-cong : (left right : List F → F) →
    ((point : List F) → left point ≈ right point) →
    (n : ℕ) (claim : F) (rounds : List (Round F)) (challenges : List F) →
    verify op left n claim rounds challenges ≡ verify op right n claim rounds challenges
  verify-oracle-cong left right pointwise n claim rounds challenges =
    cong ((n ≡ᵇ length rounds) ∧_) (oracle-cong left right pointwise [] claim rounds challenges)
