{-# OPTIONS --safe --without-K #-}
module Ring.Correctness where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Ring.Verifier
open import Ring.Prelude using (cong; cong₂; sym; trans; and-left; and-right; nat-eq-sound; nat-eq-complete)

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
  agree oracle seen left right left≈right [] [] = same-cong left≈right (≈-refl (oracle (reverseList seen)))
  agree oracle seen left right left≈right [] (_ ∷ _) = refl
  agree oracle seen left right left≈right (_ ∷ _) [] = refl
  agree oracle seen left right left≈right (MkRound y0 y1 ∷ rest) (r ∷ rs) =
    cong₂ both (same-cong left≈right (≈-refl (add op y0 y1)))
      (agree oracle (r ∷ seen) (interpolate op y0 y1 r) (lagrange op y0 y1 r)
        (interpolation-correct y0 y1 r) rest rs)

  data Checks (oracle : List F → F) : List F → F → List (Round F) → List F → Set where
    final : {seen : List F} {claim : F} → claim ≈ oracle (reverseList seen) →
      Checks oracle seen claim [] []
    step : {seen : List F} {claim y0 y1 r : F}
      {rounds : List (Round F)} {challenges : List F} →
      claim ≈ add op y0 y1 →
      Checks oracle (r ∷ seen) (lagrange op y0 y1 r) rounds challenges →
      Checks oracle seen claim (MkRound y0 y1 ∷ rounds) (r ∷ challenges)

  record Accepts (oracle : List F → F) (n : Nat) (claim : F)
    (rounds : List (Round F)) (challenges : List F) : Set where
    constructor accepted
    field
      expected-length : n ≡ countRounds rounds
      checked-rounds : Checks oracle [] claim rounds challenges

  spec-sound : (oracle : List F → F) (seen : List F) (claim : F)
    (rounds : List (Round F)) (challenges : List F) →
    verifyWith op (lagrange op) oracle seen claim rounds challenges ≡ true →
    Checks oracle seen claim rounds challenges
  spec-sound oracle seen claim [] [] h = final (same-sound claim (oracle (reverseList seen)) h)
  spec-sound oracle seen claim [] (_ ∷ _) ()
  spec-sound oracle seen claim (_ ∷ _) [] ()
  spec-sound oracle seen claim (MkRound y0 y1 ∷ rest) (r ∷ rs) h =
    step (same-sound claim (add op y0 y1) (and-left h))
      (spec-sound oracle (r ∷ seen) (lagrange op y0 y1 r) rest rs (and-right h))

  spec-complete : {oracle : List F → F} {seen : List F} {claim : F}
    {rounds : List (Round F)} {challenges : List F} →
    Checks oracle seen claim rounds challenges →
    verifyWith op (lagrange op) oracle seen claim rounds challenges ≡ true
  spec-complete (final h) = same-complete _ _ h
  spec-complete (step h rest) rewrite same-complete _ _ h | spec-complete rest = refl

  verify-sound : (oracle : List F → F) (n : Nat) (claim : F)
    (rounds : List (Round F)) (challenges : List F) →
    verify op oracle n claim rounds challenges ≡ true → Accepts oracle n claim rounds challenges
  verify-sound oracle n claim rounds challenges h = accepted
    (nat-eq-sound n (countRounds rounds) (and-left h))
    (spec-sound oracle [] claim rounds challenges
      (trans (sym (agree oracle [] claim claim (≈-refl claim) rounds challenges)) (and-right h)))

  verify-complete : (oracle : List F → F) (n : Nat) (claim : F)
    (rounds : List (Round F)) (challenges : List F) →
    Accepts oracle n claim rounds challenges → verify op oracle n claim rounds challenges ≡ true
  verify-complete oracle n claim rounds challenges (accepted count checked)
    rewrite nat-eq-complete n (countRounds rounds) count |
      trans (agree oracle [] claim claim (≈-refl claim) rounds challenges) (spec-complete checked) = refl

  -- Quest 12's per-query agreement, specialized to the single final oracle
  -- query. This is not the full stateful free-monad composition theorem.
  oracle-cong : (left right : List F → F) →
    ((point : List F) → left point ≈ right point) →
    (seen : List F) (claim : F) (rounds : List (Round F)) (challenges : List F) →
    verifyWith op (interpolate op) left seen claim rounds challenges ≡
    verifyWith op (interpolate op) right seen claim rounds challenges
  oracle-cong left right pointwise seen claim [] [] =
    same-cong (≈-refl claim) (pointwise (reverseList seen))
  oracle-cong left right pointwise seen claim [] (_ ∷ _) = refl
  oracle-cong left right pointwise seen claim (_ ∷ _) [] = refl
  oracle-cong left right pointwise seen claim (MkRound y0 y1 ∷ rest) (r ∷ rs) =
    cong (both (same op claim (add op y0 y1)))
      (oracle-cong left right pointwise (r ∷ seen) (interpolate op y0 y1 r) rest rs)

  verify-oracle-cong : (left right : List F → F) →
    ((point : List F) → left point ≈ right point) →
    (n : Nat) (claim : F) (rounds : List (Round F)) (challenges : List F) →
    verify op left n claim rounds challenges ≡ verify op right n claim rounds challenges
  verify-oracle-cong left right pointwise n claim rounds challenges =
    cong (both (n == countRounds rounds)) (oracle-cong left right pointwise [] claim rounds challenges)
