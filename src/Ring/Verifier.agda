{-# OPTIONS --safe --without-K #-}
module Ring.Verifier where

open import Data.Bool.Base using (Bool; false; _∧_)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; length; reverse)

-- Executable dictionary of ring operations. It carries no laws: proofs
-- take them as separate hypotheses (see Ring.Correctness).
record Operations (F : Set) : Set where
  constructor MkOperations
  field
    one : F
    add mul : F → F → F
    neg : F → F
    normalize : F → F
    same : F → F → Bool
open Operations public

data Round (F : Set) : Set where
  MkRound : F → F → Round F

interpolate : {F : Set} → Operations F → F → F → F → F
interpolate op y0 y1 r = normalize op (add op y0 (mul op (add op y1 (neg op y0)) r))

lagrange : {F : Set} → Operations F → F → F → F → F
lagrange op y0 y1 r = normalize op (add op (mul op (add op (one op) (neg op r)) y0) (mul op r y1))

-- Challenges are separate from prover messages and must be independently
-- supplied. The lists must match and the number of rounds must be expected.
verifyWith : {F : Set} → Operations F → (F → F → F → F) → (List F → F) →
  List F → F → List (Round F) → List F → Bool
verifyWith op eval oracle seen claim [] [] = same op claim (oracle (reverse seen))
verifyWith op eval oracle seen claim [] (_ ∷ _) = false
verifyWith op eval oracle seen claim (_ ∷ _) [] = false
verifyWith op eval oracle seen claim (MkRound y0 y1 ∷ rounds) (r ∷ challenges) =
  same op claim (add op y0 y1) ∧
    verifyWith op eval oracle (r ∷ seen) (eval y0 y1 r) rounds challenges

verify : {F : Set} → Operations F → (List F → F) → ℕ → F → List (Round F) → List F → Bool
verify op oracle n claim rounds challenges =
  (n ≡ᵇ length rounds) ∧ verifyWith op (interpolate op) oracle [] claim rounds challenges
