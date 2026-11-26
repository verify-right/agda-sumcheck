{-# OPTIONS --safe --without-K #-}
module Ring.Verifier where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _==_)
open import Agda.Builtin.List using (List; []; _∷_)

both : Bool → Bool → Bool
both true b = b
both false b = false

countRounds : {A : Set} → List A → Nat
countRounds [] = 0
countRounds (_ ∷ xs) = 1 + countRounds xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto [] acc = acc
reverseOnto (x ∷ xs) acc = reverseOnto xs (x ∷ acc)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

-- Kept separate from proofs so this record is an ordinary Haskell dictionary.
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
verifyWith op eval oracle seen claim [] [] = same op claim (oracle (reverseList seen))
verifyWith op eval oracle seen claim [] (_ ∷ _) = false
verifyWith op eval oracle seen claim (_ ∷ _) [] = false
verifyWith op eval oracle seen claim (MkRound y0 y1 ∷ rounds) (r ∷ challenges) =
  both (same op claim (add op y0 y1))
    (verifyWith op eval oracle (r ∷ seen) (eval y0 y1 r) rounds challenges)

verify : {F : Set} → Operations F → (List F → F) → Nat → F → List (Round F) → List F → Bool
verify op oracle n claim rounds challenges =
  both (n == countRounds rounds) (verifyWith op (interpolate op) oracle [] claim rounds challenges)
