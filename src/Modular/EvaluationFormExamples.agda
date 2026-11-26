{-# OPTIONS --safe --without-K #-}
module Modular.EvaluationFormExamples where

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ring.Verifier using (MkRound; verify)
open import Modular.Operations using (operations; normalize)
open import Modular.Ring 15 using (commutativeRing; remainder-idem)
import Modular.Correctness as ModuloCorrectness
import Circuit.Protocol as C
import Circuit.EvaluationForm as EvaluationForm

module E = EvaluationForm commutativeRing (ModuloCorrectness._≟_ 15) (normalize 15) remainder-idem

-- z-lean's Example 1 over F₁₇: p(x) = 1 + 2x, round values q(0) = 1,
-- q(1) = 3, claim 4.
oracle : List ℕ → ℕ
oracle [] = 4
oracle (x ∷ []) = normalize 15 (1 + 2 * x)
oracle (_ ∷ _ ∷ _) = 0

honest : verify (operations 15) oracle 1 4 (MkRound 1 3 ∷ []) (2 ∷ []) ≡ true
honest = refl

wrong-claim : verify (operations 15) oracle 1 5 (MkRound 1 3 ∷ []) (2 ∷ []) ≡ false
wrong-claim = refl

missing-challenge : verify (operations 15) oracle 1 4 (MkRound 1 3 ∷ []) [] ≡ false
missing-challenge = refl

extra-challenge : verify (operations 15) oracle 1 4 (MkRound 1 3 ∷ []) (2 ∷ 3 ∷ []) ≡ false
extra-challenge = refl

zero-rounds : verify (operations 15) oracle 0 4 [] [] ≡ true
zero-rounds = refl

node-challenge : verify (operations 15) oracle 1 4 (MkRound 1 3 ∷ []) (1 ∷ []) ≡ true
node-challenge = refl

-- The evaluation-form acceptance transfers to the circuit verifier at
-- degree bound 1, through the general equivalence theorem.
honest-as-circuit : C.verify (operations 15) 0 oracle 1 1 4
  (map E.decode (MkRound 1 3 ∷ [])) (2 ∷ []) ≡ true
honest-as-circuit = E.wire-sound oracle 1 4 (MkRound 1 3 ∷ []) (2 ∷ []) honest

-- Degree zero.
constant-oracle : List ℕ → ℕ
constant-oracle _ = 3

constant-accepted : E.verify0 constant-oracle 1 6 (MkRound 3 3 ∷ []) (8 ∷ []) ≡ true
constant-accepted = refl

nonconstant-rejected : E.verify0 constant-oracle 1 7 (MkRound 3 4 ∷ []) (8 ∷ []) ≡ false
nonconstant-rejected = refl
