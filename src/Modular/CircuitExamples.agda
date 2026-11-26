{-# OPTIONS --safe --without-K #-}
module Modular.CircuitExamples where

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Modular.Operations using (operations)
open import Circuit.Protocol
import Modular.Correctness as ModuloCorrectness
open import Modular.Ring 15 using (modulus-shift)

-- f(x,y) = 1 + x³ + 2y² + xy. The Boolean-cube sum is 11.
X Y : Polynomial ℕ
X = Var 0
Y = Var 1

cubic : Polynomial ℕ
cubic = AddP (AddP (AddP (Const 1) (MulP X (MulP X X)))
  (MulP (Const 2) (MulP Y Y))) (MulP X Y)

challenges : List ℕ
challenges = 2 ∷ 3 ∷ []

f5-sum : cube (operations 3) 0 cubic [] challenges ≡ 1
f5-sum = refl

f17-sum : cube (operations 15) 0 cubic [] challenges ≡ 11
f17-sum = refl

f5-final : evaluate (operations 3) 0 cubic challenges ≡ 3
f5-final = refl

f17-final : evaluate (operations 15) 0 cubic challenges ≡ 16
f17-final = refl

f5-example : verify (operations 3) 0 (evaluate (operations 3) 0 cubic) 2 (bound cubic) 1
  (honest (operations 3) 0 cubic [] challenges) challenges ≡ true
f5-example = refl

f17-example : verify (operations 15) 0 (evaluate (operations 15) 0 cubic) 2 (bound cubic) 11
  (honest (operations 15) 0 cubic [] challenges) challenges ≡ true
f17-example = refl

bad-claim : verify (operations 15) 0 (evaluate (operations 15) 0 cubic) 2 (bound cubic) 12
  (honest (operations 15) 0 cubic [] challenges) challenges ≡ false
bad-claim = refl

too-small-degree : verify (operations 15) 0 (evaluate (operations 15) 0 cubic) 2 2 11
  (honest (operations 15) 0 cubic [] challenges) challenges ≡ false
too-small-degree = refl

missing-challenge : verify (operations 15) 0 (evaluate (operations 15) 0 cubic) 2 (bound cubic) 11
  (honest (operations 15) 0 cubic [] challenges) (2 ∷ []) ≡ false
missing-challenge = refl

module F17 = ModuloCorrectness 15

-- The universal honest-prover theorem specialized to F₁₇, for every
-- challenge list, rather than one computed transcript.
f17-complete : (rs : List ℕ) →
  verify (operations 15) 0 (evaluate (operations 15) 0 cubic) (length rs) (bound cubic)
    (cube (operations 15) 0 cubic [] rs) (honest (operations 15) 0 cubic [] rs) rs ≡ true
f17-complete rs = F17.Honest.honest-complete cubic (bound cubic) ≤-refl
  sum rs (F17.same-complete sum sum refl)
  where sum = cube (operations 15) 0 cubic [] rs

oracle17 : List ℕ → ℕ
oracle17 = evaluate (operations 15) 0 cubic

shiftedOracle17 : List ℕ → ℕ
shiftedOracle17 point = 17 + oracle17 point

f17-oracle-agreement : (n d claim : ℕ) (ms : List (Message ℕ)) (rs : List ℕ) →
  verify (operations 15) 0 oracle17 n d claim ms rs ≡
  verify (operations 15) 0 shiftedOracle17 n d claim ms rs
f17-oracle-agreement n d claim ms rs = F17.CircuitAgreement.verify-oracle-cong
  oracle17 shiftedOracle17 (λ point → modulus-shift (oracle17 point)) n d claim ms rs
