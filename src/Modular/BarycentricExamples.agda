{-# OPTIONS --safe --without-K #-}
module Modular.BarycentricExamples where

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Nullary.Decidable.Core using (does; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Modular.Operations using (operations; normalize)
import Modular.Ring as ModuloRing
import Modular.Correctness as ModuloCorrectness
import Circuit.Protocol as C
import Circuit.Barycentric as Barycentric

module B = Barycentric (ModuloRing.commutativeRing 15) (ModuloCorrectness._≟_ 15)
  (normalize 15) (ModuloRing.remainder-idem 15)

------------------------------------------------------------------------
-- Certified node sets in F₁₇. Weights are inverses of ∏_{j≠i} (x_i - x_j),
-- checked by B.certify?.

quadratic : B.NodeSet 2
quadratic = B.nodeSet (0 ∷ 1 ∷ 2 ∷ []) (9 ∷ 16 ∷ 9 ∷ [])
  (toWitness {a? = B.certify? (0 ∷ 1 ∷ 2 ∷ []) (9 ∷ 16 ∷ 9 ∷ [])} tt)

cubic : B.NodeSet 3
cubic = B.nodeSet (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) (14 ∷ 9 ∷ 8 ∷ 3 ∷ [])
  (toWitness {a? = B.certify? (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) (14 ∷ 9 ∷ 8 ∷ 3 ∷ [])} tt)

-- Invalid configurations are rejected.
wrong-weights : does (B.certify? (0 ∷ 1 ∷ 2 ∷ []) (9 ∷ 1 ∷ 9 ∷ [])) ≡ false
wrong-weights = refl

duplicate-nodes : does (B.certify? (0 ∷ 0 ∷ 2 ∷ []) (9 ∷ 16 ∷ 9 ∷ [])) ≡ false
duplicate-nodes = refl

------------------------------------------------------------------------
-- Scalar evaluation

at-node : B.evaluate quadratic (2 ∷ 4 ∷ 10 ∷ []) 1 ≡ 4
at-node = refl

away-from-nodes : B.evaluate quadratic (2 ∷ 4 ∷ 10 ∷ []) 3 ≡ 3   -- 2·3² + 2 = 20 ≡ 3
away-from-nodes = refl

cubic-eval : B.evaluate cubic (0 ∷ 1 ∷ 8 ∷ 10 ∷ []) 4 ≡ 13         -- x³ at 4 = 64 ≡ 13
cubic-eval = refl

------------------------------------------------------------------------
-- z-lean Example 1: p(x) = 1 + 2x, claim 4, values (1, 3) at 0, 1.

oracle1 : List ℕ → ℕ
oracle1 (x ∷ []) = normalize 15 (1 + 2 * x)
oracle1 _ = 0

example1 : B.verify oracle1 ((1 , B.linearNodes) ∷ []) 4 ((1 ∷ 3 ∷ []) ∷ []) (2 ∷ []) ≡ true
example1 = refl

-- The same polynomial under a degree-2 bound, sent as values at 0, 1, 2.
example1-quadratic : B.verify oracle1 ((2 , quadratic) ∷ []) 4 ((1 ∷ 3 ∷ 5 ∷ []) ∷ []) (2 ∷ []) ≡ true
example1-quadratic = refl

example1-wrong-claim : B.verify oracle1 ((1 , B.linearNodes) ∷ []) 5 ((1 ∷ 3 ∷ []) ∷ []) (2 ∷ []) ≡ false
example1-wrong-claim = refl

------------------------------------------------------------------------
-- z-lean Example 3: p(x,y,z) = x²y + z, claim 6, challenges 2, 3, 5.
-- g₁(X) = 2X² + 2, g₂(Y) = 8Y + 1, g₃(Z) = 12 + Z; p(2,3,5) = 17 ≡ 0.

oracle3 : List ℕ → ℕ
oracle3 (x ∷ y ∷ z ∷ []) = normalize 15 (x * x * y + z)
oracle3 _ = 0

challenges3 : List ℕ
challenges3 = 2 ∷ 3 ∷ 5 ∷ []

-- Mixed per-round degree bounds: 2 for x, 1 for y and z.
mixed : List B.Config
mixed = (2 , quadratic) ∷ (1 , B.linearNodes) ∷ (1 , B.linearNodes) ∷ []

example3-mixed : B.verify oracle3 mixed 6
  ((2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []) challenges3 ≡ true
example3-mixed = refl

-- Uniform degree bound 2.
uniform : List B.Config
uniform = (2 , quadratic) ∷ (2 , quadratic) ∷ (2 , quadratic) ∷ []

messages3 : List (List ℕ)
messages3 = (2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 9 ∷ 0 ∷ []) ∷ (12 ∷ 13 ∷ 14 ∷ []) ∷ []

example3 : B.verify oracle3 uniform 6 messages3 challenges3 ≡ true
example3 = refl

example3-wrong-claim : B.verify oracle3 uniform 7 messages3 challenges3 ≡ false
example3-wrong-claim = refl

-- Noncanonical residues: 19 ≡ 2, 21 ≡ 4, 27 ≡ 10.
example3-noncanonical : B.verify oracle3 uniform 23
  ((19 ∷ 21 ∷ 27 ∷ []) ∷ (1 ∷ 9 ∷ 0 ∷ []) ∷ (12 ∷ 13 ∷ 14 ∷ []) ∷ []) challenges3 ≡ true
example3-noncanonical = refl

-- Challenge at a node (r₁ = 1): g₁(1) = 4, g₂(Y) = 2Y + 1, g₃(Z) = 3 + Z.
example3-node-challenge : B.verify oracle3 uniform 6
  ((2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 3 ∷ 5 ∷ []) ∷ (3 ∷ 4 ∷ 5 ∷ []) ∷ []) (1 ∷ 3 ∷ 5 ∷ []) ≡ true
example3-node-challenge = refl

-- Malformed external lists are rejected at the boundary.
short-tuple : B.verify oracle3 uniform 6
  ((2 ∷ 4 ∷ []) ∷ (1 ∷ 9 ∷ 0 ∷ []) ∷ (12 ∷ 13 ∷ 14 ∷ []) ∷ []) challenges3 ≡ false
short-tuple = refl

long-tuple : B.verify oracle3 mixed 6
  ((2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 9 ∷ 0 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []) challenges3 ≡ false
long-tuple = refl

missing-challenge : B.verify oracle3 uniform 6 messages3 (2 ∷ 3 ∷ []) ≡ false
missing-challenge = refl

extra-message : B.verify oracle3 uniform 6 (messages3 ++ ((0 ∷ 0 ∷ 0 ∷ []) ∷ [])) challenges3 ≡ false
extra-message = refl

zero-rounds : B.verify (λ _ → 6) [] 6 [] [] ≡ true
zero-rounds = refl

-- The representation theorem: the circuit verifier at uniform degree
-- bound 2 accepts the decoded transcript.
example3-as-circuit : C.verify (operations 15) 0 oracle3 3 2 6
  (map (B.decodeList (2 , quadratic)) messages3) challenges3 ≡ true
example3-as-circuit = trans (sym (B.verify-equivalent quadratic oracle3 3 6 messages3 challenges3)) example3

------------------------------------------------------------------------
-- Degree 0: one value per round and a constant interpolant.

constant : List B.Config
constant = (0 , B.constantNodes 0) ∷ []

degree-zero : B.verify (λ _ → 3) constant 6 ((3 ∷ []) ∷ []) (8 ∷ []) ≡ true
degree-zero = refl

degree-zero-wrong-claim : B.verify (λ _ → 3) constant 7 ((3 ∷ []) ∷ []) (8 ∷ []) ≡ false
degree-zero-wrong-claim = refl

degree-zero-two-values : B.verify (λ _ → 3) constant 6 ((3 ∷ 3 ∷ []) ∷ []) (8 ∷ []) ≡ false
degree-zero-two-values = refl

------------------------------------------------------------------------
-- A composite modulus, 15, with unit differences 1 and 2.

module B15 = Barycentric (ModuloRing.commutativeRing 13) (ModuloCorrectness._≟_ 13)
  (normalize 13) (ModuloRing.remainder-idem 13)

quadratic15 : B15.NodeSet 2
quadratic15 = B15.nodeSet (0 ∷ 1 ∷ 2 ∷ []) (8 ∷ 14 ∷ 8 ∷ [])
  (toWitness {a? = B15.certify? (0 ∷ 1 ∷ 2 ∷ []) (8 ∷ 14 ∷ 8 ∷ [])} tt)

-- 2X² + 2 at X = 4 is 34 ≡ 4 modulo 15.
composite-eval : B15.evaluate quadratic15 (2 ∷ 4 ∷ 10 ∷ []) 4 ≡ 4
composite-eval = refl

-- Nodes 0, 3 differ by a non-unit modulo 15: no weight 5 works.
non-unit-difference : does (B15.certify? (0 ∷ 3 ∷ []) (5 ∷ 5 ∷ [])) ≡ false
non-unit-difference = refl
