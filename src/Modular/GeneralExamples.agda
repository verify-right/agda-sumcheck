{-# OPTIONS --safe --without-K #-}
module Modular.GeneralExamples where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_)
import Data.Nat.Properties as ℕ
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Modular.Operations using (operations; normalize; modulus)
import Modular.Ring as ModuloRing
import Modular.Correctness as ModuloCorrectness
import Ring.DensePolynomial as DensePolynomial
import Ring.LagrangeInverse as LagrangeInverse
import Circuit.Protocol as C
import Circuit.Degree as Degree
import Circuit.Barycentric as Barycentric
import Circuit.Reconstruction as Reconstruction
import Circuit.General as General
import Circuit.GeneralCompleteness as GeneralCompleteness
open import Modular.BarycentricExamples using (quadratic; cubic; quadratic15)

-- F₁₇ (k = 15) and ℤ/15 (k = 13).
module F17 where
  ring = ModuloRing.commutativeRing 15
  module B = Barycentric ring (ModuloCorrectness._≟_ 15) (normalize 15) (ModuloRing.remainder-idem 15)
  module Rc = Reconstruction ring (ModuloCorrectness._≟_ 15) (normalize 15) (ModuloRing.remainder-idem 15)
  module G = General ring (ModuloCorrectness._≟_ 15) (normalize 15) (ModuloRing.remainder-idem 15)
  module GC = GeneralCompleteness ring (ModuloCorrectness._≟_ 15) (normalize 15) (ModuloRing.remainder-idem 15)
  module LI = LagrangeInverse ring
  open DensePolynomial ring public using (Poly; con; _▹_; eval)

module Z15 where
  ring = ModuloRing.commutativeRing 13
  module B = Barycentric ring (ModuloCorrectness._≟_ 13) (normalize 13) (ModuloRing.remainder-idem 13)
  module GC = GeneralCompleteness ring (ModuloCorrectness._≟_ 13) (normalize 13) (ModuloRing.remainder-idem 13)
  module LI = LagrangeInverse ring
  open DensePolynomial ring public using (Poly; con; _▹_; eval)

-- Inverses by explicit finite search over the residues 0 … p - 1. Only
-- for small examples; setup validates every result with certify?.
invMod : ℕ → ℕ → ℕ
invMod k a = search (modulus k)
  where
  search : ℕ → ℕ
  search zero = 0
  search (suc b) = if normalize k (a * b) ≡ᵇ 1 then b else search b

coefficients : {n : ℕ} → (k : ℕ) → DensePolynomial.Poly (ModuloRing.commutativeRing k) n → List ℕ
coefficients k (DensePolynomial.con a) = normalize k a ∷ []
coefficients k (a DensePolynomial.▹ p) = normalize k a ∷ coefficients k p

------------------------------------------------------------------------
-- Stage 1: coefficients → evaluations → coefficients

module RoundTrip where
  open F17

  x = lookup (B.nodes quadratic)
  w = lookup (B.weights quadratic)

  p : Poly 2                         -- 1 + 2X + 3X²
  p = 1 ▹ 2 ▹ con 3

  f17 : coefficients 15 (LI.interpolant x w (λ i → eval p (x i))) ≡ 1 ∷ 2 ∷ 3 ∷ []
  f17 = refl

  noncanonical : coefficients 15 (LI.interpolant x w (λ i → eval (18 ▹ 19 ▹ con 20) (x i))) ≡ 1 ∷ 2 ∷ 3 ∷ []
  noncanonical = refl

  -- The universal inverse law, instantiated.
  universal : LI.interpolate {x = x} {w} (B.certified quadratic) (LI.evaluations {x = x} {w} (B.certified quadratic) p) LI.≋ p
  universal = LI.interpolate-evaluate {x = x} {w} (B.certified quadratic) p

  degree0 : coefficients 15 (LI.interpolant (lookup (B.nodes (B.constantNodes 7)))
    (lookup (B.weights (B.constantNodes 7))) (λ i → eval (con 5) (lookup (B.nodes (B.constantNodes 7)) i))) ≡ 5 ∷ []
  degree0 = refl

  degree1 : coefficients 15 (LI.interpolant (lookup (B.nodes B.linearNodes)) (lookup (B.weights B.linearNodes))
    (λ i → eval (4 ▹ con 9) (lookup (B.nodes B.linearNodes) i))) ≡ 4 ∷ 9 ∷ []
  degree1 = refl

  degree3 : coefficients 15 (LI.interpolant (lookup (B.nodes cubic)) (lookup (B.weights cubic))
    (λ i → eval (1 ▹ 0 ▹ 5 ▹ con 16) (lookup (B.nodes cubic) i))) ≡ 1 ∷ 0 ∷ 5 ∷ 16 ∷ []
  degree3 = refl

module RoundTrip15 where
  open Z15

  composite : coefficients 13 (LI.interpolant (lookup (B.nodes quadratic15)) (lookup (B.weights quadratic15))
    (λ i → eval (4 ▹ 7 ▹ con 11) (lookup (B.nodes quadratic15) i))) ≡ 4 ∷ 7 ∷ 11 ∷ []
  composite = refl

------------------------------------------------------------------------
-- Public setup

module Setup where
  open F17

  quadratic-weights : Maybe.map B.weights (GC.setup (invMod 15) (0 ∷ 1 ∷ 2 ∷ [])) ≡ just (9 ∷ 16 ∷ 9 ∷ [])
  quadratic-weights = refl

  shifted-weights : Maybe.map B.weights (GC.setup (invMod 15) (3 ∷ 5 ∷ 7 ∷ [])) ≡ just (15 ∷ 4 ∷ 15 ∷ [])
  shifted-weights = refl

  duplicate-nodes : GC.setup (invMod 15) (0 ∷ 0 ∷ 2 ∷ []) ≡ nothing
  duplicate-nodes = refl

  non-unit : Z15.GC.setup (invMod 13) (0 ∷ 3 ∷ []) ≡ nothing
  non-unit = refl

  composite-units : Maybe.map Z15.B.weights (Z15.GC.setup (invMod 13) (0 ∷ 1 ∷ 2 ∷ [])) ≡ just (8 ∷ 14 ∷ 8 ∷ [])
  composite-units = refl

open F17

-- Node sets used below. Weights computed by setup and certified by certify?.
shifted : B.NodeSet 2
shifted = B.nodeSet (3 ∷ 5 ∷ 7 ∷ []) (GC.weightsFor (invMod 15) (3 ∷ 5 ∷ 7 ∷ []))
  (toWitness {a? = B.certify? (3 ∷ 5 ∷ 7 ∷ []) (GC.weightsFor (invMod 15) (3 ∷ 5 ∷ 7 ∷ []))} tt)

quartic : B.NodeSet 4
quartic = B.nodeSet (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (GC.weightsFor (invMod 15) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
  (toWitness {a? = B.certify? (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (GC.weightsFor (invMod 15) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []))} tt)

------------------------------------------------------------------------
-- Stage 2: reconstruction, with honest degree-check semantics

module Circuits where
  open C

  -- X² - X² + X: degree 1, but four occurrences of X in the first leaf.
  cancelling : Message ℕ
  cancelling = Branch (Leaf (UAdd (UMul UVar UVar) (UNeg (UMul UVar UVar)))) (Leaf UVar)

  cancelling-rejected-at-1 : degreeOK 1 cancelling ≡ false
  cancelling-rejected-at-1 = refl

  cancelling-accepted-at-4 : degreeOK 4 cancelling ≡ true
  cancelling-accepted-at-4 = refl

  cancelling-reconstructed : B.evaluate quartic (Rc.encode quartic cancelling) 7 ≡ 7
  cancelling-reconstructed = refl

  cancelling-universal : (r : ℕ) →
    ModuloRing._≈_ 15 (B.evaluate quartic (Rc.encode quartic cancelling) r) (evaluateMessage (operations 15) cancelling r)
  cancelling-universal = Rc.reconstruction quartic cancelling refl

  -- X + X: structural degree 1, occurrence count 2.
  twice : Message ℕ
  twice = Leaf (UAdd UVar UVar)

  twice-structural : Degree.messageDegree twice ≡ 1
  twice-structural = refl

  twice-rejected-at-1 : degreeOK 1 twice ≡ false
  twice-rejected-at-1 = refl

------------------------------------------------------------------------
-- Stage 3 and 4: z-lean Example 3, p = x²y + z over domain [0, 1]

module Example3 where
  open C using (Polynomial; Var; AddP; MulP; evaluate)

  p : Polynomial ℕ
  p = AddP (MulP (MulP (Var 0) (Var 0)) (Var 1)) (Var 2)

  f : List ℕ → ℕ
  f = evaluate (operations 15) 0 p

  dom = G.boolean
  configs : List B.Config
  configs = (2 , quadratic) ∷ (1 , B.linearNodes) ∷ (1 , B.linearNodes) ∷ []

  messages : List (List ℕ)
  messages = (2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []

  challenges : List ℕ
  challenges = 2 ∷ 3 ∷ 5 ∷ []

  -- Successive claims 6, 10, 8, 0.
  claim1 : B.evaluate quadratic (2 ∷ 4 ∷ 10 ∷ []) 2 ≡ 10
  claim1 = refl
  claim2 : B.evaluate B.linearNodes (1 ∷ 9 ∷ []) 3 ≡ 8
  claim2 = refl
  claim3 : B.evaluate B.linearNodes (12 ∷ 13 ∷ []) 5 ≡ 0
  claim3 = refl

  -- The honest prover computes exactly these tuples.
  honest-messages : GC.honestTuples dom p 0 [] configs challenges ≡ messages
  honest-messages = refl

  full-run : G.evVerify dom (G.residual dom f 0) configs 6 messages challenges ≡ true
  full-run = refl

  -- Partial runs: stop after k rounds with n - k = 3 - k unbound variables.
  stop0 : G.evVerify dom (G.residual dom f 3) [] 6 [] [] ≡ true
  stop0 = refl

  stop1 : G.evVerify dom (G.residual dom f 2) ((2 , quadratic) ∷ []) 6 ((2 ∷ 4 ∷ 10 ∷ []) ∷ []) (2 ∷ []) ≡ true
  stop1 = refl

  residual2 : G.residual dom f 1 (2 ∷ 3 ∷ []) ≡ 8      -- 12 + 13 = 25 ≡ 8
  residual2 = refl

  stop2 : G.evVerify dom (G.residual dom f 1) ((2 , quadratic) ∷ (1 , B.linearNodes) ∷ []) 6
    ((2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ []) (2 ∷ 3 ∷ []) ≡ true
  stop2 = refl

  wrong-claim : G.evVerify dom (G.residual dom f 0) configs 7 messages challenges ≡ false
  wrong-claim = refl

  symbolic : G.symVerify dom (G.residual dom f 0) (2 ∷ 1 ∷ 1 ∷ []) 6 (GC.honest dom p [] challenges 0) challenges ≡ true
  symbolic = refl

  -- Universal completeness with the public bounds (2, 1, 1), instantiated.
  bounded : GC.Bounded p 0 (2 ∷ 1 ∷ 1 ∷ [])
  bounded = ℕ.≤-refl GC.∷ (ℕ.≤-refl GC.∷ (ℕ.≤-refl GC.∷ GC.[]))

  complete : G.evVerify dom (G.residual dom f 0) configs (G.residual dom f 3 [])
    (GC.honestTuples dom p 0 [] configs challenges) challenges ≡ true
  complete = GC.evaluation-form-complete dom p 0 configs bounded challenges refl

  -- Malformed input: a short tuple, a missing round, an extra round.
  short-tuple : G.evVerify dom (G.residual dom f 0) configs 6
    ((2 ∷ 4 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []) challenges ≡ false
  short-tuple = refl

  missing-round : G.evVerify dom (G.residual dom f 0) configs 6
    ((2 ∷ 4 ∷ 10 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ []) challenges ≡ false
  missing-round = refl

  extra-round : G.evVerify dom (G.residual dom f 0) configs 6
    (messages Data.List.Base.++ ((0 ∷ []) ∷ [])) challenges ≡ false
  extra-round = refl

  -- The general rejection theorem, instantiated for every claim and
  -- challenge list.
  short-tuple-rejected : (claim : ℕ) (rs : List ℕ) → G.evVerify dom (G.residual dom f 0) configs claim
    ((2 ∷ 4 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []) rs ≡ false
  short-tuple-rejected claim = G.malformed-rejected dom (G.residual dom f 0) [] claim configs
    ((2 ∷ 4 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []) refl

------------------------------------------------------------------------
-- Domains and node sets

module Domains where
  open C using (Polynomial; Var; Const; AddP; MulP; evaluate)

  square : Polynomial ℕ                  -- x²
  square = MulP (Var 0) (Var 0)

  affine : Polynomial ℕ                  -- 1 + 2x
  affine = AddP (Const 1) (MulP (Const 2) (Var 0))

  -- Domain [0, 1, 2]: 0 + 1 + 4 = 5; final x² at 3 is 9.
  three-points : G.evVerify (0 ∷ 1 ∷ 2 ∷ []) (G.residual (0 ∷ 1 ∷ 2 ∷ []) (evaluate (operations 15) 0 square) 0)
    ((2 , quadratic) ∷ []) 5 ((0 ∷ 1 ∷ 4 ∷ []) ∷ []) (3 ∷ []) ≡ true
  three-points = refl

  -- Domain entries 5, 6 are not interpolation nodes: 11 + 13 = 24 ≡ 7.
  off-nodes : G.evVerify (5 ∷ 6 ∷ []) (G.residual (5 ∷ 6 ∷ []) (evaluate (operations 15) 0 affine) 0)
    ((1 , B.linearNodes) ∷ []) 7 ((1 ∷ 3 ∷ []) ∷ []) (2 ∷ []) ≡ true
  off-nodes = refl

  -- Repeated entries are summed with multiplicity: 3 + 3 + 1 = 7.
  repeated : G.evVerify (1 ∷ 1 ∷ 0 ∷ []) (G.residual (1 ∷ 1 ∷ 0 ∷ []) (evaluate (operations 15) 0 affine) 0)
    ((1 , B.linearNodes) ∷ []) 7 ((1 ∷ 3 ∷ []) ∷ []) (2 ∷ []) ≡ true
  repeated = refl

  -- Empty domain: the round sum is 0.
  empty : G.evVerify [] (λ point → evaluate (operations 15) 0 affine point)
    ((1 , B.linearNodes) ∷ []) 0 ((1 ∷ 3 ∷ []) ∷ []) (2 ∷ []) ≡ true
  empty = refl

  -- Degree 0 on three summation points, node 7 outside the domain: 3·3 = 9.
  constant : G.evVerify (0 ∷ 1 ∷ 2 ∷ []) (λ _ → 3) ((0 , B.constantNodes 7) ∷ []) 9 ((3 ∷ []) ∷ []) (4 ∷ []) ≡ true
  constant = refl

  constant-two-values : G.evVerify (0 ∷ 1 ∷ 2 ∷ []) (λ _ → 3) ((0 , B.constantNodes 7) ∷ []) 9
    ((3 ∷ 3 ∷ []) ∷ []) (4 ∷ []) ≡ false
  constant-two-values = refl

------------------------------------------------------------------------
-- Different node sets of the same degree, and variable order:
-- p(x, y) = x² + 2y, claim 6, challenges 4, 6, final p(4, 6) = 28 ≡ 11.

module Order where
  open C using (Polynomial; Var; Const; AddP; MulP; evaluate)

  p q : Polynomial ℕ
  p = AddP (MulP (Var 0) (Var 0)) (MulP (Const 2) (Var 1))
  q = AddP (MulP (Var 1) (Var 1)) (MulP (Const 2) (Var 0))     -- y² + 2x

  configs : List B.Config
  configs = (2 , quadratic) ∷ (2 , shifted) ∷ []

  oracle = G.residual G.boolean (evaluate (operations 15) 0 p) 0

  honest-tuples : GC.honestTuples G.boolean p 0 [] configs (4 ∷ 6 ∷ []) ≡ (2 ∷ 4 ∷ 10 ∷ []) ∷ (5 ∷ 9 ∷ 13 ∷ []) ∷ []
  honest-tuples = refl

  accepted : G.evVerify G.boolean oracle configs 6 ((2 ∷ 4 ∷ 10 ∷ []) ∷ (5 ∷ 9 ∷ 13 ∷ []) ∷ []) (4 ∷ 6 ∷ []) ≡ true
  accepted = refl

  -- The transposed polynomial has the same sum and passes both round
  -- checks, but its final claim 10 differs from p(4, 6) = 11.
  transposed-rejected : G.evVerify G.boolean oracle configs 6
    (GC.honestTuples G.boolean q 0 [] configs (4 ∷ 6 ∷ [])) (4 ∷ 6 ∷ []) ≡ false
  transposed-rejected = refl
