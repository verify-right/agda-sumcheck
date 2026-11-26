{-# OPTIONS --safe --without-K #-}
module Modular.CertifiedExamples where

open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥)
open import Function.Bundles using (module Equivalence)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import Ring.Verifier using (verify)
open import Modular.Operations using (operations)
import Modular.Ring as ModuloRing
open import Modular.Examples
import Modular.Correctness as ModuloCorrectness

module F5 = ModuloCorrectness 3
module F17 = ModuloCorrectness 15
module Mod4 = ModuloCorrectness 2

-- These values instantiate the universal acceptance theorem, rather than
-- only computing the Bool in Examples.
f5-certified : F5.Verified.Accepts oracle 2 1 f5-rounds (2 ∷ 3 ∷ [])
f5-certified = F5.Verified.verify-sound oracle 2 1 f5-rounds (2 ∷ 3 ∷ []) f5-honest

f17-certified : F17.Verified.Accepts oracle 2 11 f17-rounds (2 ∷ 3 ∷ [])
f17-certified = F17.Verified.verify-sound oracle 2 11 f17-rounds (2 ∷ 3 ∷ []) f17-honest

-- Completeness of the executable check excludes an accepting specification
-- derivation for this wrong claim.
f17-wrong-not-accepted : F17.Verified.Accepts oracle 2 12 f17-rounds (2 ∷ 3 ∷ []) → ⊥
-- T false is ⊥, so T-≡ turns false ≡ true into a contradiction.
f17-wrong-not-accepted h = Equivalence.from T-≡ (trans (sym f17-wrong-claim)
  (F17.Verified.verify-complete oracle 2 12 f17-rounds (2 ∷ 3 ∷ []) h))

-- The same polynomial oracle may return another representative of its result.
shiftedOracle : List ℕ → ℕ
shiftedOracle point = 17 + oracle point

module R17 = ModuloRing 15

f17-oracle-transport :
  verify (operations 15) oracle 2 11 f17-rounds (2 ∷ 3 ∷ []) ≡
  verify (operations 15) shiftedOracle 2 11 f17-rounds (2 ∷ 3 ∷ [])
f17-oracle-transport = F17.Verified.verify-oracle-cong oracle shiftedOracle
  (λ point → R17.modulus-shift (oracle point)) 2 11 f17-rounds (2 ∷ 3 ∷ [])
