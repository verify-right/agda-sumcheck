{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- Coefficient interpretation of round circuits. Generalized from
-- quest15.13 CircuitNormalization.agda (stated there for arithmetic modulo
-- p) to any ring with a certified normalization.
--
-- The coefficient vector's length follows the structural degree of
-- Circuit.Degree (max for addition, sum for multiplication). The executable
-- check degreeOK counts variable occurrences; accepted-degree shows it
-- implies the structural bound, so accepted messages fit d + 1 coefficients.
-- Neither bound is the exact degree: cancellation can make it smaller.
module Circuit.Normalization (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_)
open import Data.Bool.Base using (true)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Ring.DensePolynomialLaws R
import Ring.FromRing as FromRing
open import Circuit.Protocol
open import Circuit.Degree using (structuralDegree; messageDegree; accepted-degree)

private
  module D = FromRing R _≟_ normalize normalize-≈
  op = D.operations

normalizeU : (c : Univariate Carrier) → Poly (structuralDegree c)
normalizeU (Value a) = con a
normalizeU UVar = 0# ▹ con 1#
normalizeU (UAdd a b) = plusP (normalizeU a) (normalizeU b)
normalizeU (UMul a b) = mulP (normalizeU a) (normalizeU b)
normalizeU (UNeg a) = negP (normalizeU a)

normalizeMessage : (m : Message Carrier) → Poly (messageDegree m)
normalizeMessage (Leaf a) = normalizeU a
normalizeMessage (Branch a b) = plusP (normalizeMessage a) (normalizeMessage b)

univariate-correct : (c : Univariate Carrier) (r : Carrier) →
  evaluateU op c r ≈ eval (normalizeU c) r
univariate-correct (Value a) r = refl
univariate-correct UVar r = sym (trans (+-identityˡ _) (*-identityʳ r))
univariate-correct (UAdd a b) r = trans (normalize-≈ _)
  (trans (+-cong (univariate-correct a r) (univariate-correct b r))
    (sym (plus-eval (normalizeU a) (normalizeU b) r)))
univariate-correct (UMul a b) r = trans (normalize-≈ _)
  (trans (*-cong (univariate-correct a r) (univariate-correct b r))
    (sym (mul-eval (normalizeU a) (normalizeU b) r)))
univariate-correct (UNeg a) r = trans (normalize-≈ _)
  (trans (-‿cong (univariate-correct a r)) (sym (neg-eval (normalizeU a) r)))

message-correct : (m : Message Carrier) (r : Carrier) →
  evaluateMessage op m r ≈ eval (normalizeMessage m) r
message-correct (Leaf a) r = univariate-correct a r
message-correct (Branch a b) r = trans (normalize-≈ _)
  (trans (+-cong (message-correct a r) (message-correct b r))
    (sym (plus-eval (normalizeMessage a) (normalizeMessage b) r)))

-- An accepted message fits d + 1 coefficients; padding keeps its values.
checkedPolynomial : (d : ℕ) (m : Message Carrier) → degreeOK d m ≡ true → Poly d
checkedPolynomial d m h = pad (accepted-degree d m h) (normalizeMessage m)

checked-correct : (d : ℕ) (m : Message Carrier) (h : degreeOK d m ≡ true) (r : Carrier) →
  evaluateMessage op m r ≈ eval (checkedPolynomial d m h) r
checked-correct d m h r = trans (message-correct m r)
  (sym (pad-eval (accepted-degree d m h) (normalizeMessage m) r))
