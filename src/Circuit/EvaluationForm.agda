{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- Evaluation form of sumcheck messages. A round message of degree at most
-- one is sent as its values at 0 and 1 (Ring.Verifier). This module proves
-- that the evaluation-form verifier agrees with the circuit verifier
-- (Circuit.Protocol) at degree bound 1, for arbitrary transcripts, and
-- likewise for a degree-0 evaluation-form verifier at bound 0.
module Circuit.EvaluationForm (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; map; length; reverse)
open import Data.List.Properties using (length-map; unfold-reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (_,_; proj₁; proj₂; uncurry)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)
open import Ring.Verifier using (Round; MkRound; interpolate; same; add)
import Ring.Verifier as Wire
import Ring.Interpolation as Interpolation
import Ring.FromRing as FromRing
import Circuit.Protocol as C

private
  module I = Interpolation R
  module D = FromRing R _≟_ normalize normalize-≈

open D public using (operations)

private
  nf-cong : {a b : Carrier} → a ≈ b → normalize a ≈ normalize b
  nf-cong {a} {b} h = trans (normalize-≈ a) (trans h (sym (normalize-≈ b)))

  same-cong : {a b c d : Carrier} → a ≈ b → c ≈ d → same operations a c ≡ same operations b d
  same-cong {a} {b} {c} {d} = D.same-cong {a} {b} {c} {d}

interpolate-cong : {a b c d : Carrier} → a ≈ c → b ≈ d → (r : Carrier) →
  interpolate operations a b r ≈ interpolate operations c d r
interpolate-cong ac bd r = nf-cong (+-cong ac (*-cong (+-cong bd (-‿cong ac)) refl))

------------------------------------------------------------------------
-- Affine messages: the circuit a + X·b, evaluating to I.evaluate (a , b)

affine : Carrier → Carrier → C.Message Carrier
affine a b = C.Leaf (C.UAdd (C.Value a) (C.UMul C.UVar (C.Value b)))

affine-eval : (a b r : Carrier) →
  C.evaluateMessage operations (affine a b) r ≈ I.evaluate (a , b) r
affine-eval a b r = trans (normalize-≈ _) (+-cong refl (trans (normalize-≈ _) (*-comm r b)))

affine-zero : (a b : Carrier) → C.evaluateMessage operations (affine a b) 0# ≈ a
affine-zero a b = trans (affine-eval a b 0#) (proj₁ (I.endpoints a b))

affine-one : (a b : Carrier) → C.evaluateMessage operations (affine a b) 1# ≈ a + b
affine-one a b = trans (affine-eval a b 1#) (proj₂ (I.endpoints a b))

-- A semantic certificate that a circuit message has degree at most one:
-- it passes the degree check and interpolation from its values at 0 and 1
-- reproduces it. This is not an honesty assumption.
record Linear (m : C.Message Carrier) : Set where
  field
    degree-one : C.degreeOK 1 m ≡ true
    reconstruct : (r : Carrier) →
      interpolate operations (C.evaluateMessage operations m 0#)
        (C.evaluateMessage operations m 1#) r ≈ C.evaluateMessage operations m r
open Linear public

affine-linear : (a b : Carrier) → Linear (affine a b)
affine-linear a b = record { degree-one = P.refl ; reconstruct = λ r →
  trans (interpolate-cong (affine-zero a b) (affine-one a b) r)
    (trans (D.interpolation-of-linear a b r) (sym (affine-eval a b r))) }

------------------------------------------------------------------------
-- Encoding certified-linear circuit messages as evaluation pairs

encode : C.Message Carrier → Round Carrier
encode m = MkRound (C.evaluateMessage operations m 0#) (C.evaluateMessage operations m 1#)

-- The evaluation-form verifier keeps challenges reversed (seen); the
-- circuit verifier keeps them in order (prefix). They are related by reverse.
private
  next-prefix : (seen : List Carrier) {prefix : List Carrier} (r : Carrier) →
    reverse seen ≡ prefix → reverse (r ∷ seen) ≡ prefix ∷ʳ r
  next-prefix seen r h = P.trans (unfold-reverse r seen) (cong (_∷ʳ r) h)

run-equivalent : (oracle : List Carrier → Carrier) (seen prefix : List Carrier) →
  reverse seen ≡ prefix → (x y : Carrier) → x ≈ y →
  (ms : List (C.Message Carrier)) (rs : List Carrier) → All Linear ms →
  Wire.verifyWith operations (interpolate operations) oracle seen x (map encode ms) rs ≡
  C.verifyWith operations 0# oracle 1 prefix y ms rs
run-equivalent oracle seen prefix h x y xy [] [] [] = same-cong xy (reflexive (cong oracle h))
run-equivalent oracle seen prefix h x y xy [] (_ ∷ _) [] = P.refl
run-equivalent oracle seen prefix h x y xy (m ∷ ms) [] (good ∷ goods) = P.refl
run-equivalent oracle seen prefix h x y xy (m ∷ ms) (r ∷ rs) (good ∷ goods) =
  P.trans
    (cong₂ _∧_ (same-cong xy (sym (normalize-≈ _)))
      (run-equivalent oracle (r ∷ seen) (prefix ∷ʳ r) (next-prefix seen r h) _ _
        (reconstruct good r) ms rs goods))
    (cong (_∧ rest) (P.sym (degree-one good)))
  where
  rest = same operations y (C.plus operations (C.evaluateMessage operations m 0#)
      (C.evaluateMessage operations m 1#)) ∧
    C.verifyWith operations 0# oracle 1 (prefix ∷ʳ r) (C.evaluateMessage operations m r) ms rs

verify-equivalent : (oracle : List Carrier → Carrier) (n : ℕ) (claim : Carrier)
  (ms : List (C.Message Carrier)) (rs : List Carrier) → All Linear ms →
  Wire.verify operations oracle n claim (map encode ms) rs ≡
  C.verify operations 0# oracle n 1 claim ms rs
verify-equivalent oracle n claim ms rs goods = cong₂ _∧_
  (cong (n ≡ᵇ_) (length-map encode ms))
  (run-equivalent oracle [] [] P.refl claim claim refl ms rs goods)

------------------------------------------------------------------------
-- Decoding arbitrary evaluation pairs: every wire transcript, including
-- one chosen by an adversary, is accepted exactly when its decoding is
-- accepted by the circuit verifier at degree bound 1.

-- Specification-side map, never called by the wire verifier. The
-- coefficients are Ring.Interpolation's inverse of endpoint evaluation.
decode : Round Carrier → C.Message Carrier
decode (MkRound y₀ y₁) = uncurry affine (I.fromEvaluations (y₀ , y₁))

decode-zero : (a b : Carrier) → C.evaluateMessage operations (decode (MkRound a b)) 0# ≈ a
decode-zero a b = affine-zero a (b + - a)

decode-one : (a b : Carrier) → C.evaluateMessage operations (decode (MkRound a b)) 1# ≈ b
decode-one a b = trans (affine-one a (b + - a)) (I.add-neg-cancel a b)

private
  decode-sum : (a b : Carrier) → add operations a b ≈
    C.plus operations (C.evaluateMessage operations (decode (MkRound a b)) 0#)
      (C.evaluateMessage operations (decode (MkRound a b)) 1#)
  decode-sum a b = sym (trans (normalize-≈ _) (+-cong (decode-zero a b) (decode-one a b)))

wire-run-equivalent : (oracle : List Carrier → Carrier) (seen prefix : List Carrier) →
  reverse seen ≡ prefix → (x y : Carrier) → x ≈ y →
  (ms : List (Round Carrier)) (rs : List Carrier) →
  Wire.verifyWith operations (interpolate operations) oracle seen x ms rs ≡
  C.verifyWith operations 0# oracle 1 prefix y (map decode ms) rs
wire-run-equivalent oracle seen prefix h x y xy [] [] = same-cong xy (reflexive (cong oracle h))
wire-run-equivalent oracle seen prefix h x y xy [] (_ ∷ _) = P.refl
wire-run-equivalent oracle seen prefix h x y xy (_ ∷ _) [] = P.refl
wire-run-equivalent oracle seen prefix h x y xy (MkRound a b ∷ ms) (r ∷ rs) =
  cong₂ _∧_ (same-cong xy (decode-sum a b))
    (wire-run-equivalent oracle (r ∷ seen) (prefix ∷ʳ r) (next-prefix seen r h) _ _
      (trans (interpolate-cong (sym (decode-zero a b)) (sym (decode-one a b)) r)
        (reconstruct (affine-linear a (b + - a)) r)) ms rs)

wire-verify-equivalent : (oracle : List Carrier → Carrier) (n : ℕ) (claim : Carrier)
  (ms : List (Round Carrier)) (rs : List Carrier) →
  Wire.verify operations oracle n claim ms rs ≡
  C.verify operations 0# oracle n 1 claim (map decode ms) rs
wire-verify-equivalent oracle n claim ms rs = cong₂ _∧_
  (cong (n ≡ᵇ_) (P.sym (length-map decode ms)))
  (wire-run-equivalent oracle [] [] P.refl claim claim refl ms rs)

-- Acceptance transfers in both directions, without assuming an honest prover.
wire-complete : (oracle : List Carrier → Carrier) (n : ℕ) (claim : Carrier)
  (ms : List (Round Carrier)) (rs : List Carrier) →
  C.verify operations 0# oracle n 1 claim (map decode ms) rs ≡ true →
  Wire.verify operations oracle n claim ms rs ≡ true
wire-complete oracle n claim ms rs = P.trans (wire-verify-equivalent oracle n claim ms rs)

wire-sound : (oracle : List Carrier → Carrier) (n : ℕ) (claim : Carrier)
  (ms : List (Round Carrier)) (rs : List Carrier) →
  Wire.verify operations oracle n claim ms rs ≡ true →
  C.verify operations 0# oracle n 1 claim (map decode ms) rs ≡ true
wire-sound oracle n claim ms rs = P.trans (P.sym (wire-verify-equivalent oracle n claim ms rs))

-- The interactive round check agrees as well.
wire-round-equivalent : (claim a b : Carrier) →
  same operations claim (add operations a b) ≡
  C.checkRound operations 0# 1 claim (decode (MkRound a b))
wire-round-equivalent claim a b = same-cong refl (decode-sum a b)

------------------------------------------------------------------------
-- Degree zero: a constant round message must have equal values at 0 and 1.

run0 : (List Carrier → Carrier) → List Carrier → Carrier → List (Round Carrier) → List Carrier → Bool
run0 oracle prefix claim [] [] = same operations claim (oracle prefix)
run0 oracle prefix claim [] (_ ∷ _) = false
run0 oracle prefix claim (_ ∷ _) [] = false
run0 oracle prefix claim (MkRound a b ∷ ms) (r ∷ rs) =
  same operations a b ∧ (same operations claim (C.plus operations a b) ∧
    run0 oracle (prefix ∷ʳ r) (interpolate operations a b r) ms rs)

verify0 : (List Carrier → Carrier) → ℕ → Carrier → List (Round Carrier) → List Carrier → Bool
verify0 oracle n claim ms rs = (n ≡ᵇ length ms) ∧ run0 oracle [] claim ms rs

decode0 : Round Carrier → C.Message Carrier
decode0 (MkRound a b) = C.Leaf (C.Value a)

Constant : Round Carrier → Set
Constant (MkRound a b) = a ≈ b

constant-interpolation : (a r : Carrier) → interpolate operations a a r ≈ a
constant-interpolation a r = trans (normalize-≈ _)
  (trans (+-cong refl (*-cong (-‿inverseʳ a) refl))
    (trans (+-cong refl (zeroˡ r)) (+-identityʳ a)))

constant-run-equivalent : (oracle : List Carrier → Carrier) (prefix : List Carrier) (x y : Carrier) →
  x ≈ y → (ms : List (Round Carrier)) (rs : List Carrier) → All Constant ms →
  run0 oracle prefix x ms rs ≡ C.verifyWith operations 0# oracle 0 prefix y (map decode0 ms) rs
constant-run-equivalent oracle prefix x y xy [] [] [] = same-cong xy refl
constant-run-equivalent oracle prefix x y xy [] (_ ∷ _) [] = P.refl
constant-run-equivalent oracle prefix x y xy (_ ∷ _) [] (_ ∷ _) = P.refl
constant-run-equivalent oracle prefix x y xy (MkRound a b ∷ ms) (r ∷ rs) (ab ∷ goods) =
  P.trans (cong (_∧ rest) (D.same-complete a b ab)) (cong₂ _∧_
    (same-cong xy (nf-cong (+-cong refl (sym ab))))
    (constant-run-equivalent oracle (prefix ∷ʳ r) _ _
      (trans (interpolate-cong refl (sym ab) r) (constant-interpolation a r)) ms rs goods))
  where
  rest = same operations x (C.plus operations a b) ∧
    run0 oracle (prefix ∷ʳ r) (interpolate operations a b r) ms rs

constant-verify-equivalent : (oracle : List Carrier → Carrier) (n : ℕ) (claim : Carrier)
  (ms : List (Round Carrier)) (rs : List Carrier) → All Constant ms →
  verify0 oracle n claim ms rs ≡ C.verify operations 0# oracle n 0 claim (map decode0 ms) rs
constant-verify-equivalent oracle n claim ms rs goods = cong₂ _∧_
  (cong (n ≡ᵇ_) (P.sym (length-map decode0 ms)))
  (constant-run-equivalent oracle [] claim claim refl ms rs goods)

constant-invalid-rejected : (oracle : List Carrier → Carrier) (prefix : List Carrier)
  (claim a b r : Carrier) (ms : List (Round Carrier)) (rs : List Carrier) →
  same operations a b ≡ false → run0 oracle prefix claim (MkRound a b ∷ ms) (r ∷ rs) ≡ false
constant-invalid-rejected oracle prefix claim a b r ms rs h = cong (_∧ rest) h
  where
  rest = same operations claim (C.plus operations a b) ∧
    run0 oracle (prefix ∷ʳ r) (interpolate operations a b r) ms rs
