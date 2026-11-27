{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- Converse representation theorem: every circuit message that passes the
-- degree check at d is reproduced, at every point, by barycentric
-- evaluation of its values at any certified node set of size d + 1.
--
-- Proof: the message normalizes to coefficients of bound d
-- (Circuit.Normalization); the Lagrange interpolant of its node values has
-- the same node values, hence the same coefficients (Ring.LagrangeInverse).
-- Equality of functions on a finite ring alone would not suffice.
module Circuit.Reconstruction (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_; zero)
open import Data.Bool.Base using (true; _∧_)
open import Data.Nat.Base using (ℕ; suc; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; map; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-length)
open import Data.Maybe.Base using (Maybe; just)
import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate; toList)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)
open import Ring.Verifier using (same)
import Ring.Verifier as Wire
import Ring.FromRing as FromRing
import Ring.Lagrange as Lagrange
import Ring.LagrangeInverse as LagrangeInverse
open import Ring.DensePolynomialLaws R using (eval)
import Circuit.Protocol as C
import Circuit.Normalization as Normalization
import Circuit.Barycentric as Barycentric
import Circuit.EvaluationForm as EvaluationForm
open import Relation.Binary.Reasoning.Setoid setoid

private
  module D = FromRing R _≟_ normalize normalize-≈
  module L = Lagrange R
  module LI = LagrangeInverse R
  module N = Normalization R _≟_ normalize normalize-≈
  module B = Barycentric R _≟_ normalize normalize-≈
  module EF = EvaluationForm R _≟_ normalize normalize-≈
  op = D.operations

  nf-cong : {a b : Carrier} → a ≈ b → normalize a ≈ normalize b
  nf-cong {a} {b} h = trans (normalize-≈ a) (trans h (sym (normalize-≈ b)))

------------------------------------------------------------------------
-- Encoding a circuit message by its node values

encode : {d : ℕ} → B.NodeSet d → C.Message Carrier → Vec Carrier (suc d)
encode ns m = tabulate (λ i → C.evaluateMessage op m (lookup (B.nodes ns) i))

reconstruction : {d : ℕ} (ns : B.NodeSet d) (m : C.Message Carrier) → C.degreeOK d m ≡ true →
  (r : Carrier) → B.evaluate ns (encode ns m) r ≈ C.evaluateMessage op m r
reconstruction {d} ns m h r = begin
  B.evaluate ns (encode ns m) r       ≈⟨ B.evalAt-correct (B.nodes ns) (B.weights ns) (encode ns m) r ⟩
  L.lagrange x w y r                  ≈⟨ LI.interpolant-eval x w y r ⟨
  eval (LI.interpolant x w y) r       ≈⟨ LI.eval-cong same-coefficients r ⟩
  eval P r                            ≈⟨ N.checked-correct d m h r ⟨
  C.evaluateMessage op m r ∎
  where
  x = lookup (B.nodes ns)
  w = lookup (B.weights ns)
  y = lookup (encode ns m)
  P = N.checkedPolynomial d m h
  same-coefficients : LI.interpolant x w y LI.≋ P
  same-coefficients = LI.eval-injective (LI.unit-differences {x = x} {w} (B.certified ns))
    (LI.interpolant x w y) P λ i →
      trans (LI.interpolant-eval x w y (x i))
        (trans (L.lagrange-node (B.certified ns) y i)
          (trans (reflexive (lookup∘tabulate (λ j → C.evaluateMessage op m (x j)) i))
            (N.checked-correct d m h (x i))))

------------------------------------------------------------------------
-- The circuit verifier respects messages with equal degree verdicts and
-- equivalent evaluations (a simulation lemma for Circuit.Protocol).

Related : ℕ → C.Message Carrier → C.Message Carrier → Set
Related d m m' = (C.degreeOK d m ≡ C.degreeOK d m') × (∀ r → C.evaluateMessage op m r ≈ C.evaluateMessage op m' r)

messages-cong : (oracle : List Carrier → Carrier) (d : ℕ) (prefix : List Carrier) {x y : Carrier} →
  x ≈ y → {ms ms' : List (C.Message Carrier)} → Pointwise (Related d) ms ms' → (rs : List Carrier) →
  C.verifyWith op 0# oracle d prefix x ms rs ≡ C.verifyWith op 0# oracle d prefix y ms' rs
messages-cong oracle d prefix xy [] [] = D.same-cong xy refl
messages-cong oracle d prefix xy [] (_ ∷ _) = P.refl
messages-cong oracle d prefix xy (_ ∷ _) [] = P.refl
messages-cong oracle d prefix xy {m ∷ ms} {m' ∷ ms'} ((deg , ev) ∷ rel) (r ∷ rs) =
  cong₂ _∧_ deg (cong₂ _∧_ (D.same-cong xy (nf-cong (+-cong (ev 0#) (ev 1#))))
    (messages-cong oracle d (prefix ∷ʳ r) (ev r) rel rs))

verify-messages-cong : (oracle : List Carrier → Carrier) (n d : ℕ) (claim : Carrier)
  {ms ms' : List (C.Message Carrier)} → Pointwise (Related d) ms ms' → (rs : List Carrier) →
  C.verify op 0# oracle n d claim ms rs ≡ C.verify op 0# oracle n d claim ms' rs
verify-messages-cong oracle n d claim rel rs = cong₂ _∧_
  (cong (n ≡ᵇ_) (Pointwise-length rel)) (messages-cong oracle d [] refl rel rs)

------------------------------------------------------------------------
-- Encoding-direction transcript equivalence, for arbitrary circuit messages
-- passing the degree check (no Linear or other certificate).

encodeList : {d : ℕ} → B.NodeSet d → C.Message Carrier → List Carrier
encodeList ns m = toList (encode ns m)

-- Parsing a tuple's own list returns the tuple.
exactly-toList : {A : Set} {n : ℕ} (v : Vec A n) → B.exactly n (toList v) ≡ just v
exactly-toList [] = P.refl
exactly-toList (a ∷ v) = cong (Maybe.map (a ∷_)) (exactly-toList v)

decoded-related : {d : ℕ} (ns : B.NodeSet d) (m : C.Message Carrier) → C.degreeOK d m ≡ true →
  Related d (B.decodeList (d , ns) (encodeList ns m)) m
decoded-related {d} ns m h = P.subst (λ t → Related d (B.decodeTuple ns t) m)
  (P.sym (exactly-toList (encode ns m)))
  (P.trans (B.decode-degree ns (encode ns m)) (P.sym h) ,
   λ r → trans (sym (B.decode-evaluate ns (encode ns m) r)) (reconstruction ns m h r))

encode-verify-equivalent : {d : ℕ} (ns : B.NodeSet d) (oracle : List Carrier → Carrier)
  (n : ℕ) (claim : Carrier) (ms : List (C.Message Carrier)) (rs : List Carrier) →
  All (λ m → C.degreeOK d m ≡ true) ms →
  B.verify oracle (replicate n (d , ns)) claim (map (encodeList ns) ms) rs ≡
  C.verify op 0# oracle n d claim ms rs
encode-verify-equivalent {d} ns oracle n claim ms rs checked =
  P.trans (B.verify-equivalent ns oracle n claim (map (encodeList ns) ms) rs)
    (verify-messages-cong oracle n d claim (related ms checked) rs)
  where
  related : (ms : List (C.Message Carrier)) → All (λ m → C.degreeOK d m ≡ true) ms →
    Pointwise (Related d) (map (B.decodeList (d , ns)) (map (encodeList ns) ms)) ms
  related [] [] = []
  related (m ∷ ms) (h ∷ hs) = decoded-related ns m h ∷ related ms hs

------------------------------------------------------------------------
-- Degree one: every message passing degreeOK 1 carries the Linear
-- certificate of Circuit.EvaluationForm.

linear-certificate : (m : C.Message Carrier) → C.degreeOK 1 m ≡ true → EF.Linear m
linear-certificate m h = record
  { degree-one = h
  ; reconstruct = λ r → trans (sym (B.evaluate-linear _ _ r)) (reconstruction B.linearNodes m h r)
  }

-- Hence the degree-one encoding theorem needs only the degree check.
linear-verify-equivalent : (oracle : List Carrier → Carrier) (n : ℕ) (claim : Carrier)
  (ms : List (C.Message Carrier)) (rs : List Carrier) → All (λ m → C.degreeOK 1 m ≡ true) ms →
  Wire.verify op oracle n claim (map EF.encode ms) rs ≡ C.verify op 0# oracle n 1 claim ms rs
linear-verify-equivalent oracle n claim ms rs checked =
  EF.verify-equivalent oracle n claim ms rs (certificates ms checked)
  where
  certificates : (ms : List (C.Message Carrier)) → All (λ m → C.degreeOK 1 m ≡ true) ms → All EF.Linear ms
  certificates [] [] = []
  certificates (m ∷ ms) (h ∷ hs) = linear-certificate m h ∷ certificates ms hs
