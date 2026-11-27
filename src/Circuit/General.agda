{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- Generalized replay verifiers, matching the interface of z-lean's symbolic
-- verifier (Verifier.lean at d6202f1f): one public degree bound per round,
-- an arbitrary summation domain list (order and multiplicity kept), and a
-- terminal oracle supplied by the caller. Partial runs stop after k ≤ n
-- rounds; their terminal oracle is the residual sum over the n - k unbound
-- variables, with that number given explicitly.
--
-- Interpolation nodes (per-round NodeSet) are separate from the domain.
module Circuit.General (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_; zero)
open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-assoc; ∧-zeroʳ; ∧-commutativeMonoid)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; _++_; [_]; map; length; replicate; concat; concatMap; foldr)
open import Data.List.Properties using (map-++; map-∘; ++-assoc; ++-identityʳ)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; toList)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)
open import Algebra.Properties.CommutativeSemigroup
  (CommutativeMonoid.commutativeSemigroup ∧-commutativeMonoid) using (x∙yz≈y∙xz)
open import Ring.Verifier using (same)
import Ring.FromRing as FromRing
import Circuit.Protocol as C
import Circuit.Barycentric as Barycentric
import Circuit.Reconstruction as Reconstruction
open import Relation.Binary.Reasoning.Setoid setoid

private
  module D = FromRing R _≟_ normalize normalize-≈
  module B = Barycentric R _≟_ normalize normalize-≈
  module Rc = Reconstruction R _≟_ normalize normalize-≈
  op = D.operations

  plus : Carrier → Carrier → Carrier
  plus = C.plus op

  nf-cong : {a b : Carrier} → a ≈ b → normalize a ≈ normalize b
  nf-cong {a} {b} h = trans (normalize-≈ a) (trans h (sym (normalize-≈ b)))

  same-cong : {a b c d : Carrier} → a ≈ b → c ≈ d → same op a c ≡ same op b d
  same-cong {a} {b} {c} {d} = D.same-cong {a} {b} {c} {d}

  true-left : {t : Bool} (z : Bool) → t ≡ true → z ≡ t ∧ z
  true-left z P.refl = P.refl

Message = C.Message Carrier

------------------------------------------------------------------------
-- Sums over the domain list

domainSum : List Carrier → (Carrier → Carrier) → Carrier
domainSum [] f = 0#
domainSum (a ∷ as) f = plus (f a) (domainSum as f)

domainSum-cong : (dom : List Carrier) {f g : Carrier → Carrier} →
  (∀ a → f a ≈ g a) → domainSum dom f ≈ domainSum dom g
domainSum-cong [] h = refl
domainSum-cong (a ∷ as) h = nf-cong (+-cong (h a) (domainSum-cong as h))

------------------------------------------------------------------------
-- Symbolic verifier with one public bound per round

checkSym : List Carrier → ℕ → Carrier → Message → Bool
checkSym dom d claim m = C.degreeOK d m ∧ same op claim (domainSum dom (C.evaluateMessage op m))

symRun : List Carrier → (List Carrier → Carrier) → List Carrier → Carrier →
  List ℕ → List Message → List Carrier → Bool
symRun dom oracle prefix claim [] [] [] = same op claim (oracle prefix)
symRun dom oracle prefix claim [] [] (_ ∷ _) = false
symRun dom oracle prefix claim [] (_ ∷ _) _ = false
symRun dom oracle prefix claim (_ ∷ _) [] _ = false
symRun dom oracle prefix claim (_ ∷ _) (_ ∷ _) [] = false
symRun dom oracle prefix claim (d ∷ ds) (m ∷ ms) (r ∷ rs) =
  checkSym dom d claim m ∧ symRun dom oracle (prefix ∷ʳ r) (C.nextClaim op m r) ds ms rs

-- The number of rounds is the number of bounds.
symVerify : List Carrier → (List Carrier → Carrier) → List ℕ → Carrier →
  List Message → List Carrier → Bool
symVerify dom oracle bounds claim ms rs = symRun dom oracle [] claim bounds ms rs

------------------------------------------------------------------------
-- Evaluation-form verifier with one public node set per round

mutual
  evRun : List Carrier → (List Carrier → Carrier) → List Carrier → Carrier →
    List B.Config → List (List Carrier) → List Carrier → Bool
  evRun dom oracle prefix claim [] [] [] = same op claim (oracle prefix)
  evRun dom oracle prefix claim [] [] (_ ∷ _) = false
  evRun dom oracle prefix claim [] (_ ∷ _) _ = false
  evRun dom oracle prefix claim (_ ∷ _) [] _ = false
  evRun dom oracle prefix claim (_ ∷ _) (_ ∷ _) [] = false
  evRun dom oracle prefix claim ((d , ns) ∷ cs) (m ∷ ms) (r ∷ rs) =
    evTuple dom oracle prefix claim ns (B.exactly (suc d) m) cs ms r rs

  evTuple : {d : ℕ} → List Carrier → (List Carrier → Carrier) → List Carrier → Carrier →
    B.NodeSet d → Maybe (Vec Carrier (suc d)) → List B.Config → List (List Carrier) →
    Carrier → List Carrier → Bool
  evTuple dom oracle prefix claim ns nothing cs ms r rs = false
  evTuple dom oracle prefix claim ns (just ys) cs ms r rs =
    same op claim (domainSum dom (B.evaluate ns ys)) ∧
    evRun dom oracle (prefix ∷ʳ r) (B.evaluate ns ys r) cs ms rs

evVerify : List Carrier → (List Carrier → Carrier) → List B.Config → Carrier →
  List (List Carrier) → List Carrier → Bool
evVerify dom oracle configs claim ms rs = evRun dom oracle [] claim configs ms rs

bounds : List B.Config → List ℕ
bounds = map proj₁

------------------------------------------------------------------------
-- Well-formed transcripts: one tuple of the right size per configuration

data Tuples : List B.Config → Set where
  [] : Tuples []
  _∷_ : {d : ℕ} {ns : B.NodeSet d} {cs : List B.Config} →
    Vec Carrier (suc d) → Tuples cs → Tuples ((d , ns) ∷ cs)

toLists : {cs : List B.Config} → Tuples cs → List (List Carrier)
toLists [] = []
toLists (y ∷ ts) = toList y ∷ toLists ts

decodeTuples : {cs : List B.Config} → Tuples cs → List Message
decodeTuples [] = []
decodeTuples {(d , ns) ∷ cs} (y ∷ ts) = B.decode ns y ∷ decodeTuples ts

private
  cons? : {d : ℕ} {ns : B.NodeSet d} {cs : List B.Config} →
    Maybe (Vec Carrier (suc d)) → Maybe (Tuples cs) → Maybe (Tuples ((d , ns) ∷ cs))
  cons? (just y) (just ts) = just (y ∷ ts)
  cons? _ _ = nothing

-- The external boundary: lists become tuples only at their exact sizes.
parse : (cs : List B.Config) → List (List Carrier) → Maybe (Tuples cs)
parse [] [] = just []
parse [] (_ ∷ _) = nothing
parse (_ ∷ _) [] = nothing
parse ((d , ns) ∷ cs) (m ∷ ms) = cons? (B.exactly (suc d) m) (parse cs ms)

parse-toLists : {cs : List B.Config} (ts : Tuples cs) → parse cs (toLists ts) ≡ just ts
parse-toLists [] = P.refl
parse-toLists {(d , ns) ∷ cs} (y ∷ ts) =
  P.cong₂ cons? (Rc.exactly-toList y) (parse-toLists ts)

-- Parsing keeps every received value, in order and with multiplicity.
parse-sound : (cs : List B.Config) (ms : List (List Carrier)) {ts : Tuples cs} →
  parse cs ms ≡ just ts → ms ≡ toLists ts
parse-sound [] [] P.refl = P.refl
parse-sound ((d , ns) ∷ cs) (m ∷ ms) h with B.exactly (suc d) m in e | parse cs ms in e′
parse-sound ((d , ns) ∷ cs) (m ∷ ms) P.refl | just y | just ts =
  cong₂ _∷_ (P.sym (B.exactly-sound (suc d) m e)) (parse-sound cs ms e′)

-- Malformed input is rejected: wrong tuple sizes or a wrong number of
-- messages, for every claim, oracle and challenge list.
mutual
  malformed-rejected : (dom : List Carrier) (oracle : List Carrier → Carrier)
    (prefix : List Carrier) (claim : Carrier) (cs : List B.Config) (ms : List (List Carrier)) →
    parse cs ms ≡ nothing → (rs : List Carrier) → evRun dom oracle prefix claim cs ms rs ≡ false
  malformed-rejected dom oracle prefix claim [] (_ ∷ _) h rs = P.refl
  malformed-rejected dom oracle prefix claim (_ ∷ _) [] h rs = P.refl
  malformed-rejected dom oracle prefix claim (_ ∷ _) (_ ∷ _) h [] = P.refl
  malformed-rejected dom oracle prefix claim ((d , ns) ∷ cs) (m ∷ ms) h (r ∷ rs) =
    tuple-rejected dom oracle prefix claim ns cs ms r rs (B.exactly (suc d) m) h

  tuple-rejected : {d : ℕ} (dom : List Carrier) (oracle : List Carrier → Carrier)
    (prefix : List Carrier) (claim : Carrier) (ns : B.NodeSet d) (cs : List B.Config)
    (ms : List (List Carrier)) (r : Carrier) (rs : List Carrier) (t : Maybe (Vec Carrier (suc d))) →
    cons? {ns = ns} t (parse cs ms) ≡ nothing → evTuple dom oracle prefix claim ns t cs ms r rs ≡ false
  tuple-rejected dom oracle prefix claim ns cs ms r rs nothing h = P.refl
  tuple-rejected dom oracle prefix claim ns cs ms r rs (just y) h with parse cs ms in e
  ... | nothing = P.trans (cong (same op claim (domainSum dom (B.evaluate ns y)) ∧_)
          (malformed-rejected dom oracle (prefix ∷ʳ r) (B.evaluate ns y r) cs ms e rs))
        (∧-zeroʳ _)

------------------------------------------------------------------------
-- Representation theorem for well-formed transcripts: for every tuple
-- list, challenge list, domain and terminal oracle, the evaluation-form
-- verdict equals the symbolic verdict on the decoded Lagrange circuits.
-- Node sets may differ between rounds, also for equal degrees.

representation : (dom : List Carrier) (oracle : List Carrier → Carrier) (prefix : List Carrier)
  {x y : Carrier} → x ≈ y → {cs : List B.Config} (ts : Tuples cs) (rs : List Carrier) →
  evRun dom oracle prefix x cs (toLists ts) rs ≡ symRun dom oracle prefix y (bounds cs) (decodeTuples ts) rs
representation dom oracle prefix xy [] [] = same-cong xy refl
representation dom oracle prefix xy [] (_ ∷ _) = P.refl
representation dom oracle prefix xy (_ ∷ _) [] = P.refl
representation dom oracle prefix {x} {y} xy {(d , ns) ∷ cs} (v ∷ ts) (r ∷ rs) =
  P.trans (cong (λ t → evTuple dom oracle prefix x ns t cs (toLists ts) r rs) (Rc.exactly-toList v))
    (cong₂ _∧_
      (P.trans (same-cong xy (domainSum-cong dom (B.decode-evaluate ns v)))
        (true-left _ (B.decode-degree ns v)))
      (representation dom oracle (prefix ∷ʳ r) (B.decode-evaluate ns v r) ts rs))

verify-representation : (dom : List Carrier) (oracle : List Carrier → Carrier)
  {cs : List B.Config} (claim : Carrier) (ts : Tuples cs) (rs : List Carrier) →
  evVerify dom oracle cs claim (toLists ts) rs ≡ symVerify dom oracle (bounds cs) claim (decodeTuples ts) rs
verify-representation dom oracle claim ts rs = representation dom oracle [] refl ts rs

------------------------------------------------------------------------
-- Simulation lemma: the symbolic verifier respects round messages with
-- equal degree verdicts and equivalent evaluations.

data Similar : List ℕ → List Message → List Message → Set where
  [] : Similar [] [] []
  _∷_ : {d : ℕ} {ds : List ℕ} {m m' : Message} {ms ms' : List Message} →
    Rc.Related d m m' → Similar ds ms ms' → Similar (d ∷ ds) (m ∷ ms) (m' ∷ ms')

symRun-cong : (dom : List Carrier) (oracle : List Carrier → Carrier) (prefix : List Carrier)
  {x y : Carrier} → x ≈ y → {ds : List ℕ} {ms ms' : List Message} → Similar ds ms ms' →
  (rs : List Carrier) → symRun dom oracle prefix x ds ms rs ≡ symRun dom oracle prefix y ds ms' rs
symRun-cong dom oracle prefix xy [] [] = same-cong xy refl
symRun-cong dom oracle prefix xy [] (_ ∷ _) = P.refl
symRun-cong dom oracle prefix xy (_ ∷ _) [] = P.refl
symRun-cong dom oracle prefix xy ((deg , ev) ∷ sim) (r ∷ rs) =
  cong₂ _∧_ (cong₂ _∧_ deg (same-cong xy (domainSum-cong dom ev)))
    (symRun-cong dom oracle (prefix ∷ʳ r) (ev r) sim rs)

------------------------------------------------------------------------
-- Encoding direction: arbitrary circuit messages passing their round's
-- degree check, sent as node values, give the symbolic verdict.

data Checked : List B.Config → List Message → Set where
  [] : Checked [] []
  _∷_ : {d : ℕ} {ns : B.NodeSet d} {cs : List B.Config} {m : Message} {ms : List Message} →
    C.degreeOK d m ≡ true → Checked cs ms → Checked ((d , ns) ∷ cs) (m ∷ ms)

encodeChecked : {cs : List B.Config} {ms : List Message} → Checked cs ms → Tuples cs
encodeChecked [] = []
encodeChecked {(d , ns) ∷ cs} {m ∷ ms} (h ∷ hs) = Rc.encode ns m ∷ encodeChecked hs

private
  decoded-similar : {cs : List B.Config} {ms : List Message} (hs : Checked cs ms) →
    Similar (bounds cs) (decodeTuples (encodeChecked hs)) ms
  decoded-similar [] = []
  decoded-similar {(d , ns) ∷ cs} {m ∷ ms} (h ∷ hs) =
    (P.trans (B.decode-degree ns (Rc.encode ns m)) (P.sym h) ,
     λ r → trans (sym (B.decode-evaluate ns (Rc.encode ns m) r)) (Rc.reconstruction ns m h r))
    ∷ decoded-similar hs

encode-representation : (dom : List Carrier) (oracle : List Carrier → Carrier)
  {cs : List B.Config} {ms : List Message} (claim : Carrier) (hs : Checked cs ms) (rs : List Carrier) →
  evVerify dom oracle cs claim (toLists (encodeChecked hs)) rs ≡ symVerify dom oracle (bounds cs) claim ms rs
encode-representation dom oracle claim hs rs = P.trans (verify-representation dom oracle claim (encodeChecked hs) rs)
  (symRun-cong dom oracle [] refl (decoded-similar hs) rs)

------------------------------------------------------------------------
-- Legacy specializations: Boolean domain, full run, repeated bound

boolean : List Carrier
boolean = 0# ∷ 1# ∷ []

private
  boolean-sum : (f : Carrier → Carrier) → domainSum boolean f ≈ plus (f 0#) (f 1#)
  boolean-sum f = nf-cong (+-congˡ (trans (normalize-≈ _) (+-identityʳ _)))

-- The symbolic verifier specializes to Circuit.Protocol.verify.
symRun-legacy : (oracle : List Carrier → Carrier) (d : ℕ) (prefix : List Carrier)
  {x y : Carrier} → x ≈ y → (n : ℕ) (ms : List Message) (rs : List Carrier) →
  symRun boolean oracle prefix x (replicate n d) ms rs ≡
  (n ≡ᵇ length ms) ∧ C.verifyWith op 0# oracle d prefix y ms rs
symRun-legacy oracle d prefix xy zero [] [] = same-cong xy refl
symRun-legacy oracle d prefix xy zero [] (_ ∷ _) = P.refl
symRun-legacy oracle d prefix xy zero (_ ∷ _) rs = P.refl
symRun-legacy oracle d prefix xy (suc n) [] rs = P.refl
symRun-legacy oracle d prefix xy (suc n) (m ∷ ms) [] = P.sym (∧-zeroʳ (n ≡ᵇ length ms))
symRun-legacy oracle d prefix {x} {y} xy (suc n) (m ∷ ms) (r ∷ rs) =
  P.trans (cong ((deg ∧ sx) ∧_) (symRun-legacy oracle d (prefix ∷ʳ r) refl n ms rs))
  (P.trans (∧-assoc deg sx (b ∧ vw))
  (P.trans (cong (deg ∧_) (x∙yz≈y∙xz sx b vw))
  (P.trans (x∙yz≈y∙xz deg b (sx ∧ vw))
  (cong (λ t → b ∧ (deg ∧ (t ∧ vw))) (same-cong xy (boolean-sum (C.evaluateMessage op m)))))))
  where
  deg = C.degreeOK d m
  sx = same op x (domainSum boolean (C.evaluateMessage op m))
  e = C.evaluateMessage op m r
  b = n ≡ᵇ length ms
  vw = C.verifyWith op 0# oracle d (prefix ∷ʳ r) e ms rs

symVerify-legacy : (oracle : List Carrier → Carrier) (n d : ℕ) (claim : Carrier)
  (ms : List Message) (rs : List Carrier) →
  symVerify boolean oracle (replicate n d) claim ms rs ≡ C.verify op 0# oracle n d claim ms rs
symVerify-legacy oracle n d claim ms rs = symRun-legacy oracle d [] refl n ms rs

-- The evaluation-form verifier specializes to Circuit.Barycentric.verify.
mutual
  evRun-legacy : (oracle : List Carrier → Carrier) (prefix : List Carrier) (claim : Carrier)
    (cs : List B.Config) (ms : List (List Carrier)) (rs : List Carrier) →
    evRun boolean oracle prefix claim cs ms rs ≡ B.run oracle prefix claim cs ms rs
  evRun-legacy oracle prefix claim [] [] [] = P.refl
  evRun-legacy oracle prefix claim [] [] (_ ∷ _) = P.refl
  evRun-legacy oracle prefix claim [] (_ ∷ _) _ = P.refl
  evRun-legacy oracle prefix claim (_ ∷ _) [] _ = P.refl
  evRun-legacy oracle prefix claim (_ ∷ _) (_ ∷ _) [] = P.refl
  evRun-legacy oracle prefix claim ((d , ns) ∷ cs) (m ∷ ms) (r ∷ rs) =
    evTuple-legacy oracle prefix claim ns cs ms r rs (B.exactly (suc d) m)

  evTuple-legacy : {d : ℕ} (oracle : List Carrier → Carrier) (prefix : List Carrier) (claim : Carrier)
    (ns : B.NodeSet d) (cs : List B.Config) (ms : List (List Carrier)) (r : Carrier)
    (rs : List Carrier) (t : Maybe (Vec Carrier (suc d))) →
    evTuple boolean oracle prefix claim ns t cs ms r rs ≡ B.runTuple oracle prefix claim ns t cs ms r rs
  evTuple-legacy oracle prefix claim ns cs ms r rs nothing = P.refl
  evTuple-legacy oracle prefix claim ns cs ms r rs (just v) = cong₂ _∧_
    (same-cong refl (boolean-sum (B.evaluate ns v)))
    (evRun-legacy oracle (prefix ∷ʳ r) (B.evaluate ns v r) cs ms rs)

------------------------------------------------------------------------
-- Residual sums: the terminal oracle of a partial run

-- residual dom f m prefix sums f over prefix extended by every tuple of m
-- domain values. The number m of unbound variables is explicit.
residual : List Carrier → (List Carrier → Carrier) → ℕ → List Carrier → Carrier
residual dom f zero prefix = f prefix
residual dom f (suc m) prefix = domainSum dom (λ a → residual dom f m (prefix ∷ʳ a))

-- Endpoints and the one-round splitting identity hold by definition.
residual-full : (dom : List Carrier) (f : List Carrier → Carrier) (prefix : List Carrier) →
  residual dom f 0 prefix ≡ f prefix
residual-full dom f prefix = P.refl

residual-split : (dom : List Carrier) (f : List Carrier → Carrier) (m : ℕ) (prefix : List Carrier) →
  residual dom f (suc m) prefix ≡ domainSum dom (λ a → residual dom f m (prefix ∷ʳ a))
residual-split dom f m prefix = P.refl

-- Explicit semantics: Σ_{z ∈ domain^m} f(prefix ++ z), in ring arithmetic.
tuples : List Carrier → ℕ → List (List Carrier)
tuples dom zero = [] ∷ []
tuples dom (suc m) = concatMap (λ a → map (a ∷_) (tuples dom m)) dom

ringSum : List Carrier → Carrier
ringSum = foldr _+_ 0#

private
  ringSum-++ : (xs ys : List Carrier) → ringSum (xs ++ ys) ≈ ringSum xs + ringSum ys
  ringSum-++ [] ys = sym (+-identityˡ _)
  ringSum-++ (x ∷ xs) ys = trans (+-congˡ (ringSum-++ xs ys)) (sym (+-assoc x _ _))

  domainSum-ringSum : (dom : List Carrier) (g : Carrier → Carrier) → domainSum dom g ≈ ringSum (map g dom)
  domainSum-ringSum [] g = refl
  domainSum-ringSum (a ∷ as) g = trans (normalize-≈ _) (+-congˡ (domainSum-ringSum as g))

  ringSum-map-cong : {A : Set} (xs : List A) {g h : A → Carrier} → (∀ a → g a ≈ h a) →
    ringSum (map g xs) ≈ ringSum (map h xs)
  ringSum-map-cong [] eq = refl
  ringSum-map-cong (a ∷ as) eq = +-cong (eq a) (ringSum-map-cong as eq)

  ringSum-concatMap : (dom : List Carrier) (T : List (List Carrier)) (F : List Carrier → Carrier) →
    ringSum (map F (concatMap (λ a → map (a ∷_) T) dom)) ≈
    ringSum (map (λ a → ringSum (map (λ z → F (a ∷ z)) T)) dom)
  ringSum-concatMap [] T F = refl
  ringSum-concatMap (a ∷ as) T F = begin
    ringSum (map F (map (a ∷_) T ++ concatMap (λ b → map (b ∷_) T) as))
      ≈⟨ reflexive (cong ringSum (map-++ F (map (a ∷_) T) _)) ⟩
    ringSum (map F (map (a ∷_) T) ++ map F (concatMap (λ b → map (b ∷_) T) as))
      ≈⟨ ringSum-++ (map F (map (a ∷_) T)) _ ⟩
    ringSum (map F (map (a ∷_) T)) + ringSum (map F (concatMap (λ b → map (b ∷_) T) as))
      ≈⟨ +-cong (reflexive (cong ringSum (P.sym (map-∘ T)))) (ringSum-concatMap as T F) ⟩
    ringSum (map (λ z → F (a ∷ z)) T) + ringSum (map (λ b → ringSum (map (λ z → F (b ∷ z)) T)) as) ∎

residual-sum : (dom : List Carrier) (f : List Carrier → Carrier) (m : ℕ) (prefix : List Carrier) →
  residual dom f m prefix ≈ ringSum (map (λ z → f (prefix ++ z)) (tuples dom m))
residual-sum dom f zero prefix =
  sym (trans (+-identityʳ _) (reflexive (cong f (++-identityʳ prefix))))
residual-sum dom f (suc m) prefix = begin
  domainSum dom (λ a → residual dom f m (prefix ∷ʳ a))
    ≈⟨ domainSum-ringSum dom _ ⟩
  ringSum (map (λ a → residual dom f m (prefix ∷ʳ a)) dom)
    ≈⟨ ringSum-map-cong dom (λ a → trans (residual-sum dom f m (prefix ∷ʳ a))
         (ringSum-map-cong (tuples dom m) λ z → reflexive (cong f (++-assoc prefix [ a ] z)))) ⟩
  ringSum (map (λ a → ringSum (map (λ z → f (prefix ++ (a ∷ z))) (tuples dom m))) dom)
    ≈⟨ ringSum-concatMap dom (tuples dom m) (λ z → f (prefix ++ z)) ⟨
  ringSum (map (λ z → f (prefix ++ z)) (tuples dom (suc m))) ∎
