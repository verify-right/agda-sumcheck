{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- Honest-prover completeness for the generalized verifiers of
-- Circuit.General (arbitrary domain, one bound per round, partial runs),
-- and public setup of certified node sets.
--
-- Polynomials are Circuit.Protocol circuits; variables are looked up by
-- position with the legacy default 0 for out-of-range indices. This
-- models z-lean's Fin n variables only when the arity matches.
module Circuit.GeneralCompleteness (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_; zero; _+_)
open import Data.Bool.Base using (true; false; _∧_; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; _≡ᵇ_)
import Data.Nat.Properties as ℕ
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; _++_; [_]; map; length)
open import Data.List.Properties using (++-assoc; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (∃-syntax; _,_)
open import Data.Vec.Base using (Vec; lookup; tabulate; toList)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)
open import Ring.Verifier using (same)
import Ring.FromRing as FromRing
import Ring.Lagrange as Lagrange
open import Circuit.Protocol hiding (collect; message; honest)
open import Circuit.Completeness using (values; substitute-correct; values-snoc; values-fixed;
  degree-check)
import Circuit.Barycentric as Barycentric
import Circuit.Reconstruction as Reconstruction
import Circuit.General as General

private
  module D = FromRing R _≟_ normalize normalize-≈
  module L = Lagrange R
  module B = Barycentric R _≟_ normalize normalize-≈
  module Rc = Reconstruction R _≟_ normalize normalize-≈
  module G = General R _≟_ normalize normalize-≈
  op = D.operations

------------------------------------------------------------------------
-- Honest messages: sum over the domain of the remaining variables

sumTree : List Carrier → (Carrier → Message Carrier) → Message Carrier
sumTree [] g = Leaf (Value 0#)
sumTree (a ∷ as) g = Branch (g a) (sumTree as g)

collect : List Carrier → Polynomial Carrier → List (Binding Carrier) → ℕ → Message Carrier
collect dom p env zero = Leaf (substitute 0# p env)
collect dom p env (suc m) = sumTree dom (λ a → collect dom p (env ∷ʳ Fixed a) m)

-- The round message after prefix, with m variables still unbound after
-- this round. It does not depend on future challenge values.
message : List Carrier → Polynomial Carrier → List Carrier → ℕ → Message Carrier
message dom p prefix m = collect dom p (map Fixed prefix ∷ʳ Challenge) m

honest : List Carrier → Polynomial Carrier → List Carrier → List Carrier → ℕ → List (Message Carrier)
honest dom p prefix [] m = []
honest dom p prefix (r ∷ rs) m = message dom p prefix (length rs + m) ∷ honest dom p (prefix ∷ʳ r) rs m

-- The next message depends only on the prefix and the remaining arity.
honest-independent : (dom : List Carrier) (p : Polynomial Carrier) (prefix : List Carrier)
  (r r' : Carrier) (rs rs' : List Carrier) (m : ℕ) → length rs ≡ length rs' →
  message dom p prefix (length rs + m) ≡ message dom p prefix (length rs' + m)
honest-independent dom p prefix r r' rs rs' m h = cong (λ k → message dom p prefix (k + m)) h

------------------------------------------------------------------------
-- Honest-message identity: the message evaluates to the residual sum

private
  f : Polynomial Carrier → List Carrier → Carrier
  f p = evaluate op 0# p

  sumTree-eval : (dom : List Carrier) (g : Carrier → Message Carrier) (r : Carrier) →
    evaluateMessage op (sumTree dom g) r ≡ G.domainSum dom (λ a → evaluateMessage op (g a) r)
  sumTree-eval [] g r = P.refl
  sumTree-eval (a ∷ as) g r = cong (plus op (evaluateMessage op (g a) r)) (sumTree-eval as g r)

collect-correct : (dom : List Carrier) (p : Polynomial Carrier) (env : List (Binding Carrier))
  (m : ℕ) (r : Carrier) →
  evaluateMessage op (collect dom p env m) r ≈ G.residual dom (f p) m (values r env)
collect-correct dom p env zero r = reflexive (substitute-correct op 0# p env r)
collect-correct dom p env (suc m) r = trans (reflexive (sumTree-eval dom _ r))
  (G.domainSum-cong dom λ a → trans (collect-correct dom p (env ∷ʳ Fixed a) m r)
    (reflexive (cong (G.residual dom (f p) m) (values-snoc r env (Fixed a)))))

message-correct : (dom : List Carrier) (p : Polynomial Carrier) (prefix : List Carrier) (m : ℕ)
  (r : Carrier) → evaluateMessage op (message dom p prefix m) r ≈ G.residual dom (f p) m (prefix ∷ʳ r)
message-correct dom p prefix m r = trans (collect-correct dom p _ m r)
  (reflexive (cong (G.residual dom (f p) m)
    (P.trans (values-snoc r (map Fixed prefix) Challenge) (cong (_∷ʳ r) (values-fixed r prefix)))))

------------------------------------------------------------------------
-- Per-variable degree. In the round for variable k only variable k is the
-- round variable, so the honest message's occurrence count is at most the
-- number of occurrences of variable k in p. This is the analogue of
-- z-lean's per-variable bound indDegreeK; it is a syntactic count, not
-- the exact degree.

occurrences : Polynomial Carrier → ℕ → ℕ
occurrences (Const _) k = 0
occurrences (Var j) k = if j ≡ᵇ k then 1 else 0
occurrences (AddP p q) k = occurrences p k + occurrences q k
occurrences (MulP p q) k = occurrences p k + occurrences q k
occurrences (NegP p) k = occurrences p k

occurrences-≤-bound : (p : Polynomial Carrier) (k : ℕ) → occurrences p k ≤ bound p
occurrences-≤-bound (Const _) k = z≤n
occurrences-≤-bound (Var j) k with j ≡ᵇ k
... | true = ℕ.≤-refl
... | false = z≤n
occurrences-≤-bound (AddP p q) k = ℕ.+-mono-≤ (occurrences-≤-bound p k) (occurrences-≤-bound q k)
occurrences-≤-bound (MulP p q) k = ℕ.+-mono-≤ (occurrences-≤-bound p k) (occurrences-≤-bound q k)
occurrences-≤-bound (NegP p) k = occurrences-≤-bound p k

private
  -- Environments built by message: fixed prefix, round variable, fixed rest.
  env : List Carrier → List Carrier → List (Binding Carrier)
  env xs zs = map Fixed xs ++ Challenge ∷ map Fixed zs

  lookup-fixed : (zs : List Carrier) (j : ℕ) →
    degree (bindingPolynomial (lookupOr (Fixed 0#) (map Fixed zs) j)) ≡ 0
  lookup-fixed [] j = P.refl
  lookup-fixed (z ∷ zs) zero = P.refl
  lookup-fixed (z ∷ zs) (suc j) = lookup-fixed zs j

  lookup-env : (xs zs : List Carrier) (j : ℕ) →
    degree (bindingPolynomial (lookupOr (Fixed 0#) (env xs zs) j)) ≡ (if j ≡ᵇ length xs then 1 else 0)
  lookup-env [] zs zero = P.refl
  lookup-env [] zs (suc j) = lookup-fixed zs j
  lookup-env (x ∷ xs) zs zero = P.refl
  lookup-env (x ∷ xs) zs (suc j) = lookup-env xs zs j

  substitute-occurrences : (p : Polynomial Carrier) (xs zs : List Carrier) →
    degree (substitute 0# p (env xs zs)) ≤ occurrences p (length xs)
  substitute-occurrences (Const _) xs zs = z≤n
  substitute-occurrences (Var j) xs zs = ℕ.≤-reflexive (lookup-env xs zs j)
  substitute-occurrences (AddP p q) xs zs =
    ℕ.+-mono-≤ (substitute-occurrences p xs zs) (substitute-occurrences q xs zs)
  substitute-occurrences (MulP p q) xs zs =
    ℕ.+-mono-≤ (substitute-occurrences p xs zs) (substitute-occurrences q xs zs)
  substitute-occurrences (NegP p) xs zs = substitute-occurrences p xs zs

  env-snoc : (xs zs : List Carrier) (a : Carrier) → env xs zs ∷ʳ Fixed a ≡ env xs (zs ∷ʳ a)
  env-snoc xs zs a = P.trans (++-assoc (map Fixed xs) (Challenge ∷ map Fixed zs) [ Fixed a ])
    (cong (λ t → map Fixed xs ++ Challenge ∷ t) (P.sym (map-++ Fixed zs [ a ])))

  collect-occurrences : (dom : List Carrier) (p : Polynomial Carrier) (xs zs : List Carrier)
    (m d : ℕ) → occurrences p (length xs) ≤ d → degreeOK d (collect dom p (env xs zs) m) ≡ true
  collect-occurrences dom p xs zs zero d h = degree-check (ℕ.≤-trans (substitute-occurrences p xs zs) h)
  collect-occurrences dom p xs zs (suc m) d h = tree dom
    where
    tree : (as : List Carrier) → degreeOK d (sumTree as (λ a → collect dom p (env xs zs ∷ʳ Fixed a) m)) ≡ true
    tree [] = P.refl
    tree (a ∷ as) = cong₂ _∧_
      (P.subst (λ e → degreeOK d (collect dom p e m) ≡ true) (P.sym (env-snoc xs zs a))
        (collect-occurrences dom p xs (zs ∷ʳ a) m d h))
      (tree as)

  length-snoc : {A : Set} (xs : List A) (x : A) → length (xs ∷ʳ x) ≡ suc (length xs)
  length-snoc [] x = P.refl
  length-snoc (y ∷ xs) x = cong suc (length-snoc xs x)

message-degree : (dom : List Carrier) (p : Polynomial Carrier) (prefix : List Carrier) (m d : ℕ) →
  occurrences p (length prefix) ≤ d → degreeOK d (message dom p prefix m) ≡ true
message-degree dom p prefix m d = collect-occurrences dom p prefix [] m d

-- Public per-round bounds: the bound of round k covers variable k.
data Bounded (p : Polynomial Carrier) : ℕ → List ℕ → Set where
  [] : {k : ℕ} → Bounded p k []
  _∷_ : {k d : ℕ} {ds : List ℕ} → occurrences p k ≤ d → Bounded p (suc k) ds → Bounded p k (d ∷ ds)

-- The conservative global bound implies every per-round bound.
bounded-global : (p : Polynomial Carrier) (k : ℕ) (bs : List ℕ) → All (bound p ≤_) bs → Bounded p k bs
bounded-global p k [] [] = []
bounded-global p k (d ∷ ds) (h ∷ hs) = ℕ.≤-trans (occurrences-≤-bound p k) h ∷ bounded-global p (suc k) ds hs

private
  next-bounded : {p : Polynomial Carrier} (prefix : List Carrier) (r : Carrier) {ds : List ℕ} →
    Bounded p (suc (length prefix)) ds → Bounded p (length (prefix ∷ʳ r)) ds
  next-bounded {p} prefix r {ds} = P.subst (λ k → Bounded p k ds) (P.sym (length-snoc prefix r))

------------------------------------------------------------------------
-- Completeness of the symbolic verifier. After k = length rs rounds the
-- terminal oracle is the residual sum over the m unbound variables, and the
-- initial claim is the sum over all k + m variables.

honest-run : (dom : List Carrier) (p : Polynomial Carrier) (m : ℕ) →
  (prefix : List Carrier) (bs : List ℕ) → Bounded p (length prefix) bs →
  (rs : List Carrier) → length bs ≡ length rs → (claim : Carrier) →
  same op claim (G.residual dom (f p) (length rs + m) prefix) ≡ true →
  G.symRun dom (G.residual dom (f p) m) prefix claim bs (honest dom p prefix rs m) rs ≡ true
honest-run dom p m prefix [] [] [] P.refl claim h = h
honest-run dom p m prefix (d ∷ ds) (bd ∷ bds) (r ∷ rs) len claim h = cong₂ _∧_
  (cong₂ _∧_ (message-degree dom p prefix (length rs + m) d bd)
    (P.trans (D.same-cong refl (G.domainSum-cong dom λ a → message-correct dom p prefix (length rs + m) a)) h))
  (honest-run dom p m (prefix ∷ʳ r) ds (next-bounded prefix r bds) rs (ℕ.suc-injective len) _
    (D.same-complete _ _ (message-correct dom p prefix (length rs + m) r)))

honest-complete : (dom : List Carrier) (p : Polynomial Carrier) (m : ℕ)
  (bs : List ℕ) → Bounded p 0 bs → (rs : List Carrier) → length bs ≡ length rs →
  G.symVerify dom (G.residual dom (f p) m) bs (G.residual dom (f p) (length rs + m) [])
    (honest dom p [] rs m) rs ≡ true
honest-complete dom p m bs bds rs len =
  honest-run dom p m [] bs bds rs len _ (D.same-refl _)

------------------------------------------------------------------------
-- Completeness of the evaluation-form verifier, derived from the
-- symbolic one by encoding and the representation theorem.

honest-checked : (dom : List Carrier) (p : Polynomial Carrier) (m : ℕ) (prefix : List Carrier)
  (cs : List B.Config) → Bounded p (length prefix) (G.bounds cs) → (rs : List Carrier) →
  length cs ≡ length rs → G.Checked cs (honest dom p prefix rs m)
honest-checked dom p m prefix [] [] [] P.refl = G.[]
honest-checked dom p m prefix ((d , ns) ∷ cs) (bd ∷ bds) (r ∷ rs) len =
  message-degree dom p prefix (length rs + m) d bd G.∷
  honest-checked dom p m (prefix ∷ʳ r) cs (next-bounded prefix r bds) rs (ℕ.suc-injective len)

-- The executable honest prover in evaluation form.
honestTuples : (dom : List Carrier) (p : Polynomial Carrier) (m : ℕ) (prefix : List Carrier) →
  List B.Config → List Carrier → List (List Carrier)
honestTuples dom p m prefix [] rs = []
honestTuples dom p m prefix (_ ∷ _) [] = []
honestTuples dom p m prefix ((d , ns) ∷ cs) (r ∷ rs) =
  toList (Rc.encode ns (message dom p prefix (length rs + m))) ∷ honestTuples dom p m (prefix ∷ʳ r) cs rs

honestTuples-encoded : (dom : List Carrier) (p : Polynomial Carrier) (m : ℕ) (prefix : List Carrier)
  (cs : List B.Config) (bds : Bounded p (length prefix) (G.bounds cs)) (rs : List Carrier)
  (len : length cs ≡ length rs) →
  honestTuples dom p m prefix cs rs ≡ G.toLists (G.encodeChecked (honest-checked dom p m prefix cs bds rs len))
honestTuples-encoded dom p m prefix [] [] [] P.refl = P.refl
honestTuples-encoded dom p m prefix ((d , ns) ∷ cs) (bd ∷ bds) (r ∷ rs) len =
  cong (_ ∷_) (honestTuples-encoded dom p m (prefix ∷ʳ r) cs (next-bounded prefix r bds) rs (ℕ.suc-injective len))

evaluation-form-complete : (dom : List Carrier) (p : Polynomial Carrier) (m : ℕ)
  (cs : List B.Config) → Bounded p 0 (G.bounds cs) → (rs : List Carrier) → (len : length cs ≡ length rs) →
  G.evVerify dom (G.residual dom (f p) m) cs (G.residual dom (f p) (length rs + m) [])
    (honestTuples dom p m [] cs rs) rs ≡ true
evaluation-form-complete dom p m cs bds rs len =
  P.trans (cong (λ ms → G.evVerify dom _ cs _ ms rs) (honestTuples-encoded dom p m [] cs bds rs len))
  (P.trans (G.encode-representation dom _ _ (honest-checked dom p m [] cs bds rs len) rs)
    (honest-complete dom p m (G.bounds cs) bds rs (P.trans (length-bounds cs) len)))
  where
  length-bounds : (cs : List B.Config) → length (G.bounds cs) ≡ length cs
  length-bounds [] = P.refl
  length-bounds (_ ∷ cs) = cong suc (length-bounds cs)

------------------------------------------------------------------------
-- Public setup: weights from an inversion procedure, validated by certify?

weightsFor : {d : ℕ} → (Carrier → Carrier) → Vec Carrier (suc d) → Vec Carrier (suc d)
weightsFor inv xs = tabulate (λ i → inv (L.omitted (lookup xs) i (lookup xs i)))

setup : {d : ℕ} → (Carrier → Carrier) → Vec Carrier (suc d) → Maybe (B.NodeSet d)
setup inv xs with B.certify? xs (weightsFor inv xs)
... | yes certified = just (B.nodeSet xs (weightsFor inv xs) certified)
... | no _ = nothing

-- Success is correct by construction (NodeSet carries its certificate) and
-- keeps the requested nodes.
setup-nodes : {d : ℕ} (inv : Carrier → Carrier) (xs : Vec Carrier (suc d)) {ns : B.NodeSet d} →
  setup inv xs ≡ just ns → B.nodes ns ≡ xs
setup-nodes inv xs h with B.certify? xs (weightsFor inv xs)
setup-nodes inv xs P.refl | yes _ = P.refl

-- Setup succeeds whenever inv inverts every node denominator.
setup-complete : {d : ℕ} (inv : Carrier → Carrier) (xs : Vec Carrier (suc d)) →
  (∀ i → L.omitted (lookup xs) i (lookup xs i) * inv (L.omitted (lookup xs) i (lookup xs i)) ≈ 1#) →
  ∃[ ns ] (setup inv xs ≡ just ns)
setup-complete inv xs h with B.certify? xs (weightsFor inv xs)
... | yes certified = _ , P.refl
... | no uncertified = ⊥-elim (uncertified λ i →
  trans (*-congʳ (reflexive (lookup∘tabulate (λ j → inv (L.omitted (lookup xs) j (lookup xs j))) i)))
    (trans (*-comm _ _) (h i)))
