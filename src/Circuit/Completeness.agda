{-# OPTIONS --safe --without-K #-}
-- Honest-prover completeness for arbitrary-degree circuit sumcheck.
module Circuit.Completeness where

open import Data.Bool.Base using (true; _∧_)
open import Data.Bool.Properties using (∧-assoc; T-≡)
open import Data.Nat.Base using (ℕ; suc; _≤_; _<ᵇ_; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.List.Base using (List; []; _∷_; [_]; _∷ʳ_; map; length)
open import Data.List.Properties using (map-++; map-∘; map-id)
open import Function.Bundles using (module Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Ring.Verifier using (Operations; one; same)
open import Circuit.Protocol

-- The replay verifier is the interactive round check followed by the rest.
verify-round-step : {F : Set} (op : Operations F) (z : F) (oracle : List F → F)
  (d : ℕ) (prefix : List F) (claim : F) (m : Message F) (ms : List (Message F))
  (r : F) (rs : List F) →
  verifyWith op z oracle d prefix claim (m ∷ ms) (r ∷ rs) ≡
  checkRound op z d claim m ∧ verifyWith op z oracle d (prefix ∷ʳ r) (nextClaim op m r) ms rs
verify-round-step op z oracle d prefix claim m ms r rs = sym (∧-assoc (degreeOK d m)
  (same op claim (plus op (evaluateMessage op m z) (evaluateMessage op m (one op))))
  (verifyWith op z oracle d (prefix ∷ʳ r) (nextClaim op m r) ms rs))

------------------------------------------------------------------------
-- Messages evaluate to partial Boolean-cube sums

values : {F : Set} → F → List (Binding F) → List F
values r = map (bindingValue r)

lookup-values : {F : Set} (z r : F) (env : List (Binding F)) (i : ℕ) →
  bindingValue r (lookupOr (Fixed z) env i) ≡ lookupOr z (values r env) i
lookup-values z r [] i = refl
lookup-values z r (b ∷ bs) ℕ.zero = refl
lookup-values z r (b ∷ bs) (suc i) = lookup-values z r bs i

binding-correct : {F : Set} (op : Operations F) (r : F) (b : Binding F) →
  evaluateU op (bindingPolynomial b) r ≡ bindingValue r b
binding-correct op r (Fixed a) = refl
binding-correct op r Challenge = refl

substitute-correct : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (env : List (Binding F)) (r : F) →
  evaluateU op (substitute z p env) r ≡ evaluate op z p (values r env)
substitute-correct op z (Const a) env r = refl
substitute-correct op z (Var i) env r =
  trans (binding-correct op r (lookupOr (Fixed z) env i)) (lookup-values z r env i)
substitute-correct op z (AddP p q) env r =
  cong₂ (plus op) (substitute-correct op z p env r) (substitute-correct op z q env r)
substitute-correct op z (MulP p q) env r =
  cong₂ (times op) (substitute-correct op z p env r) (substitute-correct op z q env r)
substitute-correct op z (NegP p) env r = cong (minus op) (substitute-correct op z p env r)

values-snoc : {F : Set} (r : F) (env : List (Binding F)) (b : Binding F) →
  values r (env ∷ʳ b) ≡ values r env ∷ʳ bindingValue r b
values-snoc r env b = map-++ (bindingValue r) env [ b ]

values-fixed : {F : Set} (r : F) (prefix : List F) → values r (map Fixed prefix) ≡ prefix
values-fixed r prefix = trans (sym (map-∘ {g = bindingValue r} {f = Fixed} prefix)) (map-id prefix)

collect-correct : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (env : List (Binding F)) (shape : List F) (r : F) →
  evaluateMessage op (collect op z p env shape) r ≡ cube op z p (values r env) shape
collect-correct op z p env [] r = substitute-correct op z p env r
collect-correct op z p env (_ ∷ shape) r = cong₂ (plus op)
  (trans (collect-correct op z p (env ∷ʳ Fixed z) shape r)
    (cong (λ prefix → cube op z p prefix shape) (values-snoc r env (Fixed z))))
  (trans (collect-correct op z p (env ∷ʳ Fixed (one op)) shape r)
    (cong (λ prefix → cube op z p prefix shape) (values-snoc r env (Fixed (one op)))))

message-correct : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (prefix shape : List F) (r : F) →
  evaluateMessage op (message op z p prefix shape) r ≡ cube op z p (prefix ∷ʳ r) shape
message-correct op z p prefix shape r =
  trans (collect-correct op z p (map Fixed prefix ∷ʳ Challenge) shape r)
    (cong (λ es → cube op z p es shape)
      (trans (values-snoc r (map Fixed prefix) Challenge)
        (cong (_∷ʳ r) (values-fixed r prefix))))

------------------------------------------------------------------------
-- The next honest message depends only on the number of future rounds,
-- not on the values of future challenges.

collect-length : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (env : List (Binding F)) (as bs : List F) → length as ≡ length bs →
  collect op z p env as ≡ collect op z p env bs
collect-length op z p env [] [] h = refl
collect-length op z p env (_ ∷ as) (_ ∷ bs) h = cong₂ Branch
  (collect-length op z p (env ∷ʳ Fixed z) as bs (ℕ.suc-injective h))
  (collect-length op z p (env ∷ʳ Fixed (one op)) as bs (ℕ.suc-injective h))

message-independent : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (prefix as bs : List F) → length as ≡ length bs →
  message op z p prefix as ≡ message op z p prefix bs
message-independent op z p prefix =
  collect-length op z p (map Fixed prefix ∷ʳ Challenge)

------------------------------------------------------------------------
-- Honest messages pass the degree check when the bound covers the circuit

binding-degree : {F : Set} (b : Binding F) → degree (bindingPolynomial b) ≤ 1
binding-degree (Fixed a) = z≤n
binding-degree Challenge = s≤s z≤n

substitute-degree : {F : Set} (z : F) (p : Polynomial F) (env : List (Binding F)) →
  degree (substitute z p env) ≤ bound p
substitute-degree z (Const a) env = z≤n
substitute-degree z (Var i) env = binding-degree (lookupOr (Fixed z) env i)
substitute-degree z (AddP p q) env = ℕ.+-mono-≤ (substitute-degree z p env) (substitute-degree z q env)
substitute-degree z (MulP p q) env = ℕ.+-mono-≤ (substitute-degree z p env) (substitute-degree z q env)
substitute-degree z (NegP p) env = substitute-degree z p env

degree-check : {m n : ℕ} → m ≤ n → (m <ᵇ suc n) ≡ true
degree-check h = Equivalence.to T-≡ (ℕ.<⇒<ᵇ (s≤s h))

collect-degree : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (env : List (Binding F)) (shape : List F) (d : ℕ) → bound p ≤ d →
  degreeOK d (collect op z p env shape) ≡ true
collect-degree op z p env [] d h = degree-check (ℕ.≤-trans (substitute-degree z p env) h)
collect-degree op z p env (_ ∷ shape) d h = cong₂ _∧_
  (collect-degree op z p (env ∷ʳ Fixed z) shape d h)
  (collect-degree op z p (env ∷ʳ Fixed (one op)) shape d h)

honest-length : {F : Set} (op : Operations F) (z : F) (p : Polynomial F)
  (prefix challenges : List F) → length (honest op z p prefix challenges) ≡ length challenges
honest-length op z p prefix [] = refl
honest-length op z p prefix (r ∷ rs) = cong suc (honest-length op z p (prefix ∷ʳ r) rs)

------------------------------------------------------------------------
-- Completeness: the honest transcript for a correct claim is accepted.
-- Only reflexivity of the executable equality is needed.

module Correct {F : Set} (op : Operations F) (z : F)
  (same-refl : (a : F) → same op a a ≡ true) where

  honest-step : (p : Polynomial F) (d : ℕ) → bound p ≤ d →
    (prefix : List F) (claim : F) (challenges : List F) →
    same op claim (cube op z p prefix challenges) ≡ true →
    verifyWith op z (evaluate op z p) d prefix claim
      (honest op z p prefix challenges) challenges ≡ true
  honest-step p d degree-bound prefix claim [] claim-correct = claim-correct
  honest-step p d degree-bound prefix claim (r ∷ rs) claim-correct = cong₂ _∧_
    (collect-degree op z p (map Fixed prefix ∷ʳ Challenge) rs d degree-bound)
    (cong₂ _∧_
      (trans (cong (same op claim) (cong₂ (plus op)
          (message-correct op z p prefix rs z)
          (message-correct op z p prefix rs (one op))))
        claim-correct)
      (trans (cong (λ c → verifyWith op z (evaluate op z p) d (prefix ∷ʳ r) c
                            (honest op z p (prefix ∷ʳ r) rs) rs)
               (message-correct op z p prefix rs r))
        (honest-step p d degree-bound (prefix ∷ʳ r) (cube op z p (prefix ∷ʳ r) rs) rs
          (same-refl (cube op z p (prefix ∷ʳ r) rs)))))

  honest-complete : (p : Polynomial F) (d : ℕ) → bound p ≤ d →
    (claim : F) (challenges : List F) →
    same op claim (cube op z p [] challenges) ≡ true →
    verify op z (evaluate op z p) (length challenges) d claim
      (honest op z p [] challenges) challenges ≡ true
  honest-complete p d degree-bound claim challenges claim-correct = cong₂ _∧_
    (Equivalence.to T-≡ (ℕ.≡⇒≡ᵇ (length challenges) (length (honest op z p [] challenges))
      (sym (honest-length op z p [] challenges))))
    (honest-step p d degree-bound [] claim challenges claim-correct)
