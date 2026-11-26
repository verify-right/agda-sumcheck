{-# OPTIONS --safe --without-K #-}
-- Sumcheck for polynomials of arbitrary degree, given as arithmetic
-- circuits, with an executable honest prover.
module Circuit.Protocol where

open import Data.Bool.Base using (Bool; false; _∧_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; map; length)
open import Ring.Verifier using (Operations; one; add; mul; neg; normalize; same)

-- Multivariate circuits; variables are indexed by position in the point.
data Polynomial (F : Set) : Set where
  Const : F → Polynomial F
  Var : ℕ → Polynomial F
  AddP MulP : Polynomial F → Polynomial F → Polynomial F
  NegP : Polynomial F → Polynomial F

-- Univariate circuits in the round variable.
data Univariate (F : Set) : Set where
  Value : F → Univariate F
  UVar : Univariate F
  UAdd UMul : Univariate F → Univariate F → Univariate F
  UNeg : Univariate F → Univariate F

-- A round message is a sum tree of univariate circuits. It is never
-- expanded into coefficients; its degree is at most the maximum leaf degree.
data Message (F : Set) : Set where
  Leaf : Univariate F → Message F
  Branch : Message F → Message F → Message F

plus : {F : Set} → Operations F → F → F → F
plus op a b = normalize op (add op a b)

times : {F : Set} → Operations F → F → F → F
times op a b = normalize op (mul op a b)

minus : {F : Set} → Operations F → F → F
minus op a = normalize op (neg op a)

-- List lookup with a default for out-of-range indices.
lookupOr : {A : Set} → A → List A → ℕ → A
lookupOr fallback [] i = fallback
lookupOr fallback (a ∷ as) zero = a
lookupOr fallback (a ∷ as) (suc i) = lookupOr fallback as i

-- z is the ring's zero; it is also the value of out-of-range variables.
evaluate : {F : Set} → Operations F → F → Polynomial F → List F → F
evaluate op z (Const a) point = a
evaluate op z (Var i) point = lookupOr z point i
evaluate op z (AddP p q) point = plus op (evaluate op z p point) (evaluate op z q point)
evaluate op z (MulP p q) point = times op (evaluate op z p point) (evaluate op z q point)
evaluate op z (NegP p) point = minus op (evaluate op z p point)

evaluateU : {F : Set} → Operations F → Univariate F → F → F
evaluateU op (Value a) r = a
evaluateU op UVar r = r
evaluateU op (UAdd p q) r = plus op (evaluateU op p r) (evaluateU op q r)
evaluateU op (UMul p q) r = times op (evaluateU op p r) (evaluateU op q r)
evaluateU op (UNeg p) r = minus op (evaluateU op p r)

evaluateMessage : {F : Set} → Operations F → Message F → F → F
evaluateMessage op (Leaf p) r = evaluateU op p r
evaluateMessage op (Branch p q) r = plus op (evaluateMessage op p r) (evaluateMessage op q r)

-- A conservative degree bound: it counts variable occurrences, so a sum
-- adds bounds where the maximum would suffice (see Circuit.Degree).
degree : {F : Set} → Univariate F → ℕ
degree (Value _) = 0
degree UVar = 1
degree (UAdd p q) = degree p + degree q
degree (UMul p q) = degree p + degree q
degree (UNeg p) = degree p

bound : {F : Set} → Polynomial F → ℕ
bound (Const _) = 0
bound (Var _) = 1
bound (AddP p q) = bound p + bound q
bound (MulP p q) = bound p + bound q
bound (NegP p) = bound p

degreeOK : {F : Set} → ℕ → Message F → Bool
degreeOK d (Leaf p) = degree p <ᵇ suc d
degreeOK d (Branch p q) = degreeOK d p ∧ degreeOK d q

-- A variable is either fixed to a value or is the current round variable.
data Binding (F : Set) : Set where
  Fixed : F → Binding F
  Challenge : Binding F

bindingValue : {F : Set} → F → Binding F → F
bindingValue r (Fixed a) = a
bindingValue r Challenge = r

bindingPolynomial : {F : Set} → Binding F → Univariate F
bindingPolynomial (Fixed a) = Value a
bindingPolynomial Challenge = UVar

substitute : {F : Set} → F → Polynomial F → List (Binding F) → Univariate F
substitute z (Const a) env = Value a
substitute z (Var i) env = bindingPolynomial (lookupOr (Fixed z) env i)
substitute z (AddP p q) env = UAdd (substitute z p env) (substitute z q env)
substitute z (MulP p q) env = UMul (substitute z p env) (substitute z q env)
substitute z (NegP p) env = UNeg (substitute z p env)

-- The list's contents are ignored: it supplies the number of remaining
-- Boolean variables. The current challenge is not an input to message.
collect : {F : Set} → Operations F → F → Polynomial F → List (Binding F) → List F → Message F
collect op z p env [] = Leaf (substitute z p env)
collect op z p env (_ ∷ rest) = Branch
  (collect op z p (env ∷ʳ Fixed z) rest)
  (collect op z p (env ∷ʳ Fixed (one op)) rest)

message : {F : Set} → Operations F → F → Polynomial F → List F → List F → Message F
message op z p prefix remaining = collect op z p (map Fixed prefix ∷ʳ Challenge) remaining

-- Sum of p over the Boolean cube in the remaining variables.
cube : {F : Set} → Operations F → F → Polynomial F → List F → List F → F
cube op z p prefix [] = evaluate op z p prefix
cube op z p prefix (_ ∷ rest) = plus op
  (cube op z p (prefix ∷ʳ z) rest)
  (cube op z p (prefix ∷ʳ one op) rest)

honest : {F : Set} → Operations F → F → Polynomial F → List F → List F → List (Message F)
honest op z p prefix [] = []
honest op z p prefix (r ∷ rest) =
  message op z p prefix rest ∷ honest op z p (prefix ∷ʳ r) rest

-- Interactive callers can check a message before sampling the challenge,
-- then use nextClaim after receiving it. The replay verifier below agrees.
checkRound : {F : Set} → Operations F → F → ℕ → F → Message F → Bool
checkRound op z d claim m = degreeOK d m ∧
  same op claim (plus op (evaluateMessage op m z) (evaluateMessage op m (one op)))

nextClaim : {F : Set} → Operations F → Message F → F → F
nextClaim = evaluateMessage

-- Challenges and prover messages are supplied separately. A message must be
-- fixed before the corresponding challenge is sampled by the caller.
verifyWith : {F : Set} → Operations F → F → (List F → F) → ℕ → List F → F →
  List (Message F) → List F → Bool
verifyWith op z oracle d prefix claim [] [] = same op claim (oracle prefix)
verifyWith op z oracle d prefix claim [] (_ ∷ _) = false
verifyWith op z oracle d prefix claim (_ ∷ _) [] = false
verifyWith op z oracle d prefix claim (m ∷ ms) (r ∷ rs) =
  degreeOK d m ∧ (same op claim (plus op (evaluateMessage op m z) (evaluateMessage op m (one op))) ∧
    verifyWith op z oracle d (prefix ∷ʳ r) (evaluateMessage op m r) ms rs)

verify : {F : Set} → Operations F → F → (List F → F) → ℕ → ℕ → F →
  List (Message F) → List F → Bool
verify op z oracle n d claim messages challenges =
  (n ≡ᵇ length messages) ∧ verifyWith op z oracle d [] claim messages challenges
