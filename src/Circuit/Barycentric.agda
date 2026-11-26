{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (Decidable)

-- General-degree evaluation-form sumcheck. A round message of degree at
-- most d is a tuple of d + 1 values at public, certified nodes. The verifier
-- evaluates it with the first barycentric form (Ring.Lagrange) and never
-- builds a polynomial or circuit. The circuit is built only on the proof
-- side, to show that the verdict equals Circuit.Protocol's for every
-- transcript.
module Circuit.Barycentric (R : CommutativeRing 0ℓ 0ℓ)
  (open CommutativeRing R using (Carrier; _≈_))
  (_≟_ : Decidable _≈_)
  (normalize : Carrier → Carrier)
  (normalize-≈ : (x : Carrier) → normalize x ≈ x)
  where

open CommutativeRing R hiding (Carrier; _≈_; zero)
open import Algebra.Bundles using (CommutativeMonoid)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-commutativeMonoid)
open import Data.Nat.Base using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Fin.Base using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List.Base using (List; []; _∷_; _∷ʳ_; map; length; replicate)
open import Data.List.Properties using (length-map)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; toList)
open import Data.Vec.Functional using (Vector; removeAt)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong; cong₂)
open import Algebra.Properties.CommutativeSemigroup
  (CommutativeMonoid.commutativeSemigroup ∧-commutativeMonoid) using (x∙yz≈y∙xz)
open import Ring.Verifier using (same)
import Ring.Verifier as Wire
import Ring.FromRing as FromRing
import Ring.Lagrange as Lagrange
import Circuit.Protocol as C

private
  module D = FromRing R _≟_ normalize normalize-≈
  module L = Lagrange R

open D public using (operations)

private
  op = operations

  plus times : Carrier → Carrier → Carrier
  plus = C.plus op
  times = C.times op

  -- r - x, normalized
  diff : Carrier → Carrier → Carrier
  diff r x = plus r (C.minus op x)

  diff-≈ : (r x : Carrier) → diff r x ≈ r - x
  diff-≈ r x = trans (normalize-≈ _) (+-congˡ (normalize-≈ _))

  nf-cong : {a b : Carrier} → a ≈ b → normalize a ≈ normalize b
  nf-cong {a} {b} h = trans (normalize-≈ a) (trans h (sym (normalize-≈ b)))

  same-cong : {a b c d : Carrier} → a ≈ b → c ≈ d → same op a c ≡ same op b d
  same-cong {a} {b} {c} {d} = D.same-cong {a} {b} {c} {d}

  -- stdlib sum-cong-≋ with the summands given explicitly.
  Σ-cong : {n : ℕ} (f g : Vector Carrier n) → (∀ i → f i ≈ g i) → L.Σ.sum f ≈ L.Σ.sum g
  Σ-cong f g = L.Σ.sum-cong-≋ {x = f} {y = g}

------------------------------------------------------------------------
-- Certified node sets: public verifier configuration

record NodeSet (d : ℕ) : Set where
  constructor nodeSet
  field
    nodes weights : Vec Carrier (suc d)
    certified : L.Certified (lookup nodes) (lookup weights)
open NodeSet public

-- Weights are validated independently of the prover (O(m²) ring operations).
certify? : {d : ℕ} (xs ws : Vec Carrier (suc d)) → Dec (L.Certified (lookup xs) (lookup ws))
certify? xs ws = Fin.all? (λ i → (lookup ws i * L.omitted (lookup xs) i (lookup xs i)) ≟ 1#)

------------------------------------------------------------------------
-- Scalar barycentric evaluation in O(m) ring operations
--
-- One pass carries the prefix product acc = ∏_{j<i} (r - x_j) forward and
-- returns the suffix product ∏_{j≥i} (r - x_j) backward, so each omitted
-- product ∏_{j≠i} (r - x_j) = prefix · suffix costs one multiplication.
-- No division by r - x_i occurs, so nodes need no special case.

sweep : {n : ℕ} → Carrier → Carrier → Vec Carrier n → Vec Carrier n → Vec Carrier n →
  Carrier × Carrier
sweep r acc [] [] [] = 0# , 1#
sweep r acc (x ∷ xs) (w ∷ ws) (y ∷ ys) = combine (sweep r (times acc (diff r x)) xs ws ys)
  where
  combine : Carrier × Carrier → Carrier × Carrier
  combine (s , p) = plus (times (times y w) (times acc p)) s , times (diff r x) p

evalAt : {d : ℕ} (xs ws ys : Vec Carrier (suc d)) → Carrier → Carrier
evalAt xs ws ys r = proj₁ (sweep r 1# xs ws ys)

sweep-product : {n : ℕ} (r acc : Carrier) (xs ws ys : Vec Carrier n) →
  proj₂ (sweep r acc xs ws ys) ≈ L.Π.sum (λ j → r - lookup xs j)
sweep-product r acc [] [] [] = refl
sweep-product r acc (x ∷ xs) (w ∷ ws) (y ∷ ys) =
  trans (normalize-≈ _) (*-cong (diff-≈ r x) (sweep-product r _ xs ws ys))

sweep-sum : {n : ℕ} (r acc : Carrier) (xs ws ys : Vec Carrier (suc n)) →
  proj₁ (sweep r acc xs ws ys) ≈
  L.Σ.sum (λ i → (lookup ys i * lookup ws i) * (acc * L.omitted (lookup xs) i r))
sweep-sum {zero} r acc (x ∷ []) (w ∷ []) (y ∷ []) =
  trans (normalize-≈ _) (+-congʳ (trans (normalize-≈ _)
    (*-cong (normalize-≈ _) (normalize-≈ _))))
sweep-sum {suc n} r acc (x ∷ xs) (w ∷ ws) (y ∷ ys) =
  trans (normalize-≈ _) (+-cong first rest)
  where
  acc' = times acc (diff r x)
  ℓ = L.omitted (lookup (x ∷ xs))

  first : times (times y w) (times acc (proj₂ (sweep r acc' xs ws ys))) ≈ (y * w) * (acc * ℓ zero r)
  first = trans (normalize-≈ _) (*-cong (normalize-≈ _)
    (trans (normalize-≈ _) (*-congˡ (sweep-product r acc' xs ws ys))))

  shift : (i : Fin (suc n)) → acc' * L.omitted (lookup xs) i r ≈ acc * ℓ (suc i) r
  shift i = trans (*-congʳ (trans (normalize-≈ _) (*-congˡ (diff-≈ r x))))
    (*-assoc acc (r - x) (L.omitted (lookup xs) i r))

  rest : proj₁ (sweep r acc' xs ws ys) ≈
    L.Σ.sum (λ i → (lookup ys i * lookup ws i) * (acc * ℓ (suc i) r))
  rest = trans (sweep-sum r acc' xs ws ys) (Σ-cong
    (λ i → (lookup ys i * lookup ws i) * (acc' * L.omitted (lookup xs) i r))
    (λ i → (lookup ys i * lookup ws i) * (acc * ℓ (suc i) r))
    (λ i → *-congˡ (shift i)))

evalAt-correct : {d : ℕ} (xs ws ys : Vec Carrier (suc d)) (r : Carrier) →
  evalAt xs ws ys r ≈ L.lagrange (lookup xs) (lookup ws) (lookup ys) r
evalAt-correct xs ws ys r = trans (sweep-sum r 1# xs ws ys) (Σ-cong
  (λ i → (lookup ys i * lookup ws i) * (1# * L.omitted (lookup xs) i r))
  (λ i → lookup ys i * (lookup ws i * L.omitted (lookup xs) i r))
  (λ i → trans (*-congˡ (*-identityˡ (L.omitted (lookup xs) i r)))
    (*-assoc (lookup ys i) (lookup ws i) (L.omitted (lookup xs) i r))))

-- Evaluation with a node set.
evaluate : {d : ℕ} → NodeSet d → Vec Carrier (suc d) → Carrier → Carrier
evaluate ns ys r = evalAt (nodes ns) (weights ns) ys r

evaluate-node : {d : ℕ} (ns : NodeSet d) (ys : Vec Carrier (suc d)) (k : Fin (suc d)) →
  evaluate ns ys (lookup (nodes ns) k) ≈ lookup ys k
evaluate-node ns ys k = trans (evalAt-correct (nodes ns) (weights ns) ys _)
  (L.lagrange-node (certified ns) (lookup ys) k)

evaluate-cong : {d : ℕ} (ns : NodeSet d) {ys ys' : Vec Carrier (suc d)} {r r' : Carrier} →
  (∀ i → lookup ys i ≈ lookup ys' i) → r ≈ r' → evaluate ns ys r ≈ evaluate ns ys' r'
evaluate-cong ns {ys} {ys'} yy rr = trans (evalAt-correct (nodes ns) (weights ns) ys _)
  (trans (L.lagrange-cong {x = lookup (nodes ns)} {x' = lookup (nodes ns)}
      {w = lookup (weights ns)} {w' = lookup (weights ns)} {y = lookup ys} {y' = lookup ys'}
      (λ _ → refl) (λ _ → refl) yy rr)
    (sym (evalAt-correct (nodes ns) (weights ns) ys' _)))

------------------------------------------------------------------------
-- Degree 0 and degree 1 as special cases

constantNodes : Carrier → NodeSet 0
constantNodes c = nodeSet (c ∷ []) (1# ∷ []) λ { zero → *-identityʳ 1# }

evaluate-constant : (c : Carrier) (ys : Vec Carrier 1) (r : Carrier) →
  evaluate (constantNodes c) ys r ≈ lookup ys zero
evaluate-constant c ys r = trans (evalAt-correct (c ∷ []) (1# ∷ []) ys r)
  (L.lagrange-constant {x = lookup (c ∷ [])} {w = lookup (1# ∷ [])} (certified (constantNodes c)) (lookup ys) r)

linearNodes : NodeSet 1
linearNodes = nodeSet (0# ∷ 1# ∷ []) (- 1# ∷ 1# ∷ [])
  λ { zero → L.certified01 zero ; (suc zero) → L.certified01 (suc zero) }

-- At nodes 0, 1 the evaluator is the existing two-endpoint interpolation.
evaluate-linear : (a b r : Carrier) →
  evaluate linearNodes (a ∷ b ∷ []) r ≈ Wire.interpolate op a b r
evaluate-linear a b r = trans (evalAt-correct (0# ∷ 1# ∷ []) (- 1# ∷ 1# ∷ []) (a ∷ b ∷ []) r)
  (trans (L.lagrange-cong {y = lookup (a ∷ b ∷ [])} {y' = lookup (a ∷ b ∷ [])}
      nodes≈ weights≈ (λ _ → refl) refl)
    (trans (L.lagrange01 (lookup (a ∷ b ∷ [])) r) (sym (normalize-≈ _))))
  where
  nodes≈ : ∀ i → lookup (0# ∷ 1# ∷ []) i ≈ L.nodes01 i
  nodes≈ zero = refl
  nodes≈ (suc zero) = refl
  weights≈ : ∀ i → lookup (- 1# ∷ 1# ∷ []) i ≈ L.weights01 i
  weights≈ zero = refl
  weights≈ (suc zero) = refl

------------------------------------------------------------------------
-- Proof-side decoding into a Lagrange circuit
--
-- The interpolant is a sum tree with one leaf per basis term, since
-- Circuit.Protocol.degree adds occurrence counts inside UAdd. Each leaf has
-- exactly d occurrences of the round variable.

basisU : {n : ℕ} → Vector Carrier n → C.Univariate Carrier
basisU {zero} f = C.Value 1#
basisU {suc n} f = C.UMul (C.UAdd C.UVar (C.UNeg (C.Value (f zero)))) (basisU (λ j → f (suc j)))

term : {d : ℕ} (x w y : Vector Carrier (suc d)) → Fin (suc d) → C.Univariate Carrier
term x w y i = C.UMul (C.Value (y i * w i)) (basisU (removeAt x i))

sumTree : {n : ℕ} → (Fin (suc n) → C.Message Carrier) → C.Message Carrier
sumTree {zero} f = f zero
sumTree {suc n} f = C.Branch (f zero) (sumTree (λ i → f (suc i)))

decode : {d : ℕ} → NodeSet d → Vec Carrier (suc d) → C.Message Carrier
decode ns ys = sumTree (λ i → C.Leaf (term (lookup (nodes ns)) (lookup (weights ns)) (lookup ys) i))

-- Degree
private
  below : (n : ℕ) → (n <ᵇ suc n) ≡ true
  below zero = P.refl
  below (suc n) = below n

  not-below : (n : ℕ) → (n <ᵇ n) ≡ false
  not-below zero = P.refl
  not-below (suc n) = not-below n

basisU-degree : {n : ℕ} (f : Vector Carrier n) → C.degree (basisU f) ≡ n
basisU-degree {zero} f = P.refl
basisU-degree {suc n} f = cong suc (basisU-degree (λ j → f (suc j)))

sumTree-degree : {n : ℕ} (d : ℕ) (f : Fin (suc n) → C.Message Carrier) →
  (∀ i → C.degreeOK d (f i) ≡ true) → C.degreeOK d (sumTree f) ≡ true
sumTree-degree {zero} d f h = h zero
sumTree-degree {suc n} d f h = cong₂ _∧_ (h zero) (sumTree-degree d (λ i → f (suc i)) (λ i → h (suc i)))

decode-degree : {d : ℕ} (ns : NodeSet d) (ys : Vec Carrier (suc d)) →
  C.degreeOK d (decode ns ys) ≡ true
decode-degree {d} ns ys = sumTree-degree d _ λ i →
  P.trans (cong (_<ᵇ suc d) (basisU-degree (removeAt (lookup (nodes ns)) i))) (below d)

-- Evaluation
basisU-eval : {n : ℕ} (f : Vector Carrier n) (r : Carrier) →
  C.evaluateU op (basisU f) r ≈ L.Π.sum (λ j → r - f j)
basisU-eval {zero} f r = refl
basisU-eval {suc n} f r =
  trans (normalize-≈ _) (*-cong (diff-≈ r (f zero)) (basisU-eval (λ j → f (suc j)) r))

sumTree-eval : {n : ℕ} (f : Fin (suc n) → C.Message Carrier) (r : Carrier) →
  C.evaluateMessage op (sumTree f) r ≈ L.Σ.sum (λ i → C.evaluateMessage op (f i) r)
sumTree-eval {zero} f r = sym (+-identityʳ _)
sumTree-eval {suc n} f r = trans (normalize-≈ _) (+-congˡ (sumTree-eval (λ i → f (suc i)) r))

decode-eval : {d : ℕ} (ns : NodeSet d) (ys : Vec Carrier (suc d)) (r : Carrier) →
  C.evaluateMessage op (decode ns ys) r ≈ L.lagrange (lookup (nodes ns)) (lookup (weights ns)) (lookup ys) r
decode-eval ns ys r = trans (sumTree-eval (λ i → C.Leaf (term x w y i)) r) (Σ-cong
  (λ i → C.evaluateMessage op (C.Leaf (term x w y i)) r)
  (λ i → y i * (w i * L.omitted x i r))
  (λ i → trans (trans (normalize-≈ _) (*-congˡ (basisU-eval (removeAt x i) r)))
    (*-assoc (y i) (w i) (L.omitted x i r))))
  where
  x = lookup (nodes ns)
  w = lookup (weights ns)
  y = lookup ys

decode-evaluate : {d : ℕ} (ns : NodeSet d) (ys : Vec Carrier (suc d)) (r : Carrier) →
  evaluate ns ys r ≈ C.evaluateMessage op (decode ns ys) r
decode-evaluate ns ys r =
  trans (evalAt-correct (nodes ns) (weights ns) ys r) (sym (decode-eval ns ys r))

-- The decoded circuit passes through every received value.
decode-node : {d : ℕ} (ns : NodeSet d) (ys : Vec Carrier (suc d)) (k : Fin (suc d)) →
  C.evaluateMessage op (decode ns ys) (lookup (nodes ns) k) ≈ lookup ys k
decode-node ns ys k = trans (sym (decode-evaluate ns ys _)) (evaluate-node ns ys k)

------------------------------------------------------------------------
-- External boundary: a received list becomes a tuple only at its exact length

exactly : {A : Set} (n : ℕ) → List A → Maybe (Vec A n)
exactly zero [] = just []
exactly zero (_ ∷ _) = nothing
exactly (suc n) [] = nothing
exactly (suc n) (a ∷ as) = Maybe.map (a ∷_) (exactly n as)

-- Accepted tuples are the received lists, multiplicities and order included.
exactly-sound : {A : Set} (n : ℕ) (xs : List A) {v : Vec A n} →
  exactly n xs ≡ just v → toList v ≡ xs
exactly-sound zero [] P.refl = P.refl
exactly-sound (suc n) (a ∷ as) h with exactly n as in e
exactly-sound (suc n) (a ∷ as) P.refl | just v = cong (a ∷_) (exactly-sound n as e)

------------------------------------------------------------------------
-- Executable verifier: one public node set per round, Boolean domain

Config : Set
Config = Σ ℕ NodeSet

roundSum : {d : ℕ} → NodeSet d → Vec Carrier (suc d) → Carrier
roundSum ns ys = plus (evaluate ns ys 0#) (evaluate ns ys 1#)

mutual
  run : (List Carrier → Carrier) → List Carrier → Carrier → List Config →
    List (List Carrier) → List Carrier → Bool
  run oracle prefix claim [] [] [] = same op claim (oracle prefix)
  run oracle prefix claim [] [] (_ ∷ _) = false
  run oracle prefix claim [] (_ ∷ _) _ = false
  run oracle prefix claim (_ ∷ _) [] _ = false
  run oracle prefix claim (_ ∷ _) (_ ∷ _) [] = false
  run oracle prefix claim ((d , ns) ∷ cs) (m ∷ ms) (r ∷ rs) =
    runTuple oracle prefix claim ns (exactly (suc d) m) cs ms r rs

  runTuple : {d : ℕ} → (List Carrier → Carrier) → List Carrier → Carrier → NodeSet d →
    Maybe (Vec Carrier (suc d)) → List Config → List (List Carrier) → Carrier → List Carrier → Bool
  runTuple oracle prefix claim ns nothing cs ms r rs = false
  runTuple oracle prefix claim ns (just ys) cs ms r rs =
    same op claim (roundSum ns ys) ∧ run oracle (prefix ∷ʳ r) (evaluate ns ys r) cs ms rs

-- The number of rounds is the number of configurations.
verify : (List Carrier → Carrier) → List Config → Carrier →
  List (List Carrier) → List Carrier → Bool
verify oracle configs claim messages challenges = run oracle [] claim configs messages challenges

------------------------------------------------------------------------
-- Decoding received lists for the circuit verifier

-- A circuit of degree d + 1: rejected by the degree check at bound d.
power : ℕ → C.Univariate Carrier
power zero = C.Value 1#
power (suc k) = C.UMul C.UVar (power k)

reject : ℕ → C.Message Carrier
reject d = C.Leaf (power (suc d))

power-degree : (k : ℕ) → C.degree (power k) ≡ k
power-degree zero = P.refl
power-degree (suc k) = cong suc (power-degree k)

reject-rejected : (d : ℕ) → C.degreeOK d (reject d) ≡ false
reject-rejected d = P.trans (cong (_<ᵇ suc d) (power-degree (suc d))) (not-below (suc d))

decodeTuple : {d : ℕ} → NodeSet d → Maybe (Vec Carrier (suc d)) → C.Message Carrier
decodeTuple {d} ns nothing = reject d
decodeTuple ns (just ys) = decode ns ys

decodeList : Config → List Carrier → C.Message Carrier
decodeList (d , ns) m = decodeTuple ns (exactly (suc d) m)

------------------------------------------------------------------------
-- Representation theorem: for a uniform degree bound d, on the Boolean
-- domain, with the same final oracle, the evaluation-form verdict equals
-- the circuit verdict for every list of received lists and challenges.

private
  true-left : {t : Bool} (z : Bool) → t ≡ true → z ≡ t ∧ z
  true-left z P.refl = P.refl

  false-mid : (b : Bool) {t : Bool} (z : Bool) → t ≡ false → false ≡ b ∧ (t ∧ z)
  false-mid b z P.refl = P.sym (∧-zeroʳ b)

round-sum : {d : ℕ} (ns : NodeSet d) (ys : Vec Carrier (suc d)) →
  roundSum ns ys ≈ plus (C.evaluateMessage op (decode ns ys) 0#)
    (C.evaluateMessage op (decode ns ys) 1#)
round-sum ns ys = nf-cong (+-cong (decode-evaluate ns ys 0#) (decode-evaluate ns ys 1#))

-- The interactive round check agrees.
round-equivalent : {d : ℕ} (ns : NodeSet d) (claim : Carrier) (ys : Vec Carrier (suc d)) →
  same op claim (roundSum ns ys) ≡ C.checkRound op 0# _ claim (decode ns ys)
round-equivalent ns claim ys =
  P.trans (same-cong refl (round-sum ns ys)) (true-left _ (decode-degree ns ys))

module _ {d : ℕ} (ns : NodeSet d) (oracle : List Carrier → Carrier) where

  run-equivalent : (prefix : List Carrier) (x y : Carrier) → x ≈ y →
    (n : ℕ) (ms : List (List Carrier)) (rs : List Carrier) →
    run oracle prefix x (replicate n (d , ns)) ms rs ≡
    (n ≡ᵇ length ms) ∧ C.verifyWith op 0# oracle d prefix y (map (decodeList (d , ns)) ms) rs
  run-equivalent prefix x y xy zero [] [] = same-cong xy refl
  run-equivalent prefix x y xy zero [] (_ ∷ _) = P.refl
  run-equivalent prefix x y xy zero (_ ∷ _) rs = P.refl
  run-equivalent prefix x y xy (suc n) [] rs = P.refl
  run-equivalent prefix x y xy (suc n) (m ∷ ms) [] = P.sym (∧-zeroʳ (n ≡ᵇ length ms))
  run-equivalent prefix x y xy (suc n) (m ∷ ms) (r ∷ rs) = tuple (exactly (suc d) m)
    where
    b = n ≡ᵇ length ms
    rest = map (decodeList (d , ns)) ms

    tuple : (t : Maybe (Vec Carrier (suc d))) →
      runTuple oracle prefix x ns t (replicate n (d , ns)) ms r rs ≡
      b ∧ C.verifyWith op 0# oracle d prefix y (decodeTuple ns t ∷ rest) (r ∷ rs)
    tuple nothing = false-mid b _ (reject-rejected d)
    tuple (just ys) =
      P.trans (cong (same op x (roundSum ns ys) ∧_)
        (run-equivalent (prefix ∷ʳ r) (evaluate ns ys r) e (decode-evaluate ns ys r) n ms rs))
      (P.trans (x∙yz≈y∙xz (same op x (roundSum ns ys)) b vw)
      (cong (b ∧_) (P.trans (cong (_∧ vw) (same-cong xy (round-sum ns ys)))
        (true-left _ (decode-degree ns ys)))))
      where
      e = C.evaluateMessage op (decode ns ys) r
      vw = C.verifyWith op 0# oracle d (prefix ∷ʳ r) e rest rs

  verify-equivalent : (n : ℕ) (claim : Carrier) (ms : List (List Carrier)) (rs : List Carrier) →
    verify oracle (replicate n (d , ns)) claim ms rs ≡
    C.verify op 0# oracle n d claim (map (decodeList (d , ns)) ms) rs
  verify-equivalent n claim ms rs = P.trans (run-equivalent [] claim claim refl n ms rs)
    (cong (λ k → (n ≡ᵇ k) ∧ C.verifyWith op 0# oracle d [] claim (map (decodeList (d , ns)) ms) rs)
      (P.sym (length-map (decodeList (d , ns)) ms)))
