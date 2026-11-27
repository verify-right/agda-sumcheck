{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)

-- Coefficients and node values of polynomials with d + 1 coefficients are
-- isomorphic, for nodes whose Lagrange weights are certified. Over a
-- commutative ring the certificate makes every node difference a unit;
-- uniqueness then follows by synthetic division by the monic X - x₀ and
-- cancellation of those units. No field, no 0 ≠ 1 and no root count is used,
-- so the argument also holds in rings with zero divisors (e.g. ℤ/15).
--
-- Route chosen: monic synthetic division (quotient, quotient-zero) already
-- exists in the dense polynomial library, so a Newton-basis triangular
-- argument would add machinery without shortening the proof.
module Ring.LagrangeInverse (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R hiding (zero)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
import Data.Fin.Properties as Fin
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Vec.Functional using (Vector; removeAt)
open import Data.Empty using (⊥-elim)
open import Function.Bundles using (Inverse)
import Function.Consequences.Setoid as Consequences
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as P using (_≢_)
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VecEquality
open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup using (x∙yz≈y∙xz)
open import Ring.DensePolynomialLaws R
import Ring.Lagrange as Lagrange
open import Relation.Binary.Reasoning.Setoid setoid

private
  module L = Lagrange R

------------------------------------------------------------------------
-- 1. Certified weights make node differences units

UnitDifferences : {d : ℕ} → Vector Carrier (suc d) → Set
UnitDifferences x = ∀ i j → i ≢ j → ∃[ u ] ((x i - x j) * u ≈ 1#)

unit-differences : {d : ℕ} {x w : Vector Carrier (suc d)} → L.Certified x w → UnitDifferences x
unit-differences {zero} certified zero zero i≢j = ⊥-elim (i≢j P.refl)
unit-differences {suc d} {x} {w} certified i j i≢j = w i * L.Π.sum (removeAt v k) , (begin
  (x i - x j) * (w i * rest)       ≈⟨ x∙yz≈y∙xz (x i - x j) (w i) rest ⟩
  w i * ((x i - x j) * rest)       ≈⟨ *-congˡ (*-congʳ factor) ⟨
  w i * (v k * rest)               ≈⟨ *-congˡ (L.Π.sum-remove {i = k} v) ⟨
  w i * L.Π.sum v                  ≈⟨ certified i ⟩
  1# ∎)
  where
  v = removeAt (λ m → x i - x m) i
  k = punchOut i≢j
  rest = L.Π.sum (removeAt v k)
  factor : v k ≈ x i - x j
  factor = +-congˡ (-‿cong (reflexive (P.cong x (Fin.punchIn-punchOut i≢j))))

-- Cancellation of a unit.
cancel-unit : {a b u : Carrier} → a * u ≈ 1# → a * b ≈ 0# → b ≈ 0#
cancel-unit {a} {b} {u} au ab = begin
  b               ≈⟨ *-identityˡ b ⟨
  1# * b          ≈⟨ *-congʳ au ⟨
  (a * u) * b     ≈⟨ *-congʳ (*-comm a u) ⟩
  (u * a) * b     ≈⟨ *-assoc u a b ⟩
  u * (a * b)     ≈⟨ *-congˡ ab ⟩
  u * 0#          ≈⟨ zeroʳ u ⟩
  0# ∎

------------------------------------------------------------------------
-- 2. Coefficient equality (representation bound, not semantic degree)

-- Inductive, so that its indices are determined by its constructors.
infix 4 _≋_
infixr 5 _▹≋_
data _≋_ : {n : ℕ} → Poly n → Poly n → Set where
  con≋ : {a b : Carrier} → a ≈ b → con a ≋ con b
  _▹≋_ : {n : ℕ} {a b : Carrier} {p q : Poly n} → a ≈ b → p ≋ q → (a ▹ p) ≋ (b ▹ q)

≋-refl : {n : ℕ} (p : Poly n) → p ≋ p
≋-refl (con a) = con≋ refl
≋-refl (a ▹ p) = refl ▹≋ ≋-refl p

≋-sym : {n : ℕ} {p q : Poly n} → p ≋ q → q ≋ p
≋-sym (con≋ h) = con≋ (sym h)
≋-sym (h ▹≋ t) = sym h ▹≋ ≋-sym t

≋-trans : {n : ℕ} {p q s : Poly n} → p ≋ q → q ≋ s → p ≋ s
≋-trans (con≋ h) (con≋ g) = con≋ (trans h g)
≋-trans (h ▹≋ t) (g ▹≋ u) = trans h g ▹≋ ≋-trans t u

Coefficients : ℕ → Setoid 0ℓ 0ℓ
Coefficients n = record
  { Carrier = Poly n ; _≈_ = _≋_
  ; isEquivalence = record { refl = ≋-refl _ ; sym = ≋-sym ; trans = ≋-trans } }

eval-cong : {n : ℕ} {p q : Poly n} → p ≋ q → (r : Carrier) → eval p r ≈ eval q r
eval-cong (con≋ h) r = h
eval-cong (h ▹≋ t) r = +-cong h (*-congˡ (eval-cong t r))

------------------------------------------------------------------------
-- Zero polynomials. Adapted from quest15.13 PolynomialRoots.agda
-- (Zero, zero-evaluates, head-eval, quotient-zero), without its counting
-- and integral-domain parts.

Zero : {n : ℕ} → Poly n → Set
Zero (con a) = a ≈ 0#
Zero (a ▹ p) = (a ≈ 0#) × Zero p

zero-evaluates : {n : ℕ} (p : Poly n) → Zero p → (x : Carrier) → eval p x ≈ 0#
zero-evaluates (con a) h x = h
zero-evaluates (a ▹ p) (a0 , p0) x = trans (+-cong a0 (*-congˡ (zero-evaluates p p0 x)))
  (trans (+-congˡ (zeroʳ x)) (+-identityˡ 0#))

head-eval : {n : ℕ} (a : Carrier) (p : Poly n) (r : Carrier) → Zero p → eval (a ▹ p) r ≈ a
head-eval a p r p0 = trans (+-congˡ (*-congˡ (zero-evaluates p p0 r)))
  (trans (+-congˡ (zeroʳ r)) (+-identityʳ a))

-- At a root, a zero quotient forces every original coefficient to be zero.
quotient-zero : {n : ℕ} (p : Poly (suc n)) (r : Carrier) → eval p r ≈ 0# →
  Zero (quotient p r) → Zero p
quotient-zero (a ▹ con b) r root b0 = trans (sym (head-eval a (con b) r b0)) root , b0
quotient-zero (a ▹ (b ▹ p)) r root (tail-root , q0) =
  trans (sym (head-eval a (b ▹ p) r tail-zero)) root , tail-zero
  where
  tail-zero = quotient-zero (b ▹ p) r tail-root q0

zero-difference : {n : ℕ} (p q : Poly n) → Zero (addP p (negP q)) → p ≋ q
zero-difference (con a) (con b) h = con≋ (subtract-zero a b h)
zero-difference (a ▹ p) (b ▹ q) (h , t) = subtract-zero a b h ▹≋ zero-difference p q t

------------------------------------------------------------------------
-- 3. Synthetic division by the monic X - a, as a coefficient identity

-- Add a constant to the constant coefficient.
addHead : {n : ℕ} → Carrier → Poly n → Poly n
addHead c (con a) = con (c + a)
addHead c (a ▹ p) = (c + a) ▹ p

-- (X - a) · q, computed coefficientwise.
linearTimes : {n : ℕ} → Carrier → Poly n → Poly (suc n)
linearTimes a (con b) = (- (a * b)) ▹ con b
linearTimes a (b ▹ q) = (- (a * b)) ▹ addHead b (linearTimes a q)

addHead-eval : {n : ℕ} (c : Carrier) (p : Poly n) (x : Carrier) → eval (addHead c p) x ≈ c + eval p x
addHead-eval c (con a) x = refl
addHead-eval c (a ▹ p) x = +-assoc c a (x * eval p x)

linearTimes-eval : {n : ℕ} (a : Carrier) (q : Poly n) (x : Carrier) →
  eval (linearTimes a q) x ≈ (x - a) * eval q x
linearTimes-eval a (con b) x = begin
  - (a * b) + x * b      ≈⟨ +-comm _ _ ⟩
  x * b + - (a * b)      ≈⟨ +-congˡ (-‿distribˡ-* a b) ⟩
  x * b + (- a) * b      ≈⟨ distribʳ b x (- a) ⟨
  (x - a) * b ∎
  where open import Algebra.Properties.Ring ring using (-‿distribˡ-*)
linearTimes-eval a (b ▹ q) x = begin
  - (a * b) + x * eval (addHead b (linearTimes a q)) x
    ≈⟨ +-congˡ (*-congˡ (trans (addHead-eval b (linearTimes a q) x)
         (+-congˡ (linearTimes-eval a q x)))) ⟩
  - (a * b) + x * (b + (x - a) * eval q x)
    ≈⟨ +-congˡ (distribˡ x b _) ⟩
  - (a * b) + (x * b + x * ((x - a) * eval q x))
    ≈⟨ +-assoc _ _ _ ⟨
  (- (a * b) + x * b) + x * ((x - a) * eval q x)
    ≈⟨ +-cong (linearTimes-eval a (con b) x) (x∙yz≈y∙xz x (x - a) (eval q x)) ⟩
  (x - a) * b + (x - a) * (x * eval q x)
    ≈⟨ distribˡ (x - a) b (x * eval q x) ⟨
  (x - a) * (b + x * eval q x) ∎

-- p = (X - a) · quotient p a + p(a), coefficient by coefficient.
private
  add-sub : (c t : Carrier) → c ≈ (c + t) + - t
  add-sub c t = sym (trans (+-assoc c t (- t)) (trans (+-congˡ (-‿inverseʳ t)) (+-identityʳ c)))

synthetic-divide-correct : {n : ℕ} (p : Poly (suc n)) (a : Carrier) →
  p ≋ addHead (eval p a) (linearTimes a (quotient p a))
synthetic-divide-correct (c ▹ con b) a = add-sub c (a * b) ▹≋ con≋ refl
synthetic-divide-correct (c ▹ (b ▹ p)) a =
  add-sub c (a * eval (b ▹ p) a) ▹≋ synthetic-divide-correct (b ▹ p) a

-- Evaluation consequence: p(x) = (x - a) q(x) + p(a).
synthetic-divide-eval : {n : ℕ} (p : Poly (suc n)) (a x : Carrier) →
  eval p x ≈ (x - a) * eval (quotient p a) x + eval p a
synthetic-divide-eval p a x =
  trans (eval-cong (synthetic-divide-correct p a) x)
    (trans (addHead-eval (eval p a) (linearTimes a (quotient p a)) x)
      (trans (+-comm _ _) (+-congʳ (linearTimes-eval a (quotient p a) x))))

------------------------------------------------------------------------
-- 4. Uniqueness: a polynomial vanishing at d + 1 nodes with unit
-- differences has zero coefficients

vanishing-zero : {d : ℕ} (x : Vector Carrier (suc d)) → UnitDifferences x →
  (p : Poly d) → (∀ i → eval p (x i) ≈ 0#) → Zero p
vanishing-zero {zero} x units (con a) h = h zero
vanishing-zero {suc d} x units p h =
  quotient-zero p (x zero) (h zero)
    (vanishing-zero (λ j → x (suc j)) units′ q (λ j → q-vanishes j))
  where
  q = quotient p (x zero)
  units′ : UnitDifferences (λ j → x (suc j))
  units′ i j i≢j = units (suc i) (suc j) (λ e → i≢j (Fin.suc-injective e))
  q-vanishes : ∀ j → eval q (x (suc j)) ≈ 0#
  q-vanishes j = cancel-unit (proj₂ (units (suc j) zero (λ ()))) (begin
    (x (suc j) - x zero) * eval q (x (suc j))
      ≈⟨ +-identityʳ _ ⟨
    (x (suc j) - x zero) * eval q (x (suc j)) + 0#
      ≈⟨ +-congˡ (h zero) ⟨
    (x (suc j) - x zero) * eval q (x (suc j)) + eval p (x zero)
      ≈⟨ synthetic-divide-eval p (x zero) (x (suc j)) ⟨
    eval p (x (suc j))
      ≈⟨ h (suc j) ⟩
    0# ∎)

eval-injective : {d : ℕ} {x : Vector Carrier (suc d)} → UnitDifferences x →
  (p q : Poly d) → (∀ i → eval p (x i) ≈ eval q (x i)) → p ≋ q
eval-injective {x = x} units p q h = zero-difference p q (vanishing-zero x units (addP p (negP q)) λ i →
  trans (add-eval p (negP q) (x i))
    (trans (+-congˡ (neg-eval q (x i))) (subtract-equal _ _ (h i))))

------------------------------------------------------------------------
-- 5. Coefficients of the Lagrange interpolant

linearP : Carrier → Poly 1
linearP a = (- a) ▹ con 1#

basisP : {n : ℕ} → Vector Carrier n → Poly n
basisP {zero} f = con 1#
basisP {suc n} f = mulP (linearP (f zero)) (basisP (λ j → f (suc j)))

sumP : {d n : ℕ} → Vector (Poly d) n → Poly d
sumP {d} {zero} f = zeroP d
sumP {d} {suc n} f = addP (f zero) (sumP (λ i → f (suc i)))

interpolant : {d : ℕ} (x w y : Vector Carrier (suc d)) → Poly d
interpolant x w y = sumP (λ i → scale (y i * w i) (basisP (removeAt x i)))

basisP-eval : {n : ℕ} (f : Vector Carrier n) (r : Carrier) →
  eval (basisP f) r ≈ L.Π.sum (λ j → r - f j)
basisP-eval {zero} f r = refl
basisP-eval {suc n} f r = trans (mul-eval (linearP (f zero)) (basisP (λ j → f (suc j))) r)
  (*-cong (trans (+-comm _ _) (+-congʳ (*-identityʳ r))) (basisP-eval (λ j → f (suc j)) r))

sumP-eval : {d n : ℕ} (f : Vector (Poly d) n) (r : Carrier) →
  eval (sumP f) r ≈ L.Σ.sum (λ i → eval (f i) r)
sumP-eval {d} {zero} f r = zero-eval d r
sumP-eval {d} {suc n} f r = trans (add-eval (f zero) (sumP (λ i → f (suc i))) r)
  (+-congˡ (sumP-eval (λ i → f (suc i)) r))

interpolant-eval : {d : ℕ} (x w y : Vector Carrier (suc d)) (r : Carrier) →
  eval (interpolant x w y) r ≈ L.lagrange x w y r
interpolant-eval x w y r = trans (sumP-eval term r) (L.Σ.sum-cong-≋ {x = λ i → eval (term i) r}
  {y = λ i → y i * L.basis x w i r} λ i →
    trans (scale-eval (y i * w i) (basisP (removeAt x i)) r)
      (trans (*-congˡ (basisP-eval (removeAt x i) r)) (*-assoc (y i) (w i) _)))
  where
  term = λ i → scale (y i * w i) (basisP (removeAt x i))

------------------------------------------------------------------------
-- 6. The coefficient–evaluation isomorphism

Values : ℕ → Setoid 0ℓ 0ℓ
Values n = VecEquality.≋-setoid setoid n

module _ {d : ℕ} {x w : Vector Carrier (suc d)} (certified : L.Certified x w) where

  private
    units = unit-differences {x = x} {w} certified

  evaluations : Poly d → Vector Carrier (suc d)
  evaluations p i = eval p (x i)

  interpolate : Vector Carrier (suc d) → Poly d
  interpolate = interpolant x w

  -- Evaluation after interpolation returns the input values.
  evaluate-interpolate : (y : Vector Carrier (suc d)) (i : Fin (suc d)) →
    evaluations (interpolate y) i ≈ y i
  evaluate-interpolate y i = trans (interpolant-eval x w y (x i)) (L.lagrange-node certified y i)

  -- Interpolation after evaluation returns the input coefficients.
  interpolate-evaluate : (p : Poly d) → interpolate (evaluations p) ≋ p
  interpolate-evaluate p = eval-injective units _ p (evaluate-interpolate (evaluations p))

  coefficient-evaluation : Inverse (Coefficients d) (Values (suc d))
  coefficient-evaluation = record
    { to = evaluations
    ; from = interpolate
    ; to-cong = to-cong
    ; from-cong = from-cong
    ; inverse = C.strictlyInverseˡ⇒inverseˡ {f = evaluations} {f⁻¹ = interpolate}
                  to-cong evaluate-interpolate
            , C.strictlyInverseʳ⇒inverseʳ {f⁻¹ = interpolate} {f = evaluations}
                  from-cong interpolate-evaluate
    }
    where
    module C = Consequences (Coefficients d) (Values (suc d))
    to-cong : {p q : Poly d} → p ≋ q → (i : Fin (suc d)) → evaluations p i ≈ evaluations q i
    to-cong h i = eval-cong h (x i)
    from-cong : {y y' : Vector Carrier (suc d)} → (∀ i → y i ≈ y' i) → interpolate y ≋ interpolate y'
    from-cong {y} {y'} h = eval-injective units _ _ λ i →
      trans (evaluate-interpolate y i) (trans (h i) (sym (evaluate-interpolate y' i)))

-- Evaluation is additive and scalar-linear (dense polynomial laws).
evaluations-add : {d : ℕ} (x : Vector Carrier (suc d)) (p q : Poly d) (i : Fin (suc d)) →
  eval (addP p q) (x i) ≈ eval p (x i) + eval q (x i)
evaluations-add x p q i = add-eval p q (x i)

evaluations-scale : {d : ℕ} (x : Vector Carrier (suc d)) (a : Carrier) (p : Poly d) (i : Fin (suc d)) →
  eval (scale a p) (x i) ≈ a * eval p (x i)
evaluations-scale x a p i = scale-eval a p (x i)
