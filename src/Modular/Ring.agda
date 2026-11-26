{-# OPTIONS --safe --without-K #-}
open import Agda.Builtin.Nat using (Nat)
module Modular.Ring (k : Nat) where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (zero; suc; _+_; _-_; _*_; _==_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as DivMod
open import Data.Product using (_,_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (sym; trans; cong; cong₂)
open import Algebra.Bundles using (CommutativeRing)
open import Modular.Operations using (modulus; normalize; negative; same)

private
  p : Nat
  p = modulus k

infix 4 _≈_
_≈_ : Nat → Nat → Set
x ≈ y = normalize k x ≡ normalize k y

-- The implementation's normalize is definitionally stdlib's remainder.
-- The two distributivity lemmas below are imported, not reproved.
remainder-idem : (x : Nat) → normalize k (normalize k x) ≡ normalize k x
remainder-idem x = DivMod.m%n%n≡m%n x p

add-remainder : (x y : Nat) → normalize k (x + y) ≡ normalize k (normalize k x + normalize k y)
add-remainder x y = DivMod.%-distribˡ-+ x y p

mul-remainder : (x y : Nat) → normalize k (x * y) ≡ normalize k (normalize k x * normalize k y)
mul-remainder x y = DivMod.%-distribˡ-* x y p

+-cong : {x x' y y' : Nat} → x ≈ x' → y ≈ y' → (x + y) ≈ (x' + y')
+-cong {x} {x'} {y} {y'} hx hy =
  trans (add-remainder x y)
    (trans (cong₂ (λ a b → normalize k (a + b)) hx hy) (sym (add-remainder x' y')))

*-cong : {x x' y y' : Nat} → x ≈ x' → y ≈ y' → (x * y) ≈ (x' * y')
*-cong {x} {x'} {y} {y'} hx hy =
  trans (mul-remainder x y)
    (trans (cong₂ (λ a b → normalize k (a * b)) hx hy) (sym (mul-remainder x' y')))

-- Reducing only the left operand does not change the sum's residue.
reduce-add-left : (x y : Nat) → normalize k (x + y) ≡ normalize k (normalize k x + y)
reduce-add-left x y = trans (add-remainder x y)
  (sym (trans (add-remainder (normalize k x) y)
    (cong (λ a → normalize k (a + normalize k y)) (remainder-idem x))))

inverseʳ : (x : Nat) → (x + negative k x) ≈ 0
inverseʳ x = trans (reduce-add-left x (negative k x))
  (trans (cong (normalize k) (ℕ.m+[n∸m]≡n bound)) (DivMod.n%n≡0 p))
  where
  bound : normalize k x ≤ p
  bound = ℕ.<⇒≤ (DivMod.m%n<n x p)

inverseˡ : (x : Nat) → (negative k x + x) ≈ 0
inverseˡ x = trans (cong (normalize k) (ℕ.+-comm (negative k x) x)) (inverseʳ x)

neg-cong : {x y : Nat} → x ≈ y → negative k x ≈ negative k y
neg-cong h = cong (λ a → normalize k (p - a)) h

equivalence : IsEquivalence _≈_
equivalence = record { refl = refl ; sym = sym ; trans = trans }

open import Algebra.Structures _≈_ using (IsMagma; IsSemigroup; IsMonoid; IsGroup; IsAbelianGroup; IsRing; IsCommutativeRing)

+-magma : IsMagma _+_
+-magma = record { isEquivalence = equivalence ; ∙-cong = λ {x} {y} {u} {v} hx hy → +-cong {x} {y} {u} {v} hx hy }

+-semigroup : IsSemigroup _+_
+-semigroup = record { isMagma = +-magma ; assoc = λ x y z → cong (normalize k) (ℕ.+-assoc x y z) }

+-monoid : IsMonoid _+_ 0
+-monoid = record
  { isSemigroup = +-semigroup
  ; identity = (λ x → cong (normalize k) (ℕ.+-identityˡ x)) , (λ x → cong (normalize k) (ℕ.+-identityʳ x))
  }

+-group : IsGroup _+_ 0 (negative k)
+-group = record { isMonoid = +-monoid ; inverse = inverseˡ , inverseʳ ; ⁻¹-cong = λ {x} {y} h → neg-cong {x} {y} h }

+-abelian : IsAbelianGroup _+_ 0 (negative k)
+-abelian = record { isGroup = +-group ; comm = λ x y → cong (normalize k) (ℕ.+-comm x y) }

*-magma : IsMagma _*_
*-magma = record { isEquivalence = equivalence ; ∙-cong = λ {x} {y} {u} {v} hx hy → *-cong {x} {y} {u} {v} hx hy }

*-semigroup : IsSemigroup _*_
*-semigroup = record { isMagma = *-magma ; assoc = λ x y z → cong (normalize k) (ℕ.*-assoc x y z) }

*-monoid : IsMonoid _*_ 1
*-monoid = record
  { isSemigroup = *-semigroup
  ; identity = (λ x → cong (normalize k) (ℕ.*-identityˡ x)) , (λ x → cong (normalize k) (ℕ.*-identityʳ x))
  }

isRing : IsRing _+_ _*_ (negative k) 0 1
isRing = record
  { +-isAbelianGroup = +-abelian
  ; *-cong = λ {x} {y} {u} {v} hx hy → *-cong {x} {y} {u} {v} hx hy
  ; *-assoc = λ x y z → cong (normalize k) (ℕ.*-assoc x y z)
  ; *-identity = (λ x → cong (normalize k) (ℕ.*-identityˡ x)) , (λ x → cong (normalize k) (ℕ.*-identityʳ x))
  ; distrib = (λ x y z → cong (normalize k) (ℕ.*-distribˡ-+ x y z)) ,
              (λ x y z → cong (normalize k) (ℕ.*-distribʳ-+ x y z))
  }

isCommutativeRing : IsCommutativeRing _+_ _*_ (negative k) 0 1
isCommutativeRing = record { isRing = isRing ; *-comm = λ x y → cong (normalize k) (ℕ.*-comm x y) }

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { Carrier = Nat
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = negative k
  ; 0# = 0
  ; 1# = 1
  ; isCommutativeRing = isCommutativeRing
  }

-- Equivalent representatives may differ by an entire modulus.
modulus-shift : (x : Nat) → x ≈ (p + x)
modulus-shift x = sym (trans (cong (normalize k) (ℕ.+-comm p x))
  (DivMod.[m+n]%n≡m%n x p))
