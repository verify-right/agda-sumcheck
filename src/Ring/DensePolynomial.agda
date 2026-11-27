{-# OPTIONS --safe --without-K #-}
-- Ported unchanged (module names only) from quest28-hqc/DensePolynomial.agda,
-- identical to quest15.13-piccs-source/quest15-prime/DensePolynomial.agda.
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Ring.DensePolynomial (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s; _⊔_)
import Data.Nat.Base as N
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Degree is an upper bound: trailing zero coefficients are deliberately kept.
-- This is a dense Horner normal form, not a quotient by polynomial functions.
data Poly : ℕ → Set where
  con : Carrier → Poly 0
  _▹_ : ∀ {n} → Carrier → Poly n → Poly (suc n)
infixr 5 _▹_

eval : ∀ {n} → Poly n → Carrier → Carrier
eval (con a) x = a
eval (a ▹ p) x = a + x * eval p x

zeroP : (n : ℕ) → Poly n
zeroP zero = con 0#
zeroP (suc n) = 0# ▹ zeroP n

zero-eval : (n : ℕ) (x : Carrier) → eval (zeroP n) x ≈ 0#
zero-eval zero x = refl
zero-eval (suc n) x = trans (+-cong refl (*-cong refl (zero-eval n x)))
  (trans (+-cong refl (zeroʳ x)) (+-identityˡ 0#))

constant : (n : ℕ) → Carrier → Poly n
constant zero a = con a
constant (suc n) a = a ▹ zeroP n

constant-eval : (n : ℕ) (a x : Carrier) → eval (constant n a) x ≈ a
constant-eval zero a x = refl
constant-eval (suc n) a x = trans (+-cong refl (*-cong refl (zero-eval n x)))
  (trans (+-cong refl (zeroʳ x)) (+-identityʳ a))

pad : ∀ {m n} → m ≤ n → Poly m → Poly n
pad {n = n} z≤n (con a) = constant n a
pad (s≤s h) (a ▹ p) = a ▹ pad h p

pad-eval : ∀ {m n} (h : m ≤ n) (p : Poly m) (x : Carrier) → eval (pad h p) x ≈ eval p x
pad-eval {n = n} z≤n (con a) x = constant-eval n a x
pad-eval (s≤s h) (a ▹ p) x = +-cong refl (*-cong refl (pad-eval h p x))

addP : ∀ {n} → Poly n → Poly n → Poly n
addP (con a) (con b) = con (a + b)
addP (a ▹ p) (b ▹ q) = (a + b) ▹ addP p q

scale : ∀ {n} → Carrier → Poly n → Poly n
scale a (con b) = con (a * b)
scale a (b ▹ p) = (a * b) ▹ scale a p

negP : ∀ {n} → Poly n → Poly n
negP (con a) = con (- a)
negP (a ▹ p) = (- a) ▹ negP p

plusP : ∀ {m n} → Poly m → Poly n → Poly (m ⊔ n)
plusP {m} {n} p q = addP (pad (N.m≤m⊔n m n) p) (pad (N.m≤n⊔m m n) q)

mulP : ∀ {m n} → Poly m → Poly n → Poly (m N.+ n)
mulP (con a) q = scale a q
mulP {suc m} {n} (a ▹ p) q =
  addP (pad (N.m≤n⇒m≤1+n (N.m≤n+m n m)) (scale a q)) (0# ▹ mulP p q)

-- Synthetic division by X-r uses no field inverses.
quotient : ∀ {n} → Poly (suc n) → Carrier → Poly n
quotient (a ▹ con b) r = con b
quotient (a ▹ (b ▹ p)) r = eval (b ▹ p) r ▹ quotient (b ▹ p) r
