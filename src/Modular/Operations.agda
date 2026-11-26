{-# OPTIONS --safe --without-K #-}
module Modular.Operations where

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _*_; _%_; _≡ᵇ_)
open import Ring.Verifier using (Operations; MkOperations)

-- k describes the modulus p = k + 2. Thus p is always at least 2;
-- all prime fields are included, without a runtime primality test.
modulus : ℕ → ℕ
modulus k = 2 + k

normalize : ℕ → ℕ → ℕ
normalize k x = x % modulus k

negative : ℕ → ℕ → ℕ
negative k x = modulus k ∸ normalize k x

same : ℕ → ℕ → ℕ → Bool
same k x y = normalize k x ≡ᵇ normalize k y

-- Raw natural + and * are valid operations on residue representatives.
-- Interpolation normalizes at each round, preventing growth across rounds.
operations : ℕ → Operations ℕ
operations k = MkOperations 1 _+_ _*_ (negative k) (normalize k) (same k)
