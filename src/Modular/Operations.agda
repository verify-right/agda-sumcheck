{-# OPTIONS --safe --without-K #-}
module Modular.Operations where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; _+_; _-_; _*_; _==_; mod-helper)
open import Ring.Verifier using (Operations; MkOperations)

-- k describes the modulus p = k + 2. Thus p is always at least 2;
-- all prime fields are included, without a runtime primality test.
modulus : Nat → Nat
modulus k = 2 + k

normalize : Nat → Nat → Nat
normalize k x = mod-helper 0 (1 + k) x (1 + k)

negative : Nat → Nat → Nat
negative k x = modulus k - normalize k x

same : Nat → Nat → Nat → Bool
same k x y = normalize k x == normalize k y

-- Raw natural + and * are valid operations on residue representatives.
-- Interpolation normalizes at each round, preventing growth across rounds.
operations : Nat → Operations Nat
operations k = MkOperations 1 _+_ _*_ (negative k) (normalize k) (same k)
