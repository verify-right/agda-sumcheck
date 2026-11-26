{-# OPTIONS --safe --without-K #-}
module Modular.Examples where

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ring.Verifier
open import Modular.Operations using (operations)

-- The same asymmetric p(x,y) in both fields: 1 + x + 2y + xy.
-- Its integer hypercube sum is 11, hence 1 mod 5 and 11 mod 17.
polynomial : ℕ → ℕ → ℕ
polynomial x y = 1 + x + 2 * y + x * y

oracle : List ℕ → ℕ
oracle (x ∷ y ∷ []) = polynomial x y
oracle _ = 0

f5-rounds : List (Round ℕ)
f5-rounds = MkRound 4 2 ∷ MkRound 3 2 ∷ []

f17-rounds : List (Round ℕ)
f17-rounds = MkRound 4 7 ∷ MkRound 3 7 ∷ []

f5-honest : verify (operations 3) oracle 2 1 f5-rounds (2 ∷ 3 ∷ []) ≡ true
f5-honest = refl

f17-honest : verify (operations 15) oracle 2 11 f17-rounds (2 ∷ 3 ∷ []) ≡ true
f17-honest = refl

f17-wrong-claim : verify (operations 15) oracle 2 12 f17-rounds (2 ∷ 3 ∷ []) ≡ false
f17-wrong-claim = refl

f17-wrong-round : verify (operations 15) oracle 2 11
  (MkRound 4 7 ∷ MkRound 3 8 ∷ []) (2 ∷ 3 ∷ []) ≡ false
f17-wrong-round = refl

f17-wrong-final : verify (operations 15) (λ _ → 14) 2 11 f17-rounds (2 ∷ 3 ∷ []) ≡ false
f17-wrong-final = refl

missing-challenge : verify (operations 15) oracle 2 11 f17-rounds (2 ∷ []) ≡ false
missing-challenge = refl

extra-challenge : verify (operations 15) oracle 2 11 f17-rounds (2 ∷ 3 ∷ 4 ∷ []) ≡ false
extra-challenge = refl

wrong-expected-rounds : verify (operations 15) oracle 1 11 f17-rounds (2 ∷ 3 ∷ []) ≡ false
wrong-expected-rounds = refl

-- Noncanonical natural representatives are compared modulo 5.
f5-noncanonical : verify (operations 3) oracle 2 6
  (MkRound 9 7 ∷ MkRound 8 7 ∷ []) (7 ∷ 8 ∷ []) ≡ true
f5-noncanonical = refl

-- A wrong claim can still pass at an unlucky, externally chosen challenge.
f5-unlucky : verify (operations 3) oracle 2 2
  (MkRound 4 3 ∷ MkRound 1 3 ∷ []) (0 ∷ 1 ∷ []) ≡ true
f5-unlucky = refl

-- The verifier also works modulo a composite: the theorem needs a ring only.
mod4-honest : verify (operations 2) oracle 2 3
  (MkRound 0 3 ∷ MkRound 3 3 ∷ []) (2 ∷ 3 ∷ []) ≡ true
mod4-honest = refl

-- Characteristic two: both interpolation nodes are still distinct.
f2-honest : verify (operations 0) oracle 2 1
  (MkRound 0 1 ∷ MkRound 0 1 ∷ []) (1 ∷ 0 ∷ []) ≡ true
f2-honest = refl
