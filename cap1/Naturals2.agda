module plfa.Naturals2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 inc b

_ : inc (x0 nil) ≡ x1 nil
_ =
  begin
    inc (x0 nil)
  ≡⟨⟩
    x1 nil
  ∎

_ : inc (x1 nil) ≡ x0 x1 nil
_ =
  begin
    inc (x1 nil)
  ≡⟨⟩
    x0 (inc nil)
  ≡⟨⟩
    x0 x1 nil
  ∎

_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ =
  begin
    inc (x0 x1 nil)
  ≡⟨⟩
    x1 (x1 nil)
  ≡⟨⟩
    x1 x1 nil
  ∎

_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ =
  begin
    inc (x1 x1 nil)
  ≡⟨⟩
    x0 (inc (x1 nil))
  ≡⟨⟩
    x0 x0 (inc nil)
  ≡⟨⟩
    x0 x0 x1 nil
  ∎
