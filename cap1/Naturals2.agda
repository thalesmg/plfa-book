module plfa.cap1.Naturals2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 inc b

to : ℕ → Bin
to zero = x0 nil
to (suc m) = inc (to m)

from : Bin → ℕ
from nil = zero
from (x0 m) = 2 * from m
from (x1 m) = 1 + 2 * from m

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

_ : from (x0 nil) ≡ zero
_ =
  begin
    from (x0 nil)
  ≡⟨⟩
    2 * from nil
  ≡⟨⟩
    2 * zero
  ≡⟨⟩
    zero
  ∎

_ : from (x1 nil) ≡ 1
_ =
  begin
    from (x1 nil)
  ≡⟨⟩
    1 + 2 * from nil
  ≡⟨⟩
    1 + 2 * zero
  ≡⟨⟩
    1 + zero
  ≡⟨⟩
    1
  ∎

_ : from (x0 x1 nil) ≡ 2
_ =
  begin
    from (x0 x1 nil)
  ≡⟨⟩
    2 * from (x1 nil)
  ≡⟨⟩
    2 * (1 + 2 * from nil)
  ≡⟨⟩
    2 * (1 + 2 * 0)
  ≡⟨⟩
    2 * 1
  ≡⟨⟩
    2
  ∎

_ : from (x1 x1 nil) ≡ 3
_ =
  begin
    from (x1 x1 nil)
  ≡⟨⟩
    1 + 2 * from (x1 nil)
  ≡⟨⟩
    1 + 2 * (1 + 2 * from nil)
  ≡⟨⟩
    1 + 2 * (1 + 2 * 0)
  ≡⟨⟩
    1 + 2 * 1
  ≡⟨⟩
    1 + 2
  ≡⟨⟩
    3
  ∎
