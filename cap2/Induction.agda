module plfa.cap2.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎

+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identity' : ∀ (m : ℕ) → m + zero ≡ m
+-identity' zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identity' (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identity' m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity' m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc' : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite (+-assoc' m n p) = refl

+-identity'' : ∀ (m : ℕ) → m + zero ≡ m
+-identity'' zero = refl
+-identity'' (suc m) rewrite (+-identity'' m) = refl

+-suc'' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc'' zero n = refl
+-suc'' (suc m) n rewrite (+-suc'' m n) = refl

+-comm'' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm'' m zero rewrite (+-identity'' m) = refl
+-comm'' m (suc n) rewrite (+-suc'' m n) | +-comm'' m n = refl

+-assoc'' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc'' zero n p = refl
+-assoc'' (suc m) n p rewrite (+-assoc'' m n p) = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm m (n + p) | +-assoc n p m | +-comm m p = refl

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
*-suc zero n rewrite (+-identity' n) = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n zero rewrite *-zero (m + n) | *-zero m | *-zero n = refl
*-distrib-+ m n (suc p)
  rewrite *-suc (m + n) p
  | *-distrib-+ m n p
  | +-rearrange m n (m * p) (n * p)
  | +-comm n (m * p)
  | sym (+-rearrange m (m * p) n (n * p))
  | sym (*-suc m p)
  | sym (*-suc n p)
  = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
  | *-assoc m n p
  = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zero m = refl
*-comm m (suc n)
  rewrite *-suc m n
  | *-comm n m
  = refl

0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n zero rewrite +-identity' n = refl
∸-+-assoc zero n (suc p)
  rewrite 0∸n≡0 (n ∸ suc p)
  | 0∸n≡0 n
  | 0∸n≡0 (n + suc p)
  = refl
∸-+-assoc (suc m) zero (suc p) = refl
∸-+-assoc (suc m) (suc n) (suc p)
  rewrite ∸-+-assoc m n (suc p)
  = refl

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

from-inc-suc-from : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
from-inc-suc-from nil = refl
from-inc-suc-from (x0 x) = refl
from-inc-suc-from (x1 x)
  rewrite from-inc-suc-from x
  | +-identity' (from x)
  | +-suc (from x) (from x)
  = refl

-- to-from-ident : ∀ (x : Bin) → to (from x) ≡ x
-- nil ‌!≡ x0 nil
-- to-from-ident nil = {!!}
-- to-from-ident (x0 x) = {!!}
-- to-from-ident (x1 x) = {!!}

from-to-ident : ∀ (n : ℕ) → from (to n) ≡ n
from-to-ident zero = refl
from-to-ident (suc n)
  rewrite from-inc-suc-from (to n)
  | from-to-ident n
  = refl
