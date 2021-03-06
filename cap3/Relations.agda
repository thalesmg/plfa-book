module plfa.cap3.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc; *-comm)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

data _≤_ : ℕ → ℕ → Set where
  z≤s : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

≤-refl : ∀ {n : ℕ}
  -----
  → n ≤ n
≤-refl {zero} = z≤s
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  -------
  → m ≤ p
≤-trans z≤s _ = z≤s
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  -------
  → m ≡ n
≤-antisym z≤s z≤s = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero y = forward z≤s
≤-total (suc x) zero = flipped z≤s
≤-total (suc x) (suc y) with ≤-total x y
...                     | forward m≤n = forward (s≤s m≤n)
...                     | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m + p ≤ m + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoʳ-≤ m p q p≤q) (+-monoˡ-≤ m n q m≤n)

*-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m * p ≤ m * q
*-monoʳ-≤ zero p q p≤q = z≤s
*-monoʳ-≤ (suc m) p q p≤q = +-mono-≤ p q (m * p) (m * q) p≤q (*-monoʳ-≤ m p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      --------------
    → suc m < suc n

<-trans : ∀ {x y z : ℕ}
  → x < y
  → y < z
    --------
  → x < z
<-trans z<s (s<s y<z) = z<s
<-trans (s<s x<y) (s<s y<z) = s<s (<-trans x<y y<z)

data Trico (m n : ℕ) : Set where
  less : m < n → Trico m n
  equa : m ≡ n → Trico m n
  more : n < m → Trico m n

<-total : ∀ (m n : ℕ) → Trico m n
<-total zero zero = equa refl
<-total zero (suc n) = less z<s
<-total (suc m) zero = more z<s
<-total (suc m) (suc n) with <-total m n
...     | less prf = less (s<s prf)
...     | equa prf = equa (cong suc prf)
...     | more prf = more (s<s prf)

*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m) = *-zeroʳ m

+-zeroʳ : ∀ (m : ℕ) → m + zero ≡ m
+-zeroʳ zero = refl
+-zeroʳ (suc m) = cong suc (+-zeroʳ m)

+-monoʳ-< : ∀ (m p q : ℕ)
  → p < q
    -------------
  → m + p < m + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc m) p q p<q = s<s (+-monoʳ-< m p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n zero m<n rewrite +-zeroʳ m | +-zeroʳ n = m<n
+-monoˡ-< m n (suc p) m<n rewrite +-suc m p | +-suc n p = s<s (+-monoˡ-< m n p m<n)

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    ------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-<-direct : ∀ (m n : ℕ)
  → suc m ≤ n
    ---------
  → m < n
≤-iff-<-direct zero (suc zero) sm≤n = z<s
≤-iff-<-direct zero (suc (suc n)) sm≤n = z<s
≤-iff-<-direct (suc m) (suc n) (s≤s sm≤n) = s<s (≤-iff-<-direct m n sm≤n)

≤-iff-<-reverse : ∀ (m n : ℕ)
  → m < n
    ---------
  → suc m ≤ n
≤-iff-<-reverse zero (suc n) sm≤n = s≤s z≤s
≤-iff-<-reverse (suc m) (suc n) (s<s sm≤n) = s≤s (≤-iff-<-reverse m n sm≤n)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero :
    ---------
    even zero
  suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)
e+o≡o {m} {n} x y rewrite +-comm m n = o+e≡o y x

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)
o+o≡e (suc x) (suc y) = suc (e+o≡o x (suc y))

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil    = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

to : ℕ → Bin
to zero = x0 nil
to (suc m) = inc (to m)

from : Bin → ℕ
from nil = zero
from (x0 m) = 2 * from m
from (x1 m) = 1 + 2 * from m

data One : Bin → Set
data Can : Bin → Set

data One where
  one : One (x1 nil)
  with0_ : ∀ {b : Bin} → One b → One (x0 b)
  with1_ : ∀ {b : Bin} → One b → One (x1 b)

data Can where
  canZero : Can (x0 nil)
  canOne  : ∀ {b : Bin} → One b → Can b

inc-One : ∀ {b : Bin}
  → One b
    -----------
  → One (inc b)
inc-One one = with0 one
inc-One (with0 o) = with1 o
inc-One (with1 one) = with0 (with0 one)
inc-One (with1 (with0 o)) = with0 (with1 o)
inc-One (with1 (with1 o)) = with0 (with0 (inc-One o))

inc-Can : ∀ {b : Bin}
  → Can b
    -----------
  → Can (inc b)
inc-Can canZero = canOne one
inc-Can (canOne one) = canOne (with0 one)
inc-Can (canOne (with0 x)) = canOne (with1 x)
inc-Can (canOne (with1 one)) = canOne (with0 (with0 one))
inc-Can (canOne (with1 (with0 x))) = canOne (with0 (with1 x))
inc-Can (canOne (with1 (with1 x))) = canOne (with0 (with0 (inc-One x)))

to-One : ∀ {n : ℕ}
  → One (to (suc n))
to-One {zero} = one
to-One {suc n} = inc-One (to-One {n})

to-Can : ∀ {n : ℕ}
  → Can (to n)
to-Can {zero} = canZero
to-Can {suc n} = canOne (to-One {n})
