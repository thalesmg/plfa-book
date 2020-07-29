module plfa.cap3.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc; *-comm; +-identityʳ)
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
  ⟨⟩  : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = from b + from b
from (b I) = suc (from b + from b)

data One : Bin → Set
data Can : Bin → Set

-- not suitable for proving later stuff...
-- data One where
--   one : One (⟨⟩ I)
--   _withO : ∀ {b} → One b → One (b O)
--   _withI : ∀ {b} → One b → One (b I)

-- much better for proving stuff in this chapter
-- but very hard to prove stuff in Quantifiers...
-- data One where
--   one    : One (⟨⟩ I)
--   sucOne : ∀ {b} → One b → One (inc b)

data Inc : Bin → Bin → Set where
  inc-⟨⟩ : Inc (⟨⟩) (⟨⟩ I)
  inc-O  : ∀ (b : Bin) → Inc (b O) (b I)
  inc-I  : ∀ (b b' : Bin) → Inc b b' → Inc (b I) (b' O)

data One where
  one : One (⟨⟩ I)
  sucOne : ∀ {b b'} → Inc b b' → One b → One b'

data Can where
  canZero : Can (⟨⟩ O)
  canMore : ∀ {b} → One b → Can b

inc-Can : ∀ {b b' : Bin}
  → {_ : Inc b b'}
  → Can b
    -----------
  → Can b'
inc-Can {.(⟨⟩ O)} {⟨⟩ I} {prf} canZero = canMore one
inc-Can {b} {b'} {prf} (canMore o) = canMore (sucOne prf o)

Inc-inc : ∀ {b} → Inc b (inc b)
Inc-inc {⟨⟩} = inc-⟨⟩
Inc-inc {b O} = inc-O b
Inc-inc {b I} = inc-I b (inc b) Inc-inc

Inc-inc-subs : ∀ {b b'} → Inc b b' → b' ≡ inc b
Inc-inc-subs inc-⟨⟩ = refl
Inc-inc-subs (inc-O b) = refl
Inc-inc-subs (inc-I .⟨⟩ .(⟨⟩ I) inc-⟨⟩) = refl
Inc-inc-subs (inc-I .(b O) .(b I) (inc-O b)) = refl
Inc-inc-subs (inc-I .(b I) .(b' O) (inc-I b b' i)) = cong (_O) (cong _O (Inc-inc-subs i))

Inc-One : ∀ {b b'} → Inc b b' → One b → One b'
Inc-One inc-⟨⟩ (sucOne x o) = one
Inc-One (inc-O b) o = sucOne (inc-O b) o
Inc-One (inc-I .⟨⟩ .(⟨⟩ I) inc-⟨⟩) one = sucOne (inc-I ⟨⟩ (⟨⟩ I) inc-⟨⟩) one
Inc-One (inc-I b b' i) (sucOne x o) with Inc-One x o | Inc-inc-subs i
... | oo | refl = sucOne Inc-inc oo

to-One : ∀ (n : ℕ)
  → One (to (suc n))
to-One zero = one
to-One (suc n) with to-One n
... | prf = sucOne (Inc-inc {inc (to n)}) prf

to-Can : ∀ (n : ℕ)
  → Can (to n)
to-Can zero = canZero
to-Can (suc n) = canMore (to-One n)

from∘inc-lemma : ∀ {n} → from (inc n) ≡ suc (from n)
from∘inc-lemma {⟨⟩} = refl
from∘inc-lemma {n O} = refl
from∘inc-lemma {n I} rewrite from∘inc-lemma {n}
                           | +-suc (from n) (from n)
                           = refl

from∘to≡ : ∀ { n } → from (to n) ≡ n
from∘to≡ {zero} = refl
from∘to≡ {suc n} rewrite from∘inc-lemma {to n} = cong suc (from∘to≡ {n})

Can-to : ∀ {n} → Can (to n)
Can-to {zero} = canZero
Can-to {suc n} = canMore (to-One n)

-- withO-2* : ∀ b → 2 * from b ≡ from (b O)
-- withO-2* b = {!!}

withO-+ : ∀ b → from b + from b ≡ from (b O)
withO-+ b = refl

suc-suc : ∀ {n} → suc n + suc n ≡ suc (n + suc n)
suc-suc = refl

Inc-suc-from : ∀ {b b'} → Inc b b' → from b' ≡ suc (from b)
Inc-suc-from inc-⟨⟩ = refl
Inc-suc-from (inc-O b) = refl
Inc-suc-from (inc-I b b' i)
  rewrite sym (+-suc (from b) (from b))
        | suc-suc {from b}
        | Inc-suc-from i = refl

n≤sn : ∀ {n} → n ≤ suc n
n≤sn {zero} = z≤s
n≤sn {suc n} = s≤s (n≤sn {n})

n≤n+0 : ∀ {n} → n ≤ n + zero
n≤n+0 {zero} = z≤s
n≤n+0 {suc n} = s≤s (n≤n+0 {n})

x≤x+x : ∀ {n} → n ≤ n + n
x≤x+x {zero} = z≤s
x≤x+x {suc n} rewrite +-identityʳ n = s≤s (≤-trans (n≤n+0 {n}) (+-monoʳ-≤ n zero (suc n) z≤s))

inc-inc-lemma : ∀ {b b'} → Inc b b' → b' O ≡ inc (inc (b O))
inc-inc-lemma inc-⟨⟩ = refl
inc-inc-lemma (inc-O b) = refl
inc-inc-lemma (inc-I b b' i) = Inc-inc-subs (inc-I (b I) (b' O) (inc-I b b' i))

evil-lemma : ∀ {b b'} → One b → Inc b b' → One b'
evil-lemma o inc-⟨⟩ = one
evil-lemma o (inc-O b) = sucOne (inc-O b) o
evil-lemma o (inc-I b b' i) = sucOne (inc-I b b' i) o

sad-lemma : ∀ {b b'} → One b' → b I ≡ inc b' → b' ≡ b O
sad-lemma (sucOne (inc-I .⟨⟩ .(⟨⟩ I) inc-⟨⟩) one) refl = refl
sad-lemma (sucOne (inc-I b b' i) (sucOne i' o)) refl = refl

good-lemma : ∀ {b} → One b → One (b O)
good-lemma one = sucOne (inc-I ⟨⟩ (⟨⟩ I) inc-⟨⟩) one
good-lemma (sucOne inc-⟨⟩ o) = good-lemma one
good-lemma (sucOne (inc-O b) o) = sucOne (inc-I (b O) (b I) (inc-O b))
                                    (sucOne (inc-O (b O)) (good-lemma o))
good-lemma (sucOne (inc-I b b' i) o) = sucOne (inc-I (b I) (b' O) (inc-I b b' i))
                                         (sucOne (inc-O (b I)) (good-lemma o))

One-to∘from : ∀ {b : Bin} → One b → to (from b) ≡ b
One-to∘from {.(⟨⟩ I)} one = refl
One-to∘from (sucOne inc-⟨⟩ o) = refl
One-to∘from (sucOne (inc-O b) o) = cong inc (One-to∘from o)
One-to∘from (sucOne (inc-I .⟨⟩ b' i) one) with inc-inc-lemma i
... | refl = refl
One-to∘from (sucOne (inc-I b b' i) (sucOne {b''} x (sucOne x₁ o)))
--   with One-to∘from o | Inc-suc-from i | +-suc (from b) (from b) | inc-inc-lemma i | Inc-inc-subs (inc-O b'') | withO-+ (inc b)
-- ... | prf1 | prf2 | prf3 | refl | refl | refl = {!!}
  rewrite
      One-to∘from o
    | Inc-suc-from i
    | +-suc (from b) (from b)
    | inc-inc-lemma i
    -- | Inc-inc-subs (inc-O b'') =
    --   let fuck = Inc-One x₁ o
    --       carai = evil-lemma fuck x
    --       maldito = Inc-inc-subs x
    --       bosta = sad-lemma fuck maldito
    --   in cong inc (One-to∘from (sucOne (inc-O b) {!fuck!}))
    | Inc-inc-subs (inc-O b'')
    | sad-lemma (Inc-One x₁ o) (Inc-inc-subs x) = cong inc {!!}
      -- in cong inc (One-to∘from (sucOne (inc-O b) {!fuck!}))
    -- | Inc-inc-subs (inc-O b'') = {!!}

-- Inc-One : ∀ {b b'} → Inc b b' → One b → One b'
-- Inc-inc-subs : ∀ {b b'} → Inc b b' → b' ≡ inc b
-- sad-lemma : ∀ {b b'} → One b' → b I ≡ inc b' → b' ≡ b O

Can-to∘from : ∀ {b} → Can b → to (from b) ≡ b
Can-to∘from canZero = refl
Can-to∘from (canMore o) = One-to∘from o
