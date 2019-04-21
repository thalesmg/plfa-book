module plfa.cap4.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      ------
    → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      ------
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      ------
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
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

module ≤-Reasoning where
  data _≤_ : ℕ → ℕ → Set where
    z≤s : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

  postulate
    ≤-refl : ∀ {n : ℕ} → n ≤ n
    ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
    ≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n

  infix  1 begin<_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _<∎

  begin<_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  begin< x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _<∎ : ∀ (x : ℕ) → x ≤ x
  x <∎ = ≤-refl

  ≤-suc : ∀ (m : ℕ)
    → m ≤ suc m
  ≤-suc zero = z≤s
  ≤-suc (suc m) = s≤s (≤-suc m)

  ≤-refl-≡ : ∀ (m n : ℕ)
    → m + n ≤ n + m
  ≤-refl-≡ m n with m + n | +-comm m n
  ... | .(n + m) | refl = ≤-refl

  +ʳ-≤-1 : ∀ (m p : ℕ)
    → m ≤ m + p
  +ʳ-≤-1 zero zero = z≤s
  +ʳ-≤-1 (suc m) zero = s≤s (+ʳ-≤-1 m zero)
  +ʳ-≤-1 zero (suc p) = z≤s
  +ʳ-≤-1 (suc m) (suc p) = s≤s (+ʳ-≤-1 m (suc p))

  +ʳ-≤-2 : ∀ (m p : ℕ)
    → m ≤ p + m
  +ʳ-≤-2 m zero = ≤-refl
  +ʳ-≤-2 m (suc p) =
    begin<
      m
    ≤⟨ +ʳ-≤-2 m p ⟩
      p + m
    ≤⟨ ≤-suc (p + m) ⟩
      suc (p + m)
    <∎

  +-monoˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
      -------------
    → m + p ≤ n + p
  +-monoˡ-≤ m n zero m≤n with m + zero | +-identity m | n + zero | +-identity n
  ... | .m | refl | .n | refl  = m≤n
  +-monoˡ-≤ m n (suc p) m≤n with m + suc p | +-suc m p | n + suc p | +-suc n p
  ... | .(suc (m + p)) | refl | .(suc (n + p)) | refl = s≤s (+-monoˡ-≤ m n p m≤n)

  +-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
      -------------
    → m + p ≤ n + q
  +-mono-≤ m n p q m≤n p≤q =
    begin<
      m + p
    ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
      n + p
    ≤⟨ ≤-refl-≡ n p ⟩
      p + n
    ≤⟨ +-monoˡ-≤ p q n p≤q ⟩
      q + n
    ≤⟨ ≤-refl-≡ q n ⟩
      n + q
    <∎

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev rewrite +-comm n m = ev

-- Leibniz

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y
