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

  -- ≤-ident-l : ∀ (m : ℕ)
  --   → m + zero ≤ m
  -- ≤-ident-l m =
  --   begin<
  --     m + zero
  --   ≤⟨⟩
  --     m
  --   <∎

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
  +-mono-≤ m n p q m≤n p≤q = {!!}
