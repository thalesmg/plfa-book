module plfa.cap8.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Relation.Nullary using (¬_)
-- open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨⟨_,_⟩⟩)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import plfa.cap5.Isomorphism using (_≃_; extensionality)
open import plfa.cap3.Relations using (_≤_; z≤s; s≤s)

open import Data.Empty using (⊥; ⊥-elim)
open import plfa.cap7.Negation using (¬-elim)
import plfa.cap3.Relations
open plfa.cap3.Relations using ( Bin
                               ; Can
                               ; One
                               ; to-Can
                               ; inc
                               ; Inc
                               ; Inc-inc-subs
                               ; Inc-One
                               ) renaming (to to toB; from to fromB; from∘to≡ to from∘toB)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ{ f → ⟨ (λ{ x → proj₁ (f x) }) , (λ{ x → proj₂ (f x) }) ⟩ }
    ; from = λ{ ⟨ a→b , a→c ⟩ → λ{ a → ⟨ a→b a , a→c a ⟩ } }
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ x → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → (B x) ⊎ (C x)
⊎∀-implies-∀⊎ (inj₁ x→Bx) x = inj₁ (x→Bx x)
⊎∀-implies-∀⊎ (inj₂ x→Cx) x = inj₂ (x→Cx x)

{-
  ∀⊎-implies-⊎∀ does not hold because the proofs `B x` and `C x` may
  depend on the specific value `x`, but the ∀⊎-implies-⊎∀ requires us
  to determina in advance which of the cases hold, either `(∀ (x : A)
  → B x)` or `(∀ (x : A) → C x)`
 -}

-- Exercise ∀-×

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {B : Tri → Set} {f g : (x : Tri) → B x}
    → (∀ (x : Tri) → f x ≡ g x)
      --------------------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set}
  → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× =
  record
    { to = λ{ mk → ⟨ mk aa , ⟨ mk bb , mk cc ⟩ ⟩ }
    ; from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ{ aa → Baa
                                         ; bb → Bbb
                                         ; cc → Bcc
                                         }
              }
    ; from∘to = λ{ mk → ∀-extensionality λ{ aa → refl
                                          ; bb → refl
                                          ; cc → refl
                                          }
                 }
    ; to∘from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl }
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ' (A : Set) (B : A → Set) : Set where
  field
    proj₁' : A
    proj₂' : B proj₁'

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → ∃-elim f }
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ } } }
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl } }
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { -- to = λ{ ⟨ x , y ⟩ → case-⊎ (λ{ Bx → inj₁ ⟨ x , Bx ⟩ }) (λ{ Cx → inj₂ ⟨ x , Cx ⟩ }) y }
      to = λ{ ⟨ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
            ; ⟨ x , inj₂ y ⟩ → inj₂ ⟨ x , y ⟩
            }
    ; from = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ x , inj₁ y ⟩
              ; (inj₂ ⟨ x , y ⟩) → ⟨ x , inj₂ y ⟩
              }
    ; from∘to = λ{ ⟨ x , inj₁ y ⟩ → refl
                 ; ⟨ x , inj₂ y ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ ⟨ x , y ⟩) → refl
                 }
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩

{-
  the converse of ∃×-implies-×∃ does not hold. if we `∃[ x ] B` and
  `∃[ y ] C`, it is not necessarily true that x ≡ y.
-}

-- Exercise ∃-⊎

∃-⊎ : ∀ {B : Tri → Set}
  → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
    { to = λ{ ⟨ aa , y ⟩ → inj₁ y ; ⟨ bb , y ⟩ → inj₂ (inj₁ y) ; ⟨ cc , y ⟩ → inj₂ (inj₂ y) }
    ; from = λ{ (inj₁ x) → ⟨ aa , x ⟩ ; (inj₂ (inj₁ x)) → ⟨ bb , x ⟩ ; (inj₂ (inj₂ y)) → ⟨ cc , y ⟩}
    ; from∘to = λ{ ⟨ aa , y ⟩ → refl ; ⟨ bb , y ⟩ → refl ; ⟨ cc , y ⟩ → refl }
    ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl}
    }

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

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ x , refl ⟩ = ⟨ suc x , refl ⟩

odd-∃ (odd-suc e) with even-∃ e
...                  | ⟨ x , refl ⟩ = ⟨ x , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

-- Exercise : ∃-even-odd

sucx≡x+1 : ∀ {x : ℕ} → suc x ≡ x + 1
sucx≡x+1 {x} rewrite +-comm x 1 = refl

lemma6 : ∀ {m : ℕ} → m + (m + 0) + 1 ≡ 1 + 2 * m
lemma6 {m} rewrite +-identityʳ m
                 | +-assoc m m 1
                 | +-comm m 1
                 | +-comm m (suc m) = refl

lemma5 : ∀ {m : ℕ} → m + suc (m + 0) ≡ 2 * m + 1
lemma5 {m} rewrite +-identityʳ m
                 | +-comm 1 m
                 | +-assoc m m 1 = refl

lemma4 : ∀ {m : ℕ} → m + (m + 0) + 1 ≡ m + m + 1
lemma4 {m} rewrite +-identityʳ m = refl

lemma3 : ∀ (m : ℕ) → even (m + m)
lemma3 zero = even-zero
lemma3 (suc m) rewrite +-comm m (suc m) = even-suc (odd-suc (lemma3 m))

lemma2 : ∀ {x : ℕ} → suc (x + zero) ≡ (x + zero) + 1
lemma2 {x} rewrite +-comm (x + zero) 1 = refl

lemma1 : ∀ {x : ℕ} → x + suc (x + zero) ≡ 2 * x + 1
lemma1 {x} rewrite +-assoc x zero 1
                 | lemma2 {x}
                 | +-assoc x 0 1
                 | +-identityʳ x
                 | +-assoc x x 1 = refl

∃-even' : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

∃-even' ⟨ zero , refl ⟩ = even-zero
∃-even' ⟨ suc m , refl ⟩ rewrite lemma4 {m}
                              | lemma5 {m}
                              | +-comm m ((m + 0) + 1)
                              | lemma6 {m}
                              | +-identityʳ m = even-suc (odd-suc (lemma3 m))

∃-odd' ⟨ zero , refl ⟩ = odd-suc even-zero
∃-odd' ⟨ suc m , refl ⟩ rewrite +-comm (m + suc (m + zero)) 1 = odd-suc (∃-even' ⟨ suc m , refl ⟩)

-- Exercise: ∃-+-≤

≤→∃+ : ∀ (y z : ℕ)
  → y ≤ z
    ----------------
  → ∃[ x ] (x + y ≡ z)
-- ≤→∃+ y z z≤s = ⟨ z , +-identityʳ z ⟩
-- ≤→∃+ y z (s≤s y≤z) = {!!}
≤→∃+ zero z y≤z = ⟨ z , +-identityʳ z ⟩
≤→∃+ (suc y) (suc z) (s≤s y≤z) = ∃-elim (λ{ x prf → ⟨ x , lemma x y z prf ⟩ }) (≤→∃+ y z y≤z)
  where
    lemma : ∀ (a b c : ℕ) → a + b ≡ c → a + suc b ≡ suc c
    lemma a b c refl rewrite +-comm a (suc b)
                           | +-comm b a  = refl

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ (B x)
¬∃≃∀¬ =
  record
    { to = λ{ ¬∃xy x → λ{ y → ¬∃xy ⟨ x , y ⟩ } }
    ; from = λ{ ∀¬xy → λ{ ⟨ x , y ⟩ → ∀¬xy x y } }
    ; from∘to = λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from = λ{ ∀¬xy → refl }
    }

-- Exercise: ∃¬-implies-¬∀

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → (∃[ x ] (¬ (B x))) → ¬ ((x : A) → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ{ x→Bx → ¬Bx (x→Bx x) }

-- ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
--   → (¬ ((x : A) → B x)) → ∃[ x ] (¬ (B x))
{-
  The converse does not hold. The type A may not even be inhabited, so
  one cannot even produce a value of its type.
-}

-- Exercise: Bin-isomorphism

{-
data One' : Bin → Set where
  one'   : One' (Bin.⟨⟩ Bin.I)
  _withO' : ∀ {b} → One' b → One' (b Bin.O)
  _withI' : ∀ {b} → One' b → One' (b Bin.I)

One-withO : ∀ {b} → One b → One (b Bin.O)
One-withO One.one = One.sucOne One.one
One-withO (One.sucOne o) = One.sucOne (One.sucOne (One-withO o))

One-withI : ∀ {b} → One b → One (b Bin.I)
One-withI One.one = One.sucOne (One.sucOne One.one)
One-withI (One.sucOne o) = One.sucOne (One.sucOne (One-withI o))

One→One' : ∀ {b} → One b → One' b
One→One' One.one = one'
One→One' (One.sucOne {Bin.⟨⟩} o) = one'
One→One' (One.sucOne {b Bin.O} o) with One→One' o
... | oo withO' = oo withI'
One→One' (One.sucOne {b Bin.I} o) with One→One' o
... | one' = one' withO'
... | oo withI' = {!!}

One'→One : ∀ {b} → One' b → One b
One'→One one' = One.one
One'→One (o withO') with (One'→One o)
... | One.one = One.sucOne One.one
... | One.sucOne oo = One.sucOne (One-withI oo)
One'→One (o withI') with (One'→One o)
... | One.one = One.sucOne (One.sucOne One.one)
... | One.sucOne oo = One-withI (One.sucOne oo)

≡One' : ∀ {b : Bin} (o o' : One' b) → o ≡ o'
≡One' one' one' = refl
≡One' (o1 withO') (o2 withO') = cong _withO' (≡One' o1 o2)
≡One' (o1 withI') (o2 withI') = cong _withI' (≡One' o1 o2)
-}

-- Inc-One : ∀ {b b'} → Inc b b' → One b → One b'
-- Inc-inc-subs : ∀ {b b'} → Inc b b' → b' ≡ inc b

-- One-head-OI : ∀ {b} → One (b Bin.O Bin.I) → One (b Bin.O)
-- One-head-II : ∀ {b} → One (b Bin.I Bin.I) → One (b Bin.I)

Inc-I-prev-O : ∀ {b b'} → One b → Inc b (b' Bin.I) → b' Bin.O ≡ b
Inc-I-prev-O (One.sucOne () o) Inc.inc-⟨⟩
Inc-I-prev-O o (Inc.inc-O _) = refl

One-head-O : ∀ {b} → One (b Bin.O) → One b
One-head-O (One.sucOne {b Bin.I} (Inc.inc-I .b (b' Bin.O) x) (One.sucOne i o)) with sym (Inc-I-prev-O o i)
... | refl with One-head-O o
... | oo = One.sucOne x oo
One-head-O (One.sucOne {.Bin.⟨⟩ Bin.I} (Inc.inc-I .Bin.⟨⟩ (.Bin.⟨⟩ Bin.I) Inc.inc-⟨⟩) One.one) = One.one
One-head-O (One.sucOne {b Bin.I} (Inc.inc-I .b (Bin.⟨⟩ Bin.I) x) (One.sucOne i o)) with sym (Inc-I-prev-O o i)
... | refl = One.sucOne x (One-head-O o)
One-head-O (One.sucOne {b Bin.I} (Inc.inc-I .b ((b' Bin.O) Bin.I) x) (One.sucOne {b1} i o)) with sym (Inc-I-prev-O o i)
... | refl = One.sucOne x (One-head-O o)
One-head-O (One.sucOne {b Bin.I} (Inc.inc-I .b ((b' Bin.I) Bin.I) x) (One.sucOne {b1} i o)) with sym (Inc-I-prev-O o i)
... | refl = One.sucOne x (One-head-O o)

One-head-I : ∀ {b} → One (b Bin.I) → (b ≡ Bin.⟨⟩) ⊎ (One b)
One-head-I One.one = inj₁ refl
One-head-I (One.sucOne {b0} x o) with Inc-I-prev-O o x
... | refl = inj₂ (One-head-O o)

≡Inc-Inc : ∀ {b0 b1 b2 b2' : Bin} → Inc b0 b1 → Inc b1 b2 → Inc b1 b2' → b2 ≡ b2'
≡Inc-Inc Inc.inc-⟨⟩ (Inc.inc-I .Bin.⟨⟩ .(Bin.⟨⟩ Bin.I) Inc.inc-⟨⟩) (Inc.inc-I .Bin.⟨⟩ .(Bin.⟨⟩ Bin.I) Inc.inc-⟨⟩) = refl
≡Inc-Inc (Inc.inc-O Bin.⟨⟩) (Inc.inc-I .Bin.⟨⟩ b'' i) (Inc.inc-I .Bin.⟨⟩ b' i')
  rewrite Inc-inc-subs i'
        | Inc-inc-subs i = refl
≡Inc-Inc (Inc.inc-O (b Bin.O)) (Inc.inc-I .(b Bin.O) b'' i) (Inc.inc-I .(b Bin.O) b' i')
  rewrite Inc-inc-subs i'
        | Inc-inc-subs i = refl
≡Inc-Inc (Inc.inc-O (b Bin.I)) (Inc.inc-I .(b Bin.I) b'' i) (Inc.inc-I .(b Bin.I) b' i')
  rewrite Inc-inc-subs i'
        | Inc-inc-subs i = refl
≡Inc-Inc (Inc.inc-I b b' i0) (Inc.inc-O .b') (Inc.inc-O .b') = refl

≡Inc : ∀ {b0 b1 bi : Bin} → One b0 → Inc b0 bi → One b1 → Inc b1 bi → b0 ≡ b1
≡Inc o0 i0 (One.sucOne () o1) Inc.inc-⟨⟩
≡Inc (One.sucOne () o0) Inc.inc-⟨⟩ o1 (Inc.inc-O .Bin.⟨⟩)
≡Inc o0 (Inc.inc-O .b) o1 (Inc.inc-O b) = refl
≡Inc {b0 Bin.I} o0 (Inc.inc-I .b0 .b' i0) o1 (Inc.inc-I b b' i1) = cong (Bin._I) {!!}
-- ≡Inc (One.sucOne x o0) i0 (One.sucOne () o1) Inc.inc-⟨⟩
-- ≡Inc (One.sucOne () o0) Inc.inc-⟨⟩ o1 (Inc.inc-O .Bin.⟨⟩)
-- ≡Inc o0 (Inc.inc-O .b) o1 (Inc.inc-O b) = refl
-- ≡Inc o0 (Inc.inc-I Bin.⟨⟩ .(Bin.⟨⟩ Bin.I) i0) o1 (Inc.inc-I .Bin.⟨⟩ .(Bin.⟨⟩ Bin.I) Inc.inc-⟨⟩) = refl
-- ≡Inc (One.sucOne (Inc.inc-O (.Bin.⟨⟩ Bin.O)) (One.sucOne (Inc.inc-I .(b Bin.I) .(Bin.⟨⟩ Bin.O) (Inc.inc-I b .Bin.⟨⟩ ())) o0)) (Inc.inc-I .(Bin.⟨⟩ Bin.O) .(Bin.⟨⟩ Bin.I) (Inc.inc-O .Bin.⟨⟩)) o1 (Inc.inc-I .Bin.⟨⟩ .(Bin.⟨⟩ Bin.I) Inc.inc-⟨⟩)
-- ≡Inc o0 (Inc.inc-I b0 .(b Bin.I) i0) o1 (Inc.inc-I .(b Bin.O) .(b Bin.I) (Inc.inc-O b)) = {!!}
-- ≡Inc o0 (Inc.inc-I .(b₁ Bin.I) .(b' Bin.O) (Inc.inc-I b₁ .b' i0)) o1 (Inc.inc-I .(b Bin.I) .(b' Bin.O) (Inc.inc-I b b' i1)) = {!!}

unique-Inc' : ∀ {b0 b1 : Bin} → (i i' : Inc b0 b1) → i ≡ i'
unique-Inc' Inc.inc-⟨⟩ Inc.inc-⟨⟩ = refl
unique-Inc' (Inc.inc-O .b) (Inc.inc-O b) = refl
unique-Inc' (Inc.inc-I .b .b' i) (Inc.inc-I b b' i') = cong (Inc.inc-I b b') (unique-Inc' i i')

≡One : ∀ {b : Bin} (o o' : One b) → o ≡ o'
≡One One.one One.one = refl
≡One (One.sucOne Inc.inc-⟨⟩ (One.sucOne () o1)) One.one
≡One (One.sucOne (Inc.inc-O .Bin.⟨⟩) (One.sucOne (Inc.inc-I b .Bin.⟨⟩ ()) o1)) One.one
≡One One.one (One.sucOne Inc.inc-⟨⟩ (One.sucOne () o2))
≡One One.one (One.sucOne (Inc.inc-O .Bin.⟨⟩) (One.sucOne (Inc.inc-I b .Bin.⟨⟩ ()) o2))
≡One (One.sucOne {b0} {b1} i1 o1) (One.sucOne {b} {.b1} i2 o2) with ≡Inc o1 i1 o2 i2
... | refl with unique-Inc' i1 i2
... | refl = cong (One.sucOne i1) (≡One o1 o2)

≡Can : ∀ {b : Bin} (cb : Can b) (cb' : Can b) → cb ≡ cb'
≡Can Can.canZero Can.canZero = refl
≡Can Can.canZero (Can.canMore (One.sucOne (Inc.inc-I b .Bin.⟨⟩ ()) x₁))
≡Can (Can.canMore (One.sucOne (Inc.inc-I b .Bin.⟨⟩ ()) x₁)) Can.canZero
≡Can (Can.canMore x1) (Can.canMore x2) with ≡One x1 x2
... | refl = refl

proj₁∃ : {A : Set} {B : A → Set} → ∃[ x ] B x → A
proj₁∃ ⟨ x , _ ⟩ = x

proj₁≡→Can≡ : {cb cb' : ∃[ b ](Can b)} → proj₁∃ cb ≡ proj₁∃ cb' → cb ≡ cb'
proj₁≡→Can≡ {⟨ x , y ⟩} {⟨ x' , y' ⟩} refl rewrite ≡Can y y' = refl

ℕ-iso-∃Bin : ∃[ b ](Can b) ≃ ℕ
ℕ-iso-∃Bin =
  record
    { to = λ{ ⟨ b , cb ⟩ → fromB b }
    ; from = λ{ n → ⟨ toB n , to-Can n ⟩ }
    ; to∘from = λ{ n → from∘toB {n}}
    ; from∘to = λ{ ⟨ b , cb ⟩ → proj₁≡→Can≡ {!!} }
    }
