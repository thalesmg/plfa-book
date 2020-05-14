module plfa.cap8.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨⟨_,_⟩⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import plfa.cap5.Isomorphism using (_≃_; extensionality)

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
    { to = λ{ f → ⟨⟨ (λ{ x → proj₁ (f x) }) , (λ{ x → proj₂ (f x) }) ⟩⟩ }
    ; from = λ{ ⟨⟨ a→b , a→c ⟩⟩ → λ{ a → ⟨⟨ a→b a , a→c a ⟩⟩ } }
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
    { to = λ{ mk → ⟨⟨ mk aa , ⟨⟨ mk bb , mk cc ⟩⟩ ⟩⟩ }
    ; from = λ{ ⟨⟨ Baa , ⟨⟨ Bbb , Bcc ⟩⟩ ⟩⟩ → λ{ aa → Baa
                                         ; bb → Bbb
                                         ; cc → Bcc
                                         }
              }
    ; from∘to = λ{ mk → ∀-extensionality λ{ aa → refl
                                          ; bb → refl
                                          ; cc → refl
                                          }
                 }
    ; to∘from = λ{ ⟨⟨ Baa , ⟨⟨ Bbb , Bcc ⟩⟩ ⟩⟩ → refl }
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
∃×-implies-×∃ ⟨ x , ⟨⟨ Bx , Cx ⟩⟩ ⟩ = ⟨⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩⟩

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

lemma3 : ∀ {m : ℕ} → m + (m + 0) + 1 + 1 ≡ 2 * (m + 1)
lemma3 {m} rewrite +-identityʳ m
                 | +-identityʳ (m + 1) = {!!}

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
                              | +-identityʳ m = even-suc (odd-suc {!!})
-- ∃-even' ⟨ suc x , refl ⟩ rewrite lemma1 {x} = even-suc (∃-odd' ⟨ x , refl ⟩)
-- ∃-even' ⟨ suc x , prf ⟩ rewrite lemma1 {x} = even-suc (∃-odd' {!!})

∃-odd' ⟨ zero , refl ⟩ = odd-suc even-zero
∃-odd' ⟨ suc m , refl ⟩ rewrite +-comm (m + suc (m + zero)) 1 = odd-suc (∃-even' ⟨ suc m , refl ⟩)
-- ∃-odd' ⟨ suc m , refl ⟩ rewrite lemma1 {m}
--                              | +-identityʳ m
--                              | +-comm (m + m + 1) 1
--                              | +-identityʳ m = odd-suc (even-suc (∃-odd' ⟨ m , lemma4 {m} ⟩))
