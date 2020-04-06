module plfa.cap8.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
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
    { to = λ{ f → ⟨ (λ{ x → proj₁ (f x) }) , (λ{ x → proj₂ (f x) }) ⟩ }
    ; from = λ{ ⟨ a→b , a→c ⟩ → λ{ a → ⟨ a→b a , a→c a ⟩ } }
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ x → refl }
    }

-- ⊎∀-implies-∀⊎
