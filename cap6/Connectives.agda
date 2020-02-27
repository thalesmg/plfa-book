module plfa.cap6.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.cap5.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.cap5.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    ------
  → A
proj₁ ⟨ m , n ⟩ = m

proj₂ : ∀ {A B : Set}
  → A × B
    ------
  → B
proj₂ ⟨ m , n ⟩ = n

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; to∘from = λ{ ⟨ x , y ⟩ → refl }
    ; from∘to = λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ{ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B  ⟩ }
    ; from = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
    ; to∘from = λ{ ⟨ A→B , B→A ⟩ → refl }
    ; from∘to = λ{ A⇔B → refl }
    }

data ⊤ : Set where
  tt :
    ----
    ⊤

η-⊤ : ∀ (w : ⊤) → w ≡ tt
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ{ ⟨ tt , a ⟩ → a }
    ; from = λ{ a → ⟨ tt , a ⟩ }
    ; to∘from = λ{ a → refl }
    ; from∘to = λ{ ⟨ tt , a ⟩ → refl }
    }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where
  inj₁ :
      A
    ----
    → A ⊎ B

  inj₂ :
      B
    ----
    → A ⊎ B
