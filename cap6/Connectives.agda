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

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    --------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ x) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ{ (inj₁ x) → inj₂ x; (inj₂ y) → inj₁ y }
    ; from = λ{ (inj₁ y) → inj₂ y; (inj₂ x) → inj₁ x }
    ; to∘from = λ{ (inj₁ y) → refl; (inj₂ x) → refl }
    ; from∘to = λ{ (inj₁ x) → refl; (inj₂ y) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc =
  record
    { to = λ{ (inj₁ a) → inj₁ (inj₁ a); (inj₂ (inj₁ b)) → inj₁ (inj₂ b); (inj₂ (inj₂ c)) → inj₂ c }
    ; from = λ{ (inj₂ c) → inj₂ (inj₂ c); (inj₁ (inj₁ a)) → inj₁ a; (inj₁ (inj₂ b)) → inj₂ (inj₁ b) }
    ; to∘from = λ{ (inj₁ (inj₁ a)) → refl; (inj₁ (inj₂ b)) → refl; (inj₂ c) → refl }
    ; from∘to = λ{ (inj₁ a) → refl; (inj₂ (inj₁ b)) → refl; (inj₂ (inj₂ c)) → refl }
    }

data ⊥ : Set where
  -- nada!

⊥-elim : ∀ {A : Set}
  → ⊥
    ---
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{ (inj₂ a) → a }
    ; from = λ{ a → inj₂ a }
    ; from∘to = λ{ (inj₂ a) → refl }
    ; to∘from = λ{ a → refl }
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M
