module plfa.cap6.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.cap5.Isomorphism using (_≃_; _≲_; extensionality)
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
