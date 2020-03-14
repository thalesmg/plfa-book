module plfa.cap7.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.cap5.Isomorphism using (_≃_; extensionality)

open import plfa.cap3.Relations using (_<_; s<s; z<s)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (cong)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    -----
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    --------
  → ¬ ¬ A
¬¬-intro x = λ{ ¬x → ¬x x }

¬¬-intro' : ∀ {A : Set}
  → A
    --------
  → ¬ ¬ A
¬¬-intro' x ¬x = ¬x x

¬¬¬-elim : ∀{A : Set}
  → ¬ ¬ ¬ A
    --------
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    --------
  → (¬ B → ¬ A)
contraposition f ¬y = λ{ x → ¬y (f x)}

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id' : ⊥ → ⊥
id' ()

id≡id' : id ≡ id'
id≡id' = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality (λ{x → ⊥-elim (¬x x)})

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

trichotomy-<-¬≡ : ∀ {m n : ℕ}
  → m < n
    ------
  → ¬ (m ≡ n)
trichotomy-<-¬≡ z<s = λ()
trichotomy-<-¬≡ (s<s m<n) = λ{sm≡sn → {!!}}
