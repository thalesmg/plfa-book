module plfa.cap7.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import plfa.cap5.Isomorphism using (_≃_; extensionality)

open import plfa.cap3.Relations using (_<_; s<s; z<s)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (cong)
open import plfa.cap6.Connectives using (→-distrib-⊎; _⊎_; inj₁; inj₂; _×_; ⟨_,_⟩)
open import plfa.cap5.Isomorphism using (_≲_; _⇔_)

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

cong-suc : ∀ {m n : ℕ}
  → suc m ≡ suc n
    --------------
  → m ≡ n
cong-suc refl = refl

trichotomy-<-¬≡ : ∀ {m n : ℕ}
  → m < n
    ------
  → ¬ (m ≡ n)
trichotomy-<-¬≡ z<s = λ()
trichotomy-<-¬≡ (s<s m<n) = λ{sm≡sn → trichotomy-<-¬≡ m<n (cong-suc sm≡sn)}

trichotomy-<-¬> : ∀ {m n : ℕ}
  → m < n
    ------
  → ¬ (n < m)
trichotomy-<-¬> z<s = λ()
trichotomy-<-¬> (s<s prf) = λ{ (s<s m>n) → trichotomy-<-¬> prf m>n }

trichotomy-≡-¬< : ∀ {m n : ℕ}
  → m ≡ n
    ------
  → ¬ (m < n)
trichotomy-≡-¬< refl = λ{ m<m → ¬-elim (trichotomy-<-¬≡ m<m) refl}

trichotomy-≡-¬> : ∀ {m n : ℕ}
  → m ≡ n
    ------
  → ¬ (n < m)
trichotomy-≡-¬> refl = λ{ m<m → ¬-elim (trichotomy-<-¬≡ m<m) refl }

-- -- better!
-- trichotomy :
--   ∀ m n →
--   (m < n × ¬ m ≡ n × ¬ n < m) ⊎
--     (¬ m < n × m ≡ n × ¬ n < m) ⊎
--       (¬ m < n × ¬ m ≡ n × n < m)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× = →-distrib-⊎

-- ×-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- ×-dual-⊎ =
--   record
--     { to = λ{ ¬a×b → {!!} }
--     ; from = {!!}
--     ; from∘to = {!!}
--     ; to∘from = {!!}
--     }

⊎-→-× : ∀ {A B : Set} → ((¬ A) ⊎ (¬ B)) → (¬ (A × B))
⊎-→-× (inj₁ ¬a) = λ{ ⟨ a , b ⟩ → ¬a a }
⊎-→-× (inj₂ ¬b) = λ{ ⟨ a , b ⟩ → ¬b b }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable ¬em = ¬em (inj₂ λ{ a → ¬em (inj₁ a)})

Classical : ∀ {A B : Set}
  → (A ⊎ ¬ A) ⇔ (¬ ¬ A → A)
  × (¬ ¬ A → A) ⇔ (((A → B) → A) → A)
  × (((A → B) → A) → A) ⇔ ((A → B) → ¬ A ⊎ B)
  × (A ⊎ ¬ A) ⇔ (¬ (¬ A × ¬ B) → A ⊎ B)
Classical =
  ⟨ record { to = λ{ (inj₁ a)  →  λ{ ¬¬a → a }
                   ; (inj₂ ¬a) →  λ{ ¬¬a → ⊥-elim (¬-elim ¬¬a ¬a) }
                   }
           -- ; from = λ{ f → inj₂ (¬¬¬-elim (contraposition f λ{ a → {!f (¬¬-intro a)!} })) }
           ; from = λ{ f → em }
           }
  , ⟨ record { to = λ{ f → λ{ k → f λ{¬a → ¬a (⊥-elim (¬-elim ¬a (k λ{ a → ⊥-elim (¬-elim ¬a a) })))} } }
             -- ; from = λ{ f → λ{ ¬¬a → f (⊥-elim (¬¬a λ{ a → {!!} })) } }
             -- ; from = λ{ f → λ{ ¬¬a → f λ{ g → ⊥-elim (¬-elim ¬¬a λ{ a → {!!} }) } } }
             ; from = λ{ f → {!!} }
             }
    , ⟨ record { to = {!!}
               ; from = {!!}
               }
      , record { to = {!!}
               ; from = {!!}
               }
      ⟩
    ⟩
  ⟩
