module agda.Functors where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import agda.Category
open import Level

-- Functor defined  w/o laws between two PreCategories
record Functor {ℓ₁ ℓ₂ : Level } (C : PreCategory ℓ₁ ℓ₂) (D : PreCategory ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  private module C = PreCategory C
  private module D = PreCategory D
  field
    F₀ : C.Ob -> D.Ob
    F₁ : ∀ {A B} (f : C._⇒_ A B ) -> D._⇒_ (F₀ A) (F₀ B)

    identity : ∀ {A} -> (F₁ (C.id {A})) ≡ D.id {(F₀ A)}
    homomorphism : ∀ {A B C} -> (f : C._⇒_ A B) -> (g : C._⇒_ B C) ->
      F₁ (C._∘_ g f) ≡ D._∘_ (F₁ g) (F₁ f)


-- really a functor from a product category to a category
record BiFunctor {ℓ₁ ℓ₂ : Level} (C : PreCategory ℓ₁ ℓ₂) (D : PreCategory ℓ₁ ℓ₂) (E : PreCategory ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  private module C = PreCategory C
  private module D = PreCategory D
  private module E = PreCategory E
  field
    F₀ : E.Ob -- TODO
