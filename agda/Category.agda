module agda.Category where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Level

-- same definitions in Relation.Binary using (Rel)

REL : ∀ { ℓ₁ ℓ₂ : Level} -> Set ℓ₁ -> Set ℓ₂ -> (ℓ₃ : Level) -> Set (ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃)
REL A B ℓ = A -> B -> Set ℓ

Rel : ∀ {ℓ₁ : Level} -> Set ℓ₁ -> (ℓ₂ : Level) -> Set (ℓ₁ ⊔ suc ℓ₂)
Rel A ℓ = REL A A ℓ

-- in agda-categories,
-- they abstract over the equality type
record PreCategory(l m : Level) : Set(suc (l ⊔ m)) where
  field
    Ob : Set l
    _⇒_ : Rel Ob m
    _∘_  : ∀ {x y z : Ob} -> y ⇒ z -> x ⇒ y -> x ⇒ z
    id : ∀ {o : Ob} -> o ⇒ o
    idˡ : ∀ {x y : Ob} (f : x ⇒ y) -> f ∘ (id {x}) ≡ f
    idʳ : ∀ {x y : Ob} (f : x ⇒ y) -> (id {y}) ∘ f ≡ f
    ∘-assoc : ∀ {x y z w : Ob} (f : x ⇒ y) (g : y ⇒ z) (h : z ⇒ w) -> h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f


module Constructions {ℓ₁ ℓ₂} (𝒞 𝒟 : PreCategory ℓ₁ ℓ₂) where

  data _×_ {ℓ₁}(A B : Set ℓ₁) : Set ℓ₁ where
    _,_ : A -> B -> A × B

  record ProductCategory : Set where
    open PreCategory
    field
      Ob×Ob : (Ob 𝒞 × Ob 𝒟)
      _⇒×⇒_ : _×_ {ℓ₂} (_⇒_ 𝒞 (Ob 𝒞) (Ob 𝒞)) (_⇒_ 𝒟 (Ob 𝒟) (Ob 𝒟))   --(_⇒_ 𝒞 (Ob 𝒞) (Ob 𝒞) × _⇒_)














--
