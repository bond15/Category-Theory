module agda.Category where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Level

-- same definitions in Relation.Binary using (Rel)

REL : ∀ { ℓ₁ ℓ₂ : Level} -> Set ℓ₁ -> Set ℓ₂ -> (ℓ₃ : Level) -> Set (ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃)
REL A B ℓ = A -> B -> Set ℓ

Rel : ∀ {ℓ₁ : Level} -> Set ℓ₁ -> (ℓ₂ : Level) -> Set (ℓ₁ ⊔ suc ℓ₂)
Rel A ℓ = REL A A ℓ

record PreCategory(l m : Level) : Set(suc (l ⊔ m)) where
  field
    Ob : Set l
    Hom : Rel Ob m
    _∘_  : ∀ {x y z : Ob} -> Hom y z -> Hom x y -> Hom x z
    id : ∀ (o : Ob) -> Hom o o
    idˡ : ∀ {x y : Ob} (f : Hom x y) -> f ∘ (id x) ≡ f
    idʳ : ∀ {x y : Ob} (f : Hom x y) -> (id y) ∘ f ≡ f
    ∘-assoc : ∀ {x y z w : Ob} (f : Hom x y) (g : Hom y z) (h : Hom z w) -> h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f



Agda-0 : PreCategory (suc zero) zero
Agda-0 = record
  { Ob = Set₀
  ; Hom = λ x y -> x -> y
  ; _∘_ =  λ f g x -> f(g x)
  ; id = λ obj -> λ x -> x
  ; idˡ = λ f -> refl
  ; idʳ = λ f -> refl
  ; ∘-assoc = λ f g h -> refl
  }
