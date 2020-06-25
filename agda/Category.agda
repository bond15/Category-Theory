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

-- ‌\McC
𝒞 = zero

Agda₀ : PreCategory (suc zero) zero
Agda₀ = record
  { Ob = Set₀
  ; _⇒_ = λ x y -> x -> y -- x y : Ob  , Hom := x -> y
  ; _∘_ =  λ f g x -> f(g x)
  ; id = λ x -> x
  ; idˡ = λ f -> refl
  ; idʳ = λ f -> refl
  ; ∘-assoc = λ f g h -> refl
  }






-- initial Object
-- unique up to unique isomorphism
--record initial {ℓ₁ ℓ₂} (𝒞 : PreCategory ℓ₁ ℓ₂) : Set(ℓ₁ ⊔ ℓ₂) where
--  field
--    ⊥ : PreCategory.Ob 𝒞
--    ! : {A : PreCategory.Ob 𝒞} -> (⊥ -> A)


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


-- really a functor from a cartesian category to a category
record BiFunctor {ℓ₁ ℓ₂ : Level} (C : PreCategory ℓ₁ ℓ₂) (D : PreCategory ℓ₁ ℓ₂) (E : PreCategory ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  private module C = PreCategory C
  private module D = PreCategory D
  private module E = PreCategory E
  field
    F₀ : E.Ob -- TODO


module X {ℓ₁ ℓ₂} (𝒫 : PreCategory ℓ₁ ℓ₂) where

  open PreCategory 𝒫

  record Initial : Set(ℓ₁ ⊔ ℓ₂) where
    field
      ⊥ : Ob
      ! : {A : Ob} -> ⊥ ⇒ A
      !-unique : ∀ {A} -> (f : ⊥ ⇒ A) -> ! ≡ f
