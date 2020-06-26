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

module Objects {ℓ₁ ℓ₂} (𝒫 : PreCategory ℓ₁ ℓ₂) where

  open PreCategory 𝒫 -- \McP

  record Initial : Set(ℓ₁ ⊔ ℓ₂) where
    field
      ⊥ : Ob
      ! : {A : Ob} -> ⊥ ⇒ A
      !-unique : ∀ {A} -> (f : ⊥ ⇒ A) -> ! ≡ f

  record Terminal : Set(ℓ₁ ⊔ ℓ₂) where
    field
      ⊤ : Ob
      ! : {A : Ob} -> A ⇒ ⊤
    --  !-unique : ∀ {A} -> (f : A ⇒ ⊤) -> ! ≡ f

  private
    variable
      O₁ O₂ : Ob
      p q r : O₁ ⇒ O₂
  record Product (A B : Ob) : Set(ℓ₁ ⊔ ℓ₂) where
    field
      A×B : Ob
      π₁ : A×B ⇒ A
      π₂ : A×B ⇒ B
      ⟨_,_⟩ : ∀ {C} -> C ⇒ A -> C ⇒ B -> C ⇒ A×B

      proj₁ : π₁ ∘ ⟨ p , q ⟩ ≡ p
      proj₂ : π₂ ∘ ⟨ p , q ⟩ ≡ q
    --  unique : π₁ ∘ p ≡ q -> π₂ ∘ p ≡ r -> ⟨ q , r ⟩ ≡ p

  record Coproduct (A B : Ob) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      A+B : Ob
      inˡ : A ⇒ A+B
      inʳ : B ⇒ A+B
      _+_ : ∀ {C} -> A ⇒ C -> B ⇒ C -> A+B ⇒ C

      injˡ : (p + q) ∘ inˡ ≡ p
      injʳ : (p + q) ∘ inʳ ≡ q
