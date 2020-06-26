module agda.UniversalConstructions where


open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import agda.Category using (PreCategory)

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
