module agda.Category where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import agda.Theorems using (extensionality)

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

module Product where

  ProductCategory : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} (𝒞 : PreCategory ℓ₁ ℓ₂) (𝒟 : PreCategory ℓ₃ ℓ₄) -> (PreCategory (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄))
  ProductCategory 𝒞 𝒟 = record
    { Ob = 𝒞.Ob × 𝒟.Ob
    ; _⇒_ = λ c×d -> λ c×d' -> (𝒞._⇒_ (π₁ c×d) (π₁ c×d')) × (𝒟._⇒_ (π₂ c×d) (π₂ c×d'))
    ; _∘_ = λ ff -> λ gg ->  (𝒞._∘_ (π₁ ff) (π₁ gg)) ,  (𝒟._∘_ (π₂ ff) (π₂ gg) )
    ; id = 𝒞.id , 𝒟.id
    ; idˡ = λ ff -> cong₂ _,_ (𝒞.idˡ (π₁ ff)) (𝒟.idˡ (π₂ ff))
    ; idʳ = λ ff -> cong₂ _,_ (𝒞.idʳ (π₁ ff)) (𝒟.idʳ (π₂ ff))
    ; ∘-assoc = λ ff -> λ gg -> λ hh -> cong₂ _,_ (𝒞.∘-assoc (π₁ ff) (π₁ gg) (π₁ hh)) (𝒟.∘-assoc (π₂ ff) (π₂ gg) (π₂ hh))
    } where
      module 𝒞 = PreCategory 𝒞
      module 𝒟 = PreCategory 𝒟
      -- evidence of suffering

      --_ :  Rel (Set₀ × Set₀) zero
      --_ = λ p₁ -> λ p₂ -> (((fst p₁) -> (fst p₂)) × ((snd p₁) -> (snd p₂)))

      --_ : (r₁ : Rel Set₀ zero) -> (r₂ : Rel Set₀ zero ) -> Rel (Set₀ × Set₀) zero
      --_ = λ r₁ -> λ r₂ -> λ p₁ -> λ p₂ -> (r₁ (fst p₁) (fst p₁)) × (r₂ (snd p₁) (snd p₂))


      -- _ : ∀ (A B C D : Set) -> (ev₁ : A ≡ C) -> (ev₂ : B ≡ D) -> ((A × B) ≡ (C × D))
      -- _ = λ A B C D -> λ ev₁ ev₂ -> cong₂ _×_ ev₁ ev₂











--
