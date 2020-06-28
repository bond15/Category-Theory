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




data _×_ {ℓ₁ ℓ₂} (A : Set ℓ₁)(B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : A -> B -> A × B

fst : ∀ {A B} -> A × B -> A
fst (a , b) = a

snd : ∀ {A B} -> A × B -> B
snd (a , b) = b


--_ :  Rel (Set₀ × Set₀) zero
--_ = λ p₁ -> λ p₂ -> (((fst p₁) -> (fst p₂)) × ((snd p₁) -> (snd p₂)))

--_ : (r₁ : Rel Set₀ zero) -> (r₂ : Rel Set₀ zero ) -> Rel (Set₀ × Set₀) zero
--_ = λ r₁ -> λ r₂ -> λ p₁ -> λ p₂ -> (r₁ (fst p₁) (fst p₁)) × (r₂ (snd p₁) (snd p₂))




module Product where


--  variable
--    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- ProductCategory : (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) (𝒞 : PreCategory ℓ₁ ℓ₂) (𝒟 : PreCategory ℓ₃ ℓ₄) -> (PreCategory (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄))
--  ProductCategory  a s d f 𝒞 𝒟 = record
--    { Ob = PreCategory.Ob 𝒞 × PreCategory.Ob 𝒟
--    ; _⇒_ = λ c×d -> λ c×d' -> {! (((fst c×d) -> (fst c×d')) × ((snd c×d) -> (snd c×d')))  !}  -- λ c×d -> λ c×d' ->  (PreCategory._⇒_ 𝒞 (fst c×d) (fst c×d')) × (PreCategory._⇒_ 𝒟 (snd c×d) (snd c×d))
--    -- (((fst c×d) -> (fst c×d')) × ((snd c×d) -> (snd c×d')))
--    ; _∘_ = {!   !}
--    ; id = {!   !} -- PreCategory.id 𝒞 , PreCategory.id 𝒟
--    ; idˡ = {!   !}
--    ; idʳ = {!   !}
--    ; ∘-assoc = {!   !}
--    }



  --record ProductCategory : Set( suc (ℓ₁ ⊔ ℓ₂)) where
  --  open PreCategory
  --  field
  --    Ob×Ob : (Ob 𝒞 × Ob 𝒟)
  --    _⇒×⇒_ : _×_ {ℓ₂} (_⇒_ 𝒞 (Ob 𝒞) (Ob 𝒞)) (_⇒_ 𝒟 (Ob 𝒟) (Ob 𝒟))   --(_⇒_ 𝒞 (Ob 𝒞) (Ob 𝒞) × _⇒_)














--
