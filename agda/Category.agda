module agda.Category where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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




--data _×_ (A B : Set) : Set where
--  _,_ : A -> B -> A × B

--fst : ∀ {A B} -> _×_ {zero} A B -> A
--fst : ∀ {A B} -> A × B -> A
--fst (a , b) = a

--snd : ∀ {A B} -> A × B -> B
--snd (a , b) = b


--_ :  Rel (Set₀ × Set₀) zero
--_ = λ p₁ -> λ p₂ -> (((fst p₁) -> (fst p₂)) × ((snd p₁) -> (snd p₂)))

--_ : (r₁ : Rel Set₀ zero) -> (r₂ : Rel Set₀ zero ) -> Rel (Set₀ × Set₀) zero
--_ = λ r₁ -> λ r₂ -> λ p₁ -> λ p₂ -> (r₁ (fst p₁) (fst p₁)) × (r₂ (snd p₁) (snd p₂))


_ : ∀ (A B C D : Set) -> (ev₁ : A ≡ C) -> (ev₂ : B ≡ D) -> ((A × B) ≡ (C × D))
_ = λ A B C D -> λ ev₁ ev₂ -> cong₂ _×_ ev₁ ev₂


module Product where

--  variable
--    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

  ProductCategory : (ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level) (𝒞 : PreCategory ℓ₁ ℓ₂) (𝒟 : PreCategory ℓ₃ ℓ₄) -> (PreCategory (ℓ₁ ⊔ ℓ₃) (ℓ₂ ⊔ ℓ₄))
  ProductCategory  a s d f 𝒞 𝒟 = record
    { Ob = PreCategory.Ob 𝒞 × PreCategory.Ob 𝒟
    ; _⇒_ = λ c×d -> λ c×d' -> (PreCategory._⇒_ 𝒞 (proj₁ c×d) (proj₁ c×d')) × (PreCategory._⇒_ 𝒟 (proj₂ c×d) (proj₂ c×d')) -- λ c×d -> λ c×d' ->  (((fst c×d) -> (fst c×d')) × ((snd c×d) -> (snd c×d')))
    -- λ c×d -> λ c×d' ->  (PreCategory._⇒_ 𝒞 (fst c×d) (fst c×d')) × (PreCategory._⇒_ 𝒟 (snd c×d) (snd c×d))
    --(((proj₁ c×d) -> (proj₁ c×d')) × ((proj₂ c×d) -> (proj₂ c×d')))
    ; _∘_ = λ ff -> λ gg -> (PreCategory._∘_ 𝒞 (proj₁ ff) (proj₁ gg)) , (PreCategory._∘_ 𝒟 (proj₂ ff) (proj₂ gg) )
    ; id = PreCategory.id 𝒞 , PreCategory.id 𝒟
    ; idˡ = λ ff -> cong₂ _,_ (PreCategory.idˡ 𝒞 (proj₁ ff)) (PreCategory.idˡ 𝒟 (proj₂ ff))
    ; idʳ = λ ff -> cong₂ _,_ (PreCategory.idʳ 𝒞 (proj₁ ff)) (PreCategory.idʳ 𝒟 (proj₂ ff))
    ; ∘-assoc = λ ff -> λ gg -> λ hh -> cong₂ _,_ (PreCategory.∘-assoc 𝒞 (proj₁ ff) (proj₁ gg) (proj₁ hh)) (PreCategory.∘-assoc 𝒟 (proj₂ ff) (proj₂ gg) (proj₂ hh))
    }-- where
    --  prf : A -> B ->












--
