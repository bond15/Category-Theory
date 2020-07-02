{-# OPTIONS  --allow-unsolved-metas #-}

module agda.Functors where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Axiom.Extensionality.Propositional using (Extensionality)
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

functor-∘ : ∀ {ℓ₁ ℓ₂ : Level } (ℬ 𝒞 𝒟 : PreCategory ℓ₁ ℓ₂) -> (ℱ : Functor 𝒞 𝒟) -> (𝒢 : Functor ℬ 𝒞) -> Functor ℬ 𝒟
functor-∘ = λ ℬ 𝒞 𝒟 -> λ ℱ 𝒢 -> record
  { F₀ = λ b -> Functor.F₀ ℱ (Functor.F₀ 𝒢 b) -- some object A in ℬ   to  ℱ ( 𝒢 A) an object in 𝒟
  ; F₁ = λ Bf -> Functor.F₁ ℱ (Functor.F₁ 𝒢 Bf) -- some arrow f : A ⇒ B in ℬ to ℱ ( 𝒢 f) an arrow ℱ ( 𝒢 A) ⇒ ℱ ( 𝒢 B) in 𝒟
  ; identity =  λ {B} -> cong (λ x -> ?) {!   !}  --λ {B} -> cong {! (Functor.identity 𝒢)  !} {!   !}
  ; homomorphism = _
  }

-- TODO Bifunctor composition

-- really a functor from a product category to a category
record BiFunctor {ℓ₁ ℓ₂ : Level} (C : PreCategory ℓ₁ ℓ₂) (D : PreCategory ℓ₁ ℓ₂) (E : PreCategory ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  private module C = PreCategory C
  private module D = PreCategory D
  private module E = PreCategory E
  field
    F₀ : E.Ob -- TODO
