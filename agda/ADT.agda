module agda.ADT where
open import Level
open import agda.Category
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open PreCategory

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A -> B -> A × B

π₁ : ∀ {A B : Set} -> A × B -> A
π₁ ⟨ a , b ⟩ = a

π₂ : ∀ {A B : Set} -> A × B -> B
π₂ ⟨ a , b ⟩ = b

data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A

postulate
    -- extensionality for regular function types
    -- gawd damn just use cubical agda
    -- prove and earn that extensionality
  extensionality : ∀ {A B : Set }{f g : A -> B}
    -> (∀ (x : A) -> f x ≡ g x)
    ---------------------------
    -> f ≡ g

-- Haskell Functors are typically EndoFunctors
Endofunctor = Functor Agda₀ Agda₀

Maybe-Endofunctor : Endofunctor
Maybe-Endofunctor = record
  { F₀ = λ x -> Maybe x
  ; F₁ = λ f -> λ{ Nothing -> Nothing
                 ; (Just a) -> (Just (f a)) }
  ; identity = λ {A} ->
    extensionality λ { Nothing -> refl
                    ; (Just a) -> refl }
  ; homomorphism = λ f g ->
    extensionality λ { Nothing -> refl
                        ; (Just a) -> refl }
  }

-- compare this to Haskell
-- this maps objects in Hask to objects in Hask
-- data Maybe a = Just a | Nothing
-- Maybe : Type -> Type
-- or Hask -> Hask

-- instance Functor Maybe where
-- fmap f (Just a) = Just (f a)
-- fmap f Nothing = Nothing
