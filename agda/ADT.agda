module agda.ADT where
open import Level
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import agda.Functors using (Functor)
open import agda.Agda-Cat using (Agda₀)
open import agda.Theorems using (extensionality)

data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A

-- Haskell Functors are typically EndoFunctors
Endofunctor : Set₁
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
