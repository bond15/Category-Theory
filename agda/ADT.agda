module agda.ADT where
open import Level
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

import agda.Category
open agda.Category.Product using (ProductCategory)
open import agda.Functors using (Functor)
open import agda.Agda-Cat using (Agda₀)
open import agda.Theorems using (extensionality)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)


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


-- Bifunctors
Agda₀₀ = ProductCategory Agda₀ Agda₀

EndoBifunctor = Functor Agda₀₀ Agda₀

data Either (A B : Set₀) : Set₀ where
  left : A -> Either A B
  right : B -> Either A B

Either-EndoBifunctor : EndoBifunctor
Either-EndoBifunctor = record
    { F₀ = λ a×b -> Either (π₁ a×b) (π₂ a×b)
    ; F₁ = λ fg ->  λ { (left a) -> (left ((π₁ fg) a)); (right b) -> (right ((π₂ fg) b))}
    ; identity = λ {A} -> extensionality λ { (left a) -> refl ; (right b) -> refl }
    ; homomorphism = λ {A B C} -> λ f g -> extensionality λ { (left a) -> refl ; (right b) -> refl }
    }

-- Haskell
-- data Either a b = Left a | Right b
-- Either :: Type -> Type -> Type
-- or
-- Either :: (Type × Type) -> Type

-- Product EndoBifunctor
data _X_ (A B : Set₀) : Set₀ where
  _x_ : A -> B -> A X B

fst : ∀ {A B} -> A X B -> A
fst (a x b) = a

snd : ∀ {A B} -> A X B -> B
snd (a x b) = b

X-EndoBifunctor : EndoBifunctor
X-EndoBifunctor = record
  { F₀ = λ a×b -> (π₁ a×b) X (π₂ a×b)
  ; F₁ = λ fg -> λ p -> ((π₁ fg) (fst p)) x ((π₂ fg)(snd p))
  ; identity = λ {A} -> extensionality λ { (a x b) -> refl }
  ; homomorphism = λ {A B C} -> λ f g -> extensionality λ { (a x b) -> refl }
  }










--
