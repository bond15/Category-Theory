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


fmap-maybe : {A B : agda.Category.PreCategory.Ob Agda₀} -> (f : A -> B) -> (m : Maybe A) -> Maybe B
fmap-maybe = Functor.F₁ Maybe-Endofunctor

-- functor composition example


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

-- Haskell
-- data Prod a b = Prod a b
-- Prod :: (Type × Type) -> Type



-- Const Functor (Haskell style)
data Const (A : Set₀) : Set₀ where
  const : A -> Const A

data Unit : Set₀ where
  unit : Unit

-- alternative def
Const-Functor : Functor Agda₀ Agda₀
Const-Functor = record
  { F₀ = λ X -> Unit
  ; F₁ = λ _ -> λ u -> u
  ; identity = refl
  ; homomorphism = λ f g -> refl
  }


Id-Functor : Functor Agda₀ Agda₀
Id-Functor = record
  { F₀ = λ X -> X
  ; F₁ = λ f -> f
  ; identity = refl
  ; homomorphism = λ f -> λ g -> refl
  }


-- really F₀ should be a composition of bifunctors
-- Either (Const ) (Identity A) ≅ Maybe A
Maybe-Functor : Functor Agda₀ Agda₀
Maybe-Functor = record
  { F₀ = λ T -> (Functor.F₀ Either-EndoBifunctor ((Functor.F₀ Const-Functor) T , ( Id.F₀ T )))-- directly,  λ T ->  (Unit , T )
  ; F₁ = λ fg -> λ p -> (Functor.F₁ Either-EndoBifunctor {! ((Functor.F₁ Const-Functor) , ? )  !} p )
  ; identity = {!   !}
  ; homomorphism = {!   !}
  } where
    Id = Id-Functor
    C = Const-Functor









--
