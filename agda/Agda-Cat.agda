module agda.Agda-Cat where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Level

open import agda.Category
open import agda.Theorems
open Objects

-- Agda₀ Category
-- Objects := Types ∈ Set₀
-- Arrows := function types ∈ Set₀

Agda₀ : PreCategory (suc zero) zero
Agda₀ = record
  { Ob = Set₀
  ; _⇒_ = λ x y -> x -> y -- x y : Ob  , Hom := x -> y
  ; _∘_ =  λ f g x -> f(g x)
  ; id = λ x -> x
  ; idˡ = λ f -> refl
  ; idʳ = λ f -> refl
  ; ∘-assoc = λ f g h -> refl
  }

-- Universal Constructions

data Void : Set₀ where

Void-elim : ∀ {A : Set} -> Void -> A
Void-elim ()

data Unit : Set₀ where
  unit : Unit

data _X_ (A B : Set₀) : Set₀ where
  _x_ : A -> B -> A X B

fst : ∀ {A B} -> A X B -> A
fst (a x b) = a

snd : ∀ {A B} -> A X B -> B
snd (a x b) = b

data Either (A B : Set₀) : Set₀ where
  left : A -> Either A B
  right : B -> Either A B


-- Proofs of Univeral Constructions

Void-Initial : Initial Agda₀
Void-Initial = record
    { ⊥ = Void
    ; ! = λ ()
    ; !-unique = λ f -> extensionality λ v -> Void-elim v
    }

Unit-Terminal : Terminal Agda₀
Unit-Terminal = record
    { ⊤ = Unit
    ; ! = λ a -> unit
  --  ; !-unique = λ f -> extensionality λ a -> _
    }


X-Product : ∀ (A B : Set₀) ->  Product Agda₀ A B
X-Product A B = record
    { A×B = A X B
    ; π₁ = fst
    ; π₂ = snd
    ; ⟨_,_⟩ = λ f -> λ g -> (λ c -> (f c) x (g c))
    ; proj₁ = refl
    ; proj₂ = refl
  --  ; unique = _
    }

Either-Coproduct : ∀ (A B : Set₀) -> Coproduct Agda₀ A B
Either-Coproduct A B = record
    { A+B = Either A B
    ; inˡ = left
    ; inʳ = right
    ; _+_ = λ f -> λ g -> λ { (left a) -> f a
                            ; (right b) -> g b }
    ; injˡ = refl
    ; injʳ = refl
    }
