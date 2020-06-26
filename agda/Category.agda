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

-- ‌\McC
𝒞 = zero

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






-- initial Object
-- unique up to unique isomorphism
--record initial {ℓ₁ ℓ₂} (𝒞 : PreCategory ℓ₁ ℓ₂) : Set(ℓ₁ ⊔ ℓ₂) where
--  field
--    ⊥ : PreCategory.Ob 𝒞
--    ! : {A : PreCategory.Ob 𝒞} -> (⊥ -> A)


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


-- really a functor from a product category to a category
record BiFunctor {ℓ₁ ℓ₂ : Level} (C : PreCategory ℓ₁ ℓ₂) (D : PreCategory ℓ₁ ℓ₂) (E : PreCategory ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  private module C = PreCategory C
  private module D = PreCategory D
  private module E = PreCategory E
  field
    F₀ : E.Ob -- TODO



module X {ℓ₁ ℓ₂} (𝒫 : PreCategory ℓ₁ ℓ₂) where

  open PreCategory 𝒫

  record Initial : Set(ℓ₁ ⊔ ℓ₂) where
    field
      ⊥ : Ob
      ! : {A : Ob} -> ⊥ ⇒ A
      !-unique : ∀ {A} -> (f : ⊥ ⇒ A) -> ! ≡ f

  record Terminal : Set(ℓ₁ ⊔ ℓ₂) where
    field
      ⊤ : Ob
      ! : {A : Ob} -> A ⇒ ⊤
      !-unique : ∀ {A} -> (f : A ⇒ ⊤) -> ! ≡ f

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
      --× : Ob
      --π₁ : ∀ {A} -> x ⇒ A
      --π₂ : ∀ {B} -> x ⇒ B
      --! : ∀{A B} -> ∀ {C} -> (p : C ⇒ A) -> (q : C ⇒ B) -> (Σ (m : C ⇒ ×) Ob)

        --(Σ (m : C ⇒ ×) (prf : Σ (p ≡ π₁ ∘ m) (q ≡ π₂ ∘ m)))
      --_×_ : Ob -> Ob -> Ob
      --π₁ : ∀ {A B} -> (A × B) ⇒ A
      --π₂ : ∀ {A B} -> (A × B) ⇒ B


open X

data Void : Set₀ where

postulate
    -- extensionality for regular function types
    -- gawd damn just use cubical agda
    -- prove and earn that extensionality
  extensionality : ∀ {A B : Set }{f g : A -> B}
    -> (∀ (x : A) -> f x ≡ g x)
    ---------------------------
    -> f ≡ g

Void-elim : ∀ {A : Set} -- Void-E  absurd
  -> Void
  -----
  -> A
Void-elim ()

Void-Initial : Initial( Agda₀ )
Void-Initial = record
    { ⊥ = Void
    ; ! = λ ()
    ; !-unique = λ f -> extensionality λ v -> Void-elim v
    }

data Unit : Set₀ where
  unit : Unit


Unit-Terminal : Terminal( Agda₀ )
Unit-Terminal = record
    { ⊤ = Unit
    ; ! = λ a -> unit
    ; !-unique = λ f -> extensionality λ a -> _
    }

data _X_ (A B : Set₀) : Set₀ where
  _x_ : A -> B -> A X B

fst : ∀ {A B} -> A X B -> A
fst (a x b) = a

snd : ∀ {A B} -> A X B -> B
snd (a x b) = b

_ : Unit X Unit
_ = unit x unit

open PreCategory
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

data Either (A B : Set₀) : Set₀ where
  left : A -> Either A B
  right : B -> Either A B

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





--Adamek and Lambek theorems



--
