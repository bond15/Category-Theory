module agda.Theorems where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

-- Axiom
postulate
  extensionality : ∀ {A B : Set }{f g : A -> B}
    -> (∀ (x : A) -> f x ≡ g x)
    ---------------------------
    -> f ≡ g

-- TODO Adamek's Theorem

-- TODO Lambek's Theorem
