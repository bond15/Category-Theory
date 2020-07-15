module TypedMat where
open import Data.Nat using (_*_; ℕ; _+_)
open import Level
-- Typelevel ℕ encoding
-- Join A B
-- Fork A
--      B
-- Ex) Mat ℕ 2 1 => [ n₁ n₂ ]
data Mat (A : Set) : ℕ -> ℕ ->  Set where -- col -> row
  One : (a : A) -> Mat A 1 1
  Join : ∀ {c₁ c₂ r : ℕ } -> (Mat A c₁ r) -> Mat A c₂ r -> Mat A (c₁ + c₂) r
  Fork : ∀ {c r₁ r₂ : ℕ } -> (Mat A c r₁)-> Mat A c r₂ -> Mat A c (r₁ + r₂)

-- ex matrix) [7 8]
ex₁ : Mat ℕ 2 1
ex₁ = Join (One 7) (One 8)


-- 7 8
-- 7 8
_ : Mat ℕ 2 2
_ = Fork ex₁ ex₁

-- composition is matrix multiplication
-- Need ac hoc polymorphism on type A for numerical operations (Num typeclass)
-- For now, just use ℕ matrix

ℕ-Mat = Mat ℕ
-- postulate
--  _++_ : ∀{m n : ℕ} -> ℕ-Mat n m -> ℕ-Mat n m -> ℕ-Mat n m
--(One n) ++ (One m) = One (n + n)
--(Join a b) ++ (Join c d) = Join (a ++ c) (b ++ d)
--(Fork a b) ++ (Fork c d) = Fork (a ++ c) (b ++ d)

-- _∘_ : ∀ {m n p : ℕ}{A : Set} -> ℕ-Mat m n -> ℕ-Mat n p -> ℕ-Mat m p
-- (One a) ∘ (One b) = (One (a * b))
-- (Join a b) ∘ (Fork c d) = (a ∘ c) ++ (b ∘ d)




-- Unification problems with dependently typed Mat, try Either trees encoding

data Either {ℓ : Level}(A B : Set ℓ) : Set ℓ where
  left : A -> Either A B
  right : B -> Either A B

data Unit {ℓ : Level}: Set ℓ where
  unit : Unit


data Matrix {ℓ : Level }(E : Set ℓ) : Set ℓ -> Set ℓ -> Set (suc ℓ) where
  One : E -> Matrix E Unit Unit
  Join : ∀ {A B C} -> Matrix E A C -> Matrix E B C -> Matrix E (Either A B) C
  Fork : ∀ {A B C} -> Matrix E C A -> Matrix E C B -> Matrix E C (Either A B)

_ : Matrix ℕ Unit Unit
_ = One 7

_ : Matrix ℕ (Either Unit Unit) (Either Unit Unit)
_ = Fork (Join (One 1) (One 2)) (Join (One 3) (One 4))
-- 1 2
-- 3 4

ℕ-Matrix = Matrix ℕ

_++_ : ∀ {R C} -> ℕ-Matrix R C -> ℕ-Matrix R C -> ℕ-Matrix R C
(One n) ++ (One m) = One (n + m)
(Join a b) ++ (Join c d) = (Join (a ++ c) (b ++ d))
(Fork a b) ++ (Fork c d) = (Fork (a ++ c) (b ++ d))

-- still pattern matching Unification problems....













--
