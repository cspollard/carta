module Carta.Trail where

open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Float using (_≤ᵇ_; _≈_; _≈?_) renaming (Float to ℝ)
open import Data.Float.Properties
open import Relation.Binary.Structures (_≈_)
open import Data.Bool using (T)
open import Relation.Nullary using (Dec; T?; ¬_; True; toWitness; _×-dec_)


_≉_ : (a b : ℝ) → Set
a ≉ b = ¬ (a ≈ b)

_≤_ : (a b : ℝ) → Set
a ≤ b = T (a ≤ᵇ b)


≤-isDecTotalOrder : IsDecTotalOrder _≤_
≤-isDecTotalOrder =
  record
  { isTotalOrder = isTotalOrder
  ; _≟_  = _≈?_
  ; _≤?_ = λ x y → T? (x ≤ᵇ y)
  }
  where
    postulate
      isTotalOrder : IsTotalOrder _≤_

open IsDecTotalOrder ≤-isDecTotalOrder
  using (_≤?_)
  renaming (isTotalOrder to ≤-isTotalOrder)


open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_
  using (_<_; <-isStrictTotalOrder₂)

open IsStrictTotalOrder (<-isStrictTotalOrder₂ ≤-isDecTotalOrder)
  using (_<?_)



ℝ² : Set
ℝ² = ℝ × ℝ


record UnitInt : Set where
-- record UnitInt : Set where
--   constructor [_∣_]
--   field
--     x : ℝ
--     0≤x<1 : (0.0 ≤ x) × (x < 1.0)


-- ui : (x : ℝ) {p : True (0.0 ≤? x)} {q : True (x <? 1.0)} → UnitInt
-- ui x {p} {q} = [ x ∣ toWitness p , toWitness q ]

-- _ : UnitInt
-- _ = ui 0.5


record Cubic : Set where
  constructor cub
  field
    a b : ℝ²

record Linear : Set where
  constructor lin
  field
    m : ℝ

data Segment : Set where
  cub : Cubic → Segment
  lin : Linear → Segment

Trail : Set
Trail = List Segment

Located : Set → Set
Located A = ℝ² × A

Path : Set
Path = List (Located Trail)

