open import Algebra using (CommutativeRing)
open import Algebra.Module using (Module)

module Carta.Segment
  {r ℓr m ℓm}
  {CR : CommutativeRing r ℓr}
  (M : Module CR m ℓm)
  where


open import Level using (_⊔_)
open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Product using (_×_)
open Module M renaming (Carrierᴹ to A)
open CommutativeRing CR renaming (Carrier to S)


data Segment : Set m where
  cub : (a b c : A) → Segment
  lin : (a : A) → Segment

scale : (r : S) (s : Segment) → Segment
scale r (cub a b c) = cub (r *ₗ a) (r *ₗ b) (r *ₗ c)
scale r (lin a) = lin (r *ₗ a)

Trail : Set m
Trail = List Segment

record Object : Set m where
  constructor obj
  field
    closed : Bool
    trail : Trail


data Located {b} (B : Set b) : Set (b ⊔ m) where
  loc : A → B → Located B

record Diagram {a} (Attrs : Set a) : Set (a ⊔ m) where
  constructor diagram
  field
    objs : List (Attrs × (Located Object))

