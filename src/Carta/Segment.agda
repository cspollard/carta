module Carta.Segment where

open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Float using () renaming (Float to ℝ)

ℝ² : Set
ℝ² = ℝ × ℝ

r2 : (x y : ℝ) → ℝ²
r2 x y = x , y

record Cubic : Set where
  constructor cub
  field
    a b c : ℝ²

record Linear : Set where
  constructor lin
  field
    a : ℝ²

data Segment : Set where
  cub : Cubic → Segment
  lin : Linear → Segment

linear : (dxy : ℝ²) → Segment
linear dxy = lin (lin dxy)

bezier : (a b c : ℝ²) → Segment
bezier a b c = cub (cub a b c)

data Located (A : Set) : Set where
  loc : ℝ² → A → Located A

Trail : Set
Trail = List Segment

Path : Set
Path = Located Trail

record Attrs : Set where
  constructor attrs

Object : Set
Object = Attrs × Path

Diagram : Set
Diagram = List Object
