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

linear : (m : ℝ²) → Segment
linear m = lin (lin m)

bezier : (a b c : ℝ²) → Segment
bezier a b c = cub (cub a b c)


data Located (A : Set) : Set where
  loc : ℝ² → A → Located A

Path : Set
Path = List Segment
