module Carta.Prims where

open import Function using (_∘_; _$_; flip)
open import Data.Product using (uncurry; _,_)
open import Data.List using (List; foldl) renaming (map to mapl)
open import Data.Float using () renaming (Float to ℝ)
open import Carta.Segment

-- explicitly SVG
{-# FOREIGN GHC import Diagrams.Backend.SVG #-}
{-# FOREIGN GHC import Diagrams.Prelude #-}

postulate
  HDiagram : Set
  HPoint : Set
  HSegment : Set
  HLocated : Set → Set
  HPath : Set
  HV2 : Set
  hv2 : (x y : ℝ) → HV2
  hpoint2 : (x y : ℝ) → HPoint
  hat : List HSegment → HPoint → HLocated (List HSegment)
  hstraight : (a : HV2) → HSegment
  hbezier3 : (a b c : HV2) → HSegment
  htoPath : HLocated (List HSegment) → HPath
  hstroke : HPath → HDiagram

{-# COMPILE GHC HV2 = type V2 Double #-}
{-# COMPILE GHC HSegment = type Segment Closed V2 Double #-}
{-# COMPILE GHC HLocated = type Located #-}
{-# COMPILE GHC HPoint = type Point V2 Double #-}
{-# COMPILE GHC HPath = type Path V2 Double #-}
{-# COMPILE GHC HDiagram = type Diagram SVG #-}
{-# COMPILE GHC hv2 = V2 #-}
{-# COMPILE GHC hpoint2 = \ x y -> P (V2 x y) #-}
{-# COMPILE GHC hat = at #-}
{-# COMPILE GHC hstraight = straight #-}
{-# COMPILE GHC hbezier3 = bezier3 #-}
{-# COMPILE GHC htoPath = toPath #-}
{-# COMPILE GHC hstroke = stroke #-}


compile : Segment → HSegment
compile (cub (cub a b c)) =
  hbezier3 (uncurry hv2 a) (uncurry hv2 b) (uncurry hv2 c)
compile (lin (lin a)) = hstraight (uncurry hv2 a)

compiles : List Segment → HDiagram
compiles = hstroke ∘ htoPath ∘ flip hat (hpoint2 0.0 0.0) ∘ mapl compile
