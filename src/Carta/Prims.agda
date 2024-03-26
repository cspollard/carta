module Carta.Prims where

open import Data.Unit using (⊤)
open import Function using (_∘_; _$_; flip)
open import Data.Product using (uncurry; _,_; _×_)
open import Data.List using (List; foldl; []; _∷_) renaming (map to mapl)
open import Data.Float using (_÷_) renaming (Float to ℝ; fromℕ to ℕ→ℝ)
open import Data.Float.Real
open import Algebra.Module
open import Level using (0ℓ)
open import Carta.Color


ℝ²-module : Module ℝ-commutativeRing 0ℓ 0ℓ
ℝ²-module = ℝⁿ-module 2

ℝ² : Set
ℝ² = ℝ × ℝ

open import Carta.Segment ℝ²-module public

-- explicitly SVG
{-# FOREIGN GHC import Diagrams.Backend.SVG #-}
{-# FOREIGN GHC import Diagrams.Prelude #-}
{-# FOREIGN GHC import Debug.Trace #-}

postulate
  HColour : Set
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
  htoPathClosed : HLocated (List HSegment) → HPath
  hstroke : HPath → HDiagram
  hlinecolour : HColour → HDiagram → HDiagram
  hfillcolour : HColour → HDiagram → HDiagram
  rgbacolour : (r g b a : ℝ) → HColour

{-# COMPILE GHC HColour = type AlphaColour Double #-}
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
{-# COMPILE GHC htoPathClosed = Path . fmap (mapLoc closeTrail) . pathTrails . toPath #-}
{-# COMPILE GHC hstroke = stroke #-}
{-# COMPILE GHC hlinecolour = \ c d -> d # lcA c #-}
{-# COMPILE GHC hfillcolour = \ c d -> d # fcA c #-}
{-# COMPILE GHC rgbacolour = \ r g b a -> sRGB r g b `withOpacity` a #-}


open import Data.Fin
private
  finToFloat : ∀ {n} (i : Fin n) → ℝ
  finToFloat {n} i = ℕ→ℝ (toℕ i) ÷ ℕ→ℝ n

  toHRGBA : RGBA → HColour
  toHRGBA (r , g , b , a) =
    uncurryₙ 4 rgbacolour (map finToFloat 4 (r , g , b , a))
    where
      open import Data.Product.Nary.NonDependent
      open import Data.Vec.Recursive

fillColor : RGBA → HDiagram → HDiagram
fillColor c = hfillcolour (toHRGBA c)

lineColor : RGBA → HDiagram → HDiagram
lineColor c = hlinecolour (toHRGBA c)

compile : Segment → HSegment
compile (cub a b c) =
  hbezier3 (uncurry hv2 a) (uncurry hv2 b) (uncurry hv2 c)
compile (lin a) = hstraight (uncurry hv2 a)

compilesClosed : List Segment → HDiagram
compilesClosed = hstroke ∘ htoPathClosed ∘ flip hat (hpoint2 0.0 0.0) ∘ mapl compile

compiles : List Segment → HDiagram
compiles = hstroke ∘ htoPath ∘ flip hat (hpoint2 0.0 0.0) ∘ mapl compile

-- compile' : Diagram ⊤ → HDiagram
-- compile' (diagram xs) = hstroke (htoPath (hat (mapl {!   !} xs) (hpoint2 0.0 0.0)))
