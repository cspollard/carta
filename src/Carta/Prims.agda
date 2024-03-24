module Carta.Prims where

open import Function using (_$_)
open import Data.Float using () renaming (Float to ℝ)
open import Level using (0ℓ)
open import Carta.Trail

-- explicitly SVG
{-# FOREIGN GHC import Diagrams.Backend.SVG #-}
{-# FOREIGN GHC import Diagrams.Prelude #-}

postulate
  SVG : Set
  Segment : Set
  HPath : Set
  HTrail : Set
  HTrail' : Set
  HDiagram : Set → Set
  stroke : Path → ∀ {b} → HDiagram b

{-# COMPILE GHC SVG = type SVG #-}
{-# COMPILE GHC Segment = type Segment V2  #-}
{-# COMPILE GHC HPath = data Path #-}
{-# COMPILE GHC HTrail = data Trail #-}
{-# COMPILE GHC HTrail' = data Trail' #-}
{-# COMPILE GHC HDiagram = type Diagram #-}
{-# COMPILE GHC stroke = stroke #-}

toTrail' : Trail → HTrail'
toTrail' = {!   !}

toTrail : Trail → HTrail
toTrail = {!   !}

toDiagram : Path → ∀ {b} → HDiagram b
toDiagram t = {!   !}
