module Carta.Prims where

{-# FOREIGN GHC import Diagrams.Prelude #-}

open import Function using (_$_)
open import Data.Float using () renaming (Float to ℝ)
open import Level using (0ℓ)

postulate
  Diagram : Set → Set

{-# COMPILE GHC Diagram = type Diagram #-}
