{-# OPTIONS --guardedness #-}

module Main where

{-# FOREIGN GHC import Diagrams.Prelude #-}
{-# FOREIGN GHC import Diagrams.Backend.SVG.CmdLine #-}

open import Function using (_$_)
open import Agda.Builtin.IO using (IO)
open import Data.Float using () renaming (Float to ℝ)
open import Level using (0ℓ)
open import Data.Unit using (⊤)

postulate
  Diagram : Set → Set
  SVG : Set
  circle : ℝ → Diagram SVG
  mainWith : Diagram SVG → IO ⊤

{-# COMPILE GHC Diagram = type Diagram #-}
{-# COMPILE GHC SVG = type SVG #-}
{-# COMPILE GHC circle = circle #-}
{-# COMPILE GHC mainWith = mainWith #-}

main : IO ⊤
main = mainWith (circle 1.0)
