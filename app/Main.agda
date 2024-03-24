module Main where

open import Agda.Builtin.IO using (IO)
open import Data.Unit using (⊤)
open import Carta.Prims
open import Carta.Main
open import Data.Float renaming (Float to ℝ)

postulate
  circle : ℝ → Diagram SVG

{-# FOREIGN GHC import Diagrams.Prelude #-}
{-# COMPILE GHC circle = circle #-}

main : IO ⊤
main = mainWith (circle 1.0)
