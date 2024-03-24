module Main where

open import Agda.Builtin.IO using (IO)
open import Data.Unit using (⊤)
open import Carta.Prims
open import Carta.Main
open import Carta.Segment
open import Data.List using (List; []; _∷_)
open import Data.Float renaming (Float to ℝ)


{-# FOREIGN GHC import Diagrams.Prelude #-}

main : IO ⊤
main = mainWith (compiles (linear (r2 1.0 1.0) ∷ []))
