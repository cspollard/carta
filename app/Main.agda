{-# OPTIONS --guardedness #-}

module Main where

open import Agda.Builtin.IO using (IO)
open import Data.Unit using (⊤)
open import Carta.Prims

main : IO ⊤
main = mainWith (circle 1.0)
