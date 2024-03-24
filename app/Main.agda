module Main where

open import Agda.Builtin.IO using (IO)
open import Function using (_∘_)
open import Data.Unit using (⊤)
open import Carta.Prims
open import Carta.Main
open import Carta.Segment
open import Data.List using (List; applyUpTo; map)
open import Data.Float renaming (Float to ℝ)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)


{-# FOREIGN GHC import Diagrams.Prelude #-}

π : ℝ
π = 3.14159

xy : ℕ → List ℝ²
xy n =
  let rn = fromℕ n
      go i = let di = fromℕ i ÷ rn in (di , cos (di * π * 0.5))
  in applyUpTo go n

segments : ℕ → List Segment
segments = map linear ∘ xy

main : IO ⊤
main = mainWith (compiles (segments 1000))
