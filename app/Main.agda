module Main where

open import Agda.Builtin.IO using (IO)
open import Function using (_∘_)
open import Data.Unit using (⊤)
open import Carta.Prims
open import Carta.Main
open import Carta.Segment
open import Data.List using (List; applyUpTo; map; []; _∷_)
open import Data.Float renaming (Float to ℝ)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)


π 2π : ℝ
π = 3.14159
2π = 2.0 * π

diffs : List ℝ² → List ℝ²
diffs [] = []
diffs (x ∷ []) = []
diffs (x ∷ y ∷ xs) = mn y x ∷ diffs (y ∷ xs)
  where
    mn : (a b : ℝ²) → ℝ²
    mn (ax , ay) (bx , by) = ax - bx , ay - by

circle : ℕ → List ℝ²
circle n =
  let rn = fromℕ n
      dθ = 2π ÷ rn
      go i = let θ = fromℕ i * dθ in (cos θ , sin θ)
  in applyUpTo go (suc n)

segments : List ℝ² → List Segment
segments = map linear ∘ diffs

main : IO ⊤
main = mainWith (compiles (segments (circle 8)))
