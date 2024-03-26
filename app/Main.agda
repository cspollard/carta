module Main where

open import Agda.Builtin.IO using (IO)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤)
open import Carta.Prims
open import Carta.Main
open import Carta.Color using (opaque'; red)
open import Data.List using (List; applyUpTo; map; []; _∷_)
open import Data.Float renaming (Float to ℝ)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)

open import Algebra.Module using (Module)
open Module ℝ²-module

_-ᴹ_ : (a b : ℝ²) → ℝ²
a -ᴹ b = a +ᴹ (-ᴹ b)


π 2π : ℝ
π = 3.14159
2π = 2.0 * π

diffs : List ℝ² → List ℝ²
diffs [] = []
diffs (x ∷ []) = []
diffs (x ∷ y ∷ xs) = (y -ᴹ x) ∷ diffs (y ∷ xs)

circle : ℕ → List ℝ²
circle n =
  let rn = fromℕ n
      dθ = 2π ÷ rn
      go i = let θ = fromℕ i * dθ in (cos θ , sin θ)
  in applyUpTo go (suc n)

segments : List ℝ² → List Segment
segments = map lin ∘ diffs

main : IO ⊤
main =
  mainWith (fillColor (opaque' red) $ compilesClosed (segments (circle 8)))
