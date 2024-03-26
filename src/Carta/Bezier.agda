
open import Algebra using (CommutativeRing)
open import Algebra.Module using (Module)

module Carta.Bezier
  {c ℓ} {CR : CommutativeRing c ℓ} {ℓ ℓm} (M : Module CR ℓ ℓm) where

  open CommutativeRing CR
  open Module M

  open import Data.Vec.Recursive using (_^_; cons; tail; [])
  open import Data.Nat using (zero; suc)
  open import Data.Product using (_,_)

  liat : ∀ {a} {A : Set a} m → A ^ suc m → A ^ m
  liat 0 x = []
  liat (suc m) (x , xs) = cons m x (liat m xs)

  -- a bezier curve of order m
  bez : ∀ m → Carrierᴹ ^ suc m → Carrier → Carrierᴹ
  bez zero points t = points
  bez (suc m) points t =
    let 1-t = 1# + (- t)
    in     t   *ₗ bez m (tail (suc m) points) t
        +ᴹ 1-t *ₗ bez m (liat (suc m) points) t
