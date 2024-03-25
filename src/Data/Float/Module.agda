module Data.Float.Module where

open import Level using (0ℓ)
open import Algebra using (IsCommutativeRing; CommutativeRing)
open import Algebra.Module using (IsModule; Module)
import Algebra.Module.Construct.TensorUnit as TensorUnit
import Algebra.Module.Construct.Zero as Zero
import Algebra.Module.Construct.DirectProduct as DirectProduct
open import Data.Float using (_≈_; _+_; -_; _*_) renaming (Float to ℝ)
open import Data.Nat using (ℕ)


private
  postulate
    assume : ∀ {a} {A : Set a} → A

ℝ-isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0.0 1.0
ℝ-isCommutativeRing = assume

ℝ-commutativeRing : CommutativeRing 0ℓ 0ℓ 
ℝ-commutativeRing = record { isCommutativeRing = ℝ-isCommutativeRing }


ℝ-module : Module ℝ-commutativeRing 0ℓ 0ℓ
ℝ-module = TensorUnit.⟨module⟩

ℝⁿ-module : ℕ → Module ℝ-commutativeRing 0ℓ 0ℓ
ℝⁿ-module ℕ.zero = Zero.⟨module⟩
ℝⁿ-module (ℕ.suc ℕ.zero)  = ℝ-module
ℝⁿ-module (ℕ.suc n) = DirectProduct.⟨module⟩ ℝ-module (ℝⁿ-module n) 


-- Can I prove that any isomorphism f : A → B, with B the carrier of some
-- algebraic structure, defines a new algebraic structure with carrier A?


module _ where
  open Module
  open import Data.Product
  open import Data.Unit.Polymorphic

  _ : Carrierᴹ (ℝⁿ-module 2)
  _ = 1.0 , 2.0
