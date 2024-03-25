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


ℝ-isModule : Module ℝ-commutativeRing 0ℓ 0ℓ
ℝ-isModule = TensorUnit.⟨module⟩

ℝⁿ-isModule : ℕ → Module ℝ-commutativeRing 0ℓ 0ℓ
ℝⁿ-isModule ℕ.zero = Zero.⟨module⟩
ℝⁿ-isModule (ℕ.suc ℕ.zero)  = ℝ-isModule
ℝⁿ-isModule (ℕ.suc n) = DirectProduct.⟨module⟩ ℝ-isModule (ℝⁿ-isModule n) 

open Module

module _ where
  open import Data.Product
  open import Data.Unit.Polymorphic

  _ : Carrierᴹ (ℝⁿ-isModule 2)
  _ = 1.0 , 2.0
