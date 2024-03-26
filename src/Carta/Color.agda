module Carta.Color where

open import Data.Fin using (Fin; zero; suc; toℕ; #_; opposite; fromℕ)
import Data.Nat as ℕ
open import Data.Nat using (ℕ)
open import Relation.Nullary
open import Data.Product using (_,_)
open import Data.Vec.Recursive

plus minus : ∀ {n m} (a : Fin n) (b : Fin m) → Fin n
minus a b = plus (opposite a) (opposite b)
plus {1} {m} a b = a
plus {ℕ.suc n} {m} zero zero = zero
plus {ℕ.suc n} {m} (suc a) b = suc (plus a b)
plus {ℕ.suc (ℕ.suc n)} {m} zero (suc b) =
  suc (plus {ℕ.suc n} zero b)

RGBA : Set
RGBA = Fin 256 ^ 4

RGB : Set
RGB = Fin 256 ^ 3

_+_ _-_ : ∀ {n m} (a b : Fin n ^ m) → Fin n ^ m
_+_ {m = m} = zipWith plus m
_-_ {m = m} = zipWith minus m

#255 : Fin 256
#255 = # 255

opaque' : RGB → RGBA
opaque' x = append 3 1 x #255

red blue green black white : RGB
red = #255 , zero , zero
green = zero , #255 , zero
blue = zero , zero , #255
black = zero , zero , zero
white = #255 , #255 , #255

module _ where
  open import Relation.Binary.PropositionalEquality
  open import Data.Product.Nary.NonDependent as N
  open import Function using (_$′_)

  saturates : ∀ n {m} (x : Fin m) → plus (fromℕ n) x ≡ fromℕ n
  saturates ℕ.zero x = refl
  saturates (ℕ.suc n) x = cong suc (saturates n x)

  trunc : ∀ n {m} (x : Fin m) → Fin (ℕ.suc n)
  trunc ℕ.zero x = zero
  trunc (ℕ.suc n) zero = zero
  trunc (ℕ.suc n) (suc x) = suc (trunc n x)

  zero-plus-unit : ∀ n {m} (x : Fin m) → plus zero x ≡ trunc (ℕ.suc n) x
  zero-plus-unit ℕ.zero zero = refl
  zero-plus-unit ℕ.zero (suc x) = refl
  zero-plus-unit (ℕ.suc n) zero = refl
  zero-plus-unit (ℕ.suc n) (suc x) = cong suc (zero-plus-unit n x)

  testwhite : ∀ x → white + x ≡ white
  testwhite x = fromEqualₙ 3 $′ map (saturates 255) 3 x

  -- BBBBBBBBBLLLLLLLLLAAAAAAAAAAAAHHHHHHHH
  -- testblack : ∀ (x : RGB) → black + x ≡ x
  -- testblack x =
  --   let z = map {! λ y → unit 255 {256} y !} 3 x -- map (λ y → unit 255 {256} y)  3 x
  --   in {!   !}
