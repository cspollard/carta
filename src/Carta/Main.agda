module Carta.Main where


open import Data.Unit using (⊤)
open import Agda.Builtin.IO using (IO)

open import Carta.Prims

{-# FOREIGN GHC import Diagrams.Backend.SVG.CmdLine #-}

postulate
  mainWith : Diagram SVG → IO ⊤

{-# COMPILE GHC mainWith = mainWith #-}
