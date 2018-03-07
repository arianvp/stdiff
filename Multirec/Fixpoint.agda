open import Prelude
open import Generic.Multirec

module Multirec.Fixpoint {n : ℕ}(φ : Fam n) where
 
  open import Data.List using (monadPlus)

  open import Multirec.Internal.Fixpoint φ
    public
  {-open import Regular.Internal.ExtEnum.Fixpoint σμ List Data.List.monadPlus
    public-}
    

-- TODO create patches
{-
  diffFix : Fix σμ → Fix σμ → Alμ
  diffFix x y with diff x y
  ...| [] = magic
    where postulate magic : Alμ
  ...| (p ∷ ps) = aux p ps
    where
      aux : Alμ → List Alμ → Alμ
      aux a [] = a
      aux a (b ∷ bs) with costAlμ a ≤? costAlμ b
      ...| yes _ = aux a bs
      ...| no  _ = aux b bs
   -}

  module FixpointApplication where

    ⟪_⟫μ : {ν : Fin n} → Alμ ν → Fix φ ν → Maybe (Fix φ ν)
    ⟪ alμ ⟫μ = applyAlμ alμ 

    open import Multirec.Functor (Fix φ) _≟Fix_ as RF
    open RF.FunctorApplication Alμ ⟪_⟫μ public
