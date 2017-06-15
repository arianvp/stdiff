open import Prelude
open import Generic.Regular

module Regular.Fixpoint (σμ : Sum) where
 
  open import Data.List using (monadPlus)

  open import Regular.Internal.Fixpoint σμ
    public
  open import Regular.Internal.EnumFix σμ List Data.List.monadPlus
    public
    
  
  postulate
    magic : Alμ

  diffFix : Fix σμ → Fix σμ → Alμ
  diffFix x y with diff x y
  ...| [] = magic
  ...| (p ∷ ps) = aux p ps
    where
      aux : Alμ → List Alμ → Alμ
      aux a [] = a
      aux a (b ∷ bs) with costAlμ a ≤? costAlμ b
      ...| yes _ = aux a bs
      ...| no  _ = aux b bs

  module FixpointApplication where

    ⟪_⟫μ : Alμ → Fix σμ → Maybe (Fix σμ)
    ⟪ alμ ⟫μ = applyAlμ alμ 

    open import Regular.Functor (Fix σμ) _≟Fix_ as RF
    open RF.FunctorApplication Alμ ⟪_⟫μ public
