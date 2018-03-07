open import Prelude
open import Generic.Multirec

module Multirec.Functor {n : ℕ}
           (Rec : Setⁿ n)
           (_≟Rec_ : ∀{ν}(x y : Rec ν) → Dec (x ≡ y))
       where
  -- open import Data.List using (monadPlus)

  open import Multirec.Internal.Functor Rec _≟Rec_

    public
  -- TODO enumerate patches
  {- open import Regular.Internal.ExtEnum.Functor Rec _≟Rec_ List Data.List.monadPlus
    public -}
  
  module FunctorApplication
         (PatchRec : Setⁿ n)
         (applyR   : {ν : Fin n} → PatchRec ν → Rec ν → Maybe (Rec ν))
      where

    ⟪_⟫A : {α : Atom n} → At PatchRec α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)
    ⟪ a ⟫A = applyAt applyR a

    ⟪_⟫P : {π₁ π₂ : Prod n} → Al (At PatchRec) π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)
    ⟪ as ⟫P = applyAl ⟪_⟫A as

    ⟪_⟫SP : {π : Prod n} → All (At PatchRec) π → ⟦ π ⟧P Rec → Maybe (⟦ π ⟧P Rec)
    ⟪ ats ⟫SP = applySP ⟪_⟫A ats

    ⟪_⟫S : {σ : Sum n} → Patch PatchRec σ → ⟦ σ ⟧S Rec → Maybe (⟦ σ ⟧S Rec)
    ⟪ p ⟫S = applyS ⟪_⟫A ⟪_⟫P p

