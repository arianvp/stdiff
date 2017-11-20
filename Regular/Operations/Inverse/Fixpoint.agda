open import Prelude
open import Generic.Regular

module Regular.Operations.Inverse.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_

  {-# TERMINATING #-}
  invAlμ : Alμ → Alμ

  invCtx : ∀{π} → Ctx π → Ctx π
  invCtx (here  alμ rest) = here (invAlμ alμ) rest
  invCtx (there at  δ)    = there at (invCtx δ)

  open import Regular.Operations.Inverse.Functor (Fix μσ) _≟Fix_ Alμ invAlμ
  
  invAlμ (spn s)   = spn (invS s)
  invAlμ (ins C δ) = del C (invCtx δ)
  invAlμ (del C δ) = ins C (invCtx δ)
