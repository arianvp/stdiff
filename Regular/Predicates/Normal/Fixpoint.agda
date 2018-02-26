open import Prelude
open import Generic.Regular

module Regular.Predicates.Normal.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor 
    (Fix μσ) _≟Fix_ 

  {-# TERMINATING #-}
  normAlμ-D : Alμ → Set

  normAlμ normAlμ-I normAlμ-M : Alμ → Set

  open import Regular.Predicates.Normal.Functor 
    (Fix μσ) _≟Fix_ Alμ normAlμ
    public

  normAlμ = normAlμ-D

  normAlμ-D (del C₁ δ) = normAlμ-D (getCtx δ)
  normAlμ-D (ins C₁ δ) = normAlμ-I (ins C₁ δ)
  normAlμ-D (spn s)    = ⊥

  normAlμ-I (ins C₁ δ) = normAlμ-I (getCtx δ)
  normAlμ-I (spn s)    = normAlμ-M (spn s)
  normAlμ-I (del C₁ δ) = ⊥

  normAlμ-M (spn s)    = normS s
  normAlμ-M (ins C₁ δ) = ⊥
  normAlμ-M (del C₁ δ) = ⊥
  

