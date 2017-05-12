open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Fixpoint (σμ : Sum) where

  open import Regular.Internal.Fixpoint σμ
  open import Regular.Internal.Functor (Fix σμ) _≟Fix_
  open import Regular.Predicates.Identity.Functor (Fix σμ) _≟Fix_ Alμ
    public

  {-# TERMINATING #-}
  identityAlμ : Alμ → Set
  identityAlμ (spn s) = identityS identityAlμ {σμ} s
  identityAlμ _       = ⊥
