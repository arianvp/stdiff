open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Predicates.Identity.Functor (Fix μσ) _≟Fix_ Alμ
    public
  
  {-# TERMINATING #-}
  identityAlμ : Alμ → Set
  identityAlμ (spn sp) = identityS identityAlμ sp
  identityAlμ _        = ⊥

  identityAtμ : ∀{α} → Atμ α → Set
  identityAtμ = identityAt identityAlμ
