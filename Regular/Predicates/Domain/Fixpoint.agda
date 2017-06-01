open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Domain.Functor (Fix μσ) _≟Fix_ Alμ applyAlμ

  {-# TERMINATING #-}
  _∈domAlμ_ : Fix μσ → Alμ → Set
  ⟨ x ⟩ ∈domAlμ spn sp    = _∈domS_ _∈domAlμ_ x sp
  ⟨ x ⟩ ∈domAlμ ins C ctx = ⟨ x ⟩ ∈domAlμ (getCtx ctx)
  ⟨ x ⟩ ∈domAlμ del C ctx with match C x
  ...| nothing = ⊥
  ...| just p  = selectP p ctx ∈domAlμ getCtx ctx


