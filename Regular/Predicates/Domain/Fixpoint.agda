open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Fixpoint (σμ : Sum) where

  open import Regular.Internal.Fixpoint σμ
  open import Regular.Internal.Functor (Fix σμ) _≟Fix_
  open import Regular.Predicates.Domain.Functor (Fix σμ) _≟Fix_ Alμ applyAlμ
    public

  {-# TERMINATING #-}
  _∈domAlμ_ : Fix σμ → Alμ → Set
  ⟨ x ⟩ ∈domAlμ spn sp    = _∈domS_ _∈domAlμ_ x sp
  ⟨ x ⟩ ∈domAlμ ins C spμ = ⟨ x ⟩ ∈domAlμ (getCtx spμ)
  ⟨ x ⟩ ∈domAlμ del C spμ with match C x
  ...| nothing = ⊥
  ...| just p  = selectP p spμ ∈domAlμ getCtx spμ


