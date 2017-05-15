open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Fixpoint (σμ : Sum) where

  open import Regular.Internal.Fixpoint σμ
  open import Regular.Internal.Functor (Fix σμ) _≟Fix_
  open import Regular.Predicates.Domain.Functor (Fix σμ) _≟Fix_ Alμ applyAlμ
    public

  _∈domAlμ_ : Fix σμ → Alμ → Set
  x ∈domAlμ alμ = IsJust (applyAlμ alμ x)
