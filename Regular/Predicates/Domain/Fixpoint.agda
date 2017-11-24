open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Domain.Functor (Fix μσ) _≟Fix_ Alμ applyAlμ

  {-# TERMINATING #-}
  _∈domAlμ_ : Fix μσ → Alμ → Set

  _∈domCtx_ : ∀{π} → ⟦ π ⟧P (Fix μσ) → Ctx π → Set
  (x ∷ xs) ∈domCtx (here alμ rest) = x ∈domAlμ alμ × xs ≡ rest
  (x ∷ xs) ∈domCtx (there at ctx)  = x ≡ at × xs ∈domCtx ctx

  ⟨ x ⟩ ∈domAlμ spn sp    = _∈domS_ _∈domAlμ_ x sp
  ⟨ x ⟩ ∈domAlμ ins C ctx = ⟨ x ⟩ ∈domAlμ (getCtx ctx)
  ⟨ x ⟩ ∈domAlμ del C ctx with match C x
  ...| nothing = ⊥
  ...| just p  = p ∈domCtx ctx


