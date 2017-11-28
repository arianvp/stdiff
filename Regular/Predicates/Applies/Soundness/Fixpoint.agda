open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Soundness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Applies.Fixpoint μσ

  open FixpointApplication

  AppAlμ-sound : ∀{x y p}
                 → ⟪ p ⟫μ x ≡ just y
                 → AppAlμ x y p


  AppCtxIns-sound : ∀{π x}{pys : ⟦ π ⟧P (Fix μσ)}{δ : Ctx π}
                    → inCtx δ x ≡ just pys
                    → AppCtxIns x pys δ
  AppCtxIns-sound hip = {!!}


  AppCtxDel-sound : ∀{π}{pxs : ⟦ π ⟧P (Fix μσ)}{y : Fix μσ}
                    → {δ : Ctx π}
                    → matchCtx δ pxs ≡ just y
                    → AppCtxDel pxs y δ
  AppCtxDel-sound hip = {!!}

  AppAlμ-sound hip = ?
