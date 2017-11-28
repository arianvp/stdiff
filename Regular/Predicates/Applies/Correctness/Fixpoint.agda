open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Correctness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Applies.Fixpoint μσ

  open FixpointApplication

  AppAlμ-correct : ∀{x y p}
                 → AppAlμ x y p
                 → ⟪ p ⟫μ x ≡ just y


  AppCtxIns-correct : ∀{π x}{pys : ⟦ π ⟧P (Fix μσ)}{δ : Ctx π}
                    → AppCtxIns x pys δ
                    → inCtx δ x ≡ just pys
  AppCtxIns-correct hip = {!!}


  AppCtxDel-correct : ∀{π}{pxs : ⟦ π ⟧P (Fix μσ)}{y : Fix μσ}
                    → {δ : Ctx π}
                    → AppCtxDel pxs y δ
                    → matchCtx δ pxs ≡ just y
  AppCtxDel-correct hip = {!!}

  AppAlμ-correct (AppSpn x y s hip) 
    = {!!}
  AppAlμ-correct (AppIns x C Pys δ hip) 
    rewrite AppCtxIns-correct hip = refl
  AppAlμ-correct (AppDel C Pxs y δ hip) 
    = {!!}
