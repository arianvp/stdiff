open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Correctness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Applies.Fixpoint μσ

  open FixpointApplication

  {-# TERMINATING #-}
  AppAlμ-correct : ∀{x y p}
                 → AppAlμ x y p
                 → ⟪ p ⟫μ x ≡ just y

  open import Regular.Predicates.Applies.Correctness.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ ⟪_⟫μ AppAlμ-correct

  AppCtxIns-correct : ∀{π x}{pys : ⟦ π ⟧P (Fix μσ)}{δ : Ctx π}
                    → AppCtxIns x pys δ
                    → inCtx δ x ≡ just pys
  AppCtxIns-correct (AppInsHere x y spμ pys hip) 
    rewrite AppAlμ-correct hip = refl
  AppCtxIns-correct (AppInsThere x y pys δ hip) 
    rewrite AppCtxIns-correct hip = refl

  AppCtxDel-correct : ∀{π}{pxs : ⟦ π ⟧P (Fix μσ)}{y : Fix μσ}
                    → {δ : Ctx π}
                    → AppCtxDel pxs y δ
                    → matchCtx δ pxs ≡ just y
  AppCtxDel-correct (AppDelHere x y spμ pxs pxs' hip) 
    rewrite AppAlμ-correct hip = refl
  AppCtxDel-correct (AppDelThere x x' y pxs δ hip)
    rewrite AppCtxDel-correct hip = refl

  AppAlμ-correct (AppSpn x y s hip) 
    = Maybe-map-def (⟪ s ⟫S x) (AppS-correct hip)
  AppAlμ-correct (AppIns x C Pys δ hip) 
    rewrite AppCtxIns-correct hip = refl
  AppAlμ-correct (AppDel C Pxs y δ hip) 
    rewrite sop-inj-lemma {μσ} C Pxs
          | dec-refl _≟F_ C
          | AppCtxDel-correct hip
          = refl
