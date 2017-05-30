open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Correctness.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Domain.Fixpoint μσ
  open import Regular.Predicates.Domain.Correctness.Functor 
    (Fix μσ) _≟Fix_ Alμ applyAlμ _∈domAlμ_

  {-# TERMINATING #-}
  domAlμ-ok : (x : Fix μσ)(alμ : Alμ)(hip : x ∈domAlμ alμ)
            → IsJust (applyAlμ alμ x)

  domInCtx-ok : ∀{π}(x : Fix μσ)(ctx : Ctx π)(hip : x ∈domAlμ (getCtx ctx))
              → IsJust (inCtx ctx x)
  domInCtx-ok x (here spμ rest) hip = IsJust-map (domAlμ-ok x spμ hip)
  domInCtx-ok x (there _ ctx)   hip = IsJust-map (domInCtx-ok x ctx hip)

  domMatchCtx-ok : ∀{π}(x : ⟦ π ⟧P (Fix μσ))(ctx : Ctx π)
                   (hip : (selectP x ctx ∈domAlμ (getCtx ctx))) 
                 → IsJust (matchCtx ctx x)
  domMatchCtx-ok (x ∷ _)  (here spμ _)  hip = domAlμ-ok x spμ hip
  domMatchCtx-ok (_ ∷ xs) (there _ ctx) hip = domMatchCtx-ok xs ctx hip

  domAlμ-ok ⟨ x ⟩ (spn sp) hip    
    = IsJust-map (domS-ok domAlμ-ok x sp hip)
  domAlμ-ok ⟨ x ⟩ (ins C ctx) hip 
    = IsJust-map (domInCtx-ok ⟨ x ⟩ ctx hip)
  domAlμ-ok ⟨ x ⟩ (del C ctx) hip 
    with sop x
  ...| tag Cx Px with C ≟F Cx
  ...| no _     = ⊥-elim hip
  ...| yes refl = domMatchCtx-ok Px ctx hip
