open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Soundness.Fixpoint (μσ : Sum) where

  open import Regular.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Applies.Fixpoint μσ

  open FixpointApplication

  {-# TERMINATING #-}
  AppAlμ-sound : (x y : Fix μσ)(p : Alμ)
                 → ⟪ p ⟫μ x ≡ just y
                 → AppAlμ x y p

  open import Regular.Predicates.Applies.Soundness.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ ⟪_⟫μ AppAlμ-sound
    public

  AppCtxIns-sound : ∀{π}(x : Fix μσ)(pys : ⟦ π ⟧P (Fix μσ))(δ : Ctx π)
                    → inCtx δ x ≡ just pys
                    → AppCtxIns x pys δ
  AppCtxIns-sound x (py ∷ pys) (here alμ rest) hip 
    with ⟪ alμ ⟫μ x | inspect ⟪ alμ ⟫μ x
  ...| nothing | _ = Maybe-⊥-elim hip
  ...| just x' | [ X ] 
    rewrite proj₁ (All-∷-inj (just-inj hip)) 
          | proj₂ (All-∷-inj (just-inj hip)) 
          = AppInsHere x py alμ pys (AppAlμ-sound x py alμ X)
  AppCtxIns-sound x (py ∷ pys) (there at δ) hip 
    with inCtx δ x | inspect (inCtx δ) x
  ...| nothing | _ = Maybe-⊥-elim hip
  ...| just x' | [ X ] 
    rewrite proj₁ (All-∷-inj (just-inj hip)) 
          | proj₂ (All-∷-inj (just-inj hip)) 
          = AppInsThere x py pys δ (AppCtxIns-sound x pys δ X)


  AppCtxDel-sound : ∀{π}(pxs : ⟦ π ⟧P (Fix μσ))(y : Fix μσ)
                    → (δ : Ctx π)
                    → matchCtx δ pxs ≡ just y
                    → AppCtxDel pxs y δ
  AppCtxDel-sound (px ∷ pxs) y (here alμ rest) hip 
    = AppDelHere px y alμ pxs rest (AppAlμ-sound px y alμ hip)
  AppCtxDel-sound (px ∷ pxs) y (there at δ) hip 
    = AppDelThere px at y pxs δ (AppCtxDel-sound pxs y δ hip)

  AppAlμ-sound ⟨ x ⟩ ⟨ y ⟩ (spn s) hip 
    = AppSpn x y s (AppS-sound x y s 
        (Maybe-unmap-def {f = ⟨_⟩} ⟨⟩-inj (⟪ s ⟫S x) hip))
  AppAlμ-sound ⟨ x ⟩ ⟨ y ⟩ (ins C δ) hip 
    with sop y
  ...| tag Cy Py 
    with inCtx δ ⟨ x ⟩ | inspect (inCtx δ) ⟨ x ⟩ 
  ...| nothing | _     = Maybe-⊥-elim hip
  ...| just x' | [ X ] 
    with inj-inj (⟨⟩-inj (just-inj hip))
  ...| refl , refl 
     = AppIns ⟨ x ⟩ C x' δ 
          (AppCtxIns-sound ⟨ x ⟩ x' δ X)
  AppAlμ-sound ⟨ x ⟩ ⟨ y ⟩ (del C δ) hip 
    with sop x
  ...| tag Cx Px 
    with C ≟F Cx
  ...| no _ = Maybe-⊥-elim hip
  ...| yes refl = AppDel Cx Px ⟨ y ⟩ δ 
                    (AppCtxDel-sound Px ⟨ y ⟩ δ hip)
