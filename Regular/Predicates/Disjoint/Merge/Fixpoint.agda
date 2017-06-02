open import Prelude
open import Generic.Regular

module Regular.Predicates.Disjoint.Merge.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Identity.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Merge.Functor (Fix μσ) _≟Fix_ Alμ identityAlμ disjAlμ
    public

  {-# TERMINATING #-}
  mergeAlμ : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂) → Alμ

  mergeAtCtx : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)(hip : disjAtCtx atμs ctx) → Ctx π

  mergeInCtx : ∀{π}(alμ : Alμ)(ctx : Ctx π)(hip : disjAlμ alμ (getCtx ctx)) → Ctx π
  mergeInCtx alμ (here alμ' rest) hip = here (mergeAlμ alμ alμ' hip) rest
  mergeInCtx alμ (there a   ctx)  hip = there a (mergeInCtx alμ ctx hip)

  mergeAlμ (ins C₁ s₁) s₂         hip = ins C₁ (mergeInCtx s₂ s₁ hip)
  mergeAlμ (spn s₁)   (ins C₂ s₂) hip = ins C₂ (mergeInCtx (spn s₁) s₂ hip)
  mergeAlμ (del C s₁) (ins C₂ s₂) hip = ins C₂ (mergeInCtx (del C s₁) s₂ hip)

  mergeAlμ (spn s₁) (spn s₂)       hip = spn (mergeS mergeAlμ s₁ s₂ hip)

  mergeAlμ (spn Scp) (del C₂ s₂)   hip = del C₂ s₂

  mergeAlμ (spn (Scns C₁ at₁))  (del C₂ s₂) (refl , hip) 
    = del C₁ (mergeAtCtx at₁ s₂ hip)

  mergeAlμ (spn (Schg _ _ _)) (del C₂ s₂) ()

  mergeAlμ (del C₁ s₁) (spn Scp)   hip 
    = del C₁ s₁
  mergeAlμ (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , hip)
    = del C₁ (mergeAtCtx at₂ s₁ hip)
  mergeAlμ (del C₁ s₁) (spn (Schg _ _ _)) ()

  mergeAlμ (del C₁ s₁) (del C₂ s₂) ()

  mergeAtCtx [] ()
  mergeAtCtx (fix a ∷ as) (here alμ rest) (ha , hip) 
    = here (mergeAlμ a alμ ha) rest
  mergeAtCtx {p ∷ ps} (fix a ∷ as) (there a' ctx) hip
    = there a' (mergeAtCtx as ctx (proj₂ hip))
  mergeAtCtx {p ∷ ps} (set a ∷ as) (there a' ctx) hip
    = there a' (mergeAtCtx as ctx (proj₂ hip))
