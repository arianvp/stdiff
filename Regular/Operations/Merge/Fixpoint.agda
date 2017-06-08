open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Identity.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Fixpoint μσ
  open import Regular.Operations.Merge.Functor (Fix μσ) _≟Fix_ Alμ identityAlμ disjAlμ
    renaming (module MergeSymmetry to MergeSymmetryF)
    public

  open DisjSymmetry

  {-# TERMINATING #-}
  mergeAlμ : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂) → Alμ

  mergeAtCtx : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)(hip : disjAtCtx atμs ctx) → Ctx π

  mergeInCtx : ∀{π}(alμ : Alμ)(ctx : Ctx π)(hip : disjAlμ alμ (getCtx ctx)) → Ctx π
  mergeInCtx alμ (here alμ' rest) hip = here (mergeAlμ alμ alμ' hip) rest
  mergeInCtx alμ (there a   ctx)  hip = there a (mergeInCtx alμ ctx hip)

  mergeAlμ (ins C₁ s₁) (ins C₂ s₂) ()
  mergeAlμ (ins C₁ s₁) (spn s₂)    hip 
    = ins C₁ (mergeInCtx (spn s₂) s₁ (disjAlμ-sym (getCtx s₁) (spn s₂) hip))
  mergeAlμ (ins C₁ s₁) (del C₂ s₂) hip 
    = ins C₁ (mergeInCtx (del C₂ s₂) s₁ (disjAlμ-sym (getCtx s₁) (del C₂ s₂) hip))
  mergeAlμ (spn s₁)   (ins C₂ s₂)  hip = ins C₂ (mergeInCtx (spn s₁) s₂ hip)
  mergeAlμ (del C s₁) (ins C₂ s₂)  hip = ins C₂ (mergeInCtx (del C s₁) s₂ hip)

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

  module MergeSymmetry where

   
    mergeAlμ-sym : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂)
                 → mergeAlμ alμ₁ alμ₂ hip ≡ mergeAlμ alμ₂ alμ₁ (disjAlμ-sym alμ₁ alμ₂ hip)

    mergeAtCtx-sym : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)(hip : disjAtCtx atμs ctx) → {!!}

    mergeInCtx-sym : ∀{π}(alμ : Alμ)(ctx : Ctx π)(hip : disjAlμ alμ (getCtx ctx)) → {!!}
    mergeInCtx-sym alμ (here alμ' rest) hip = {!!}
    mergeInCtx-sym alμ (there a   ctx)  hip = {!!}

    mergeAlμ-sym (ins C₁ s₁) (ins C₂ s₂) ()
    mergeAlμ-sym (ins C₁ s₁) (spn s₂)    hip = refl
    mergeAlμ-sym (ins C₁ s₁) (del C₂ s₂) hip = refl
    mergeAlμ-sym (spn s₁)   (ins C₂ s₂)  hip = cong (ins C₂) {!!}
    mergeAlμ-sym (del C s₁) (ins C₂ s₂)  hip = {!!}

    mergeAlμ-sym (spn s₁) (spn s₂)       hip = {!!}

    mergeAlμ-sym (spn Scp) (del C₂ s₂)   hip = {!!}

    mergeAlμ-sym (spn (Scns C₁ at₁))  (del C₂ s₂) (refl , hip) 
      = {!!}

    mergeAlμ-sym (spn (Schg _ _ _)) (del C₂ s₂) ()

    mergeAlμ-sym (del C₁ s₁) (spn Scp)   hip 
      = {!!}
    mergeAlμ-sym (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , hip)
      = {!!}
    mergeAlμ-sym (del C₁ s₁) (spn (Schg _ _ _)) ()

    mergeAlμ-sym (del C₁ s₁) (del C₂ s₂) ()

    mergeAtCtx-sym [] ()
    mergeAtCtx-sym (fix a ∷ as) (here alμ rest) (ha , hip) 
      = {!!}
    mergeAtCtx-sym {p ∷ ps} (fix a ∷ as) (there a' ctx) hip
      = {!!}
    mergeAtCtx-sym {p ∷ ps} (set a ∷ as) (there a' ctx) hip
      = {!!}
