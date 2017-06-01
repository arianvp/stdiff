open import Prelude
open import Generic.Regular

module Regular.Predicates.Disjoint.Merge.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Identity.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Merge.Functor (Fix μσ) _≟Fix_ Alμ identityAlμ

  {-# TERMINATING #-}
  mergeAlμ : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂) → Alμ
  mergeCtx : ∀{π}(ctx₁ ctx₂ : Ctx π)(hip : disjCtx ctx₁ ctx₂) → Ctx π

  mergeAtCtx : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)(hip : disjAtCtx atμs ctx) → Ctx π

  mergeInCtx : ∀{π}(alμ : Alμ)(ctx : Ctx π)(hip : disjAlμ alμ (getCtx ctx))
             → Ctx π
  mergeInCtx alμ ctx hip = {!!}

  -- * Insertions are trivially mergeoint from anything.
  mergeAlμ (ins C₁ s₁) s₂          hip = ins C₁ (mergeInCtx s₂ s₁ hip)
  mergeAlμ s₁ (ins C₂ s₂)          hip = ins C₂ (mergeInCtx s₁ s₂ {!hip!})

  -- * Two spines might be mergeoint,
  mergeAlμ (spn s₁) (spn s₂)       hip = {!!}

  -- * A deletion is mergeoint from a copy
  mergeAlμ (spn Scp) (del C₂ s₂)   hip = {!!}

  -- * If the spine is a Scns and its recursive changes
  --   does NOT change the deleted context, they are still mergeoint
  mergeAlμ (spn (Scns C₁ at₁))  (del C₂ s₂)   
    hip = {!!}

  -- * A Schg is never mergeoint from a deletion.
  mergeAlμ (spn _)              (del C₂ s₂)   
    hip = {!!}

  -- * Since mergeointness is symmetric, here we just repeat the cases above.
  mergeAlμ (del C₁ s₁) (spn Scp)   hip = {!!}
  mergeAlμ (del C₁ s₁) (spn (Scns C₂ at₂))   
    hip = {!!}
  mergeAlμ (del C₁ s₁) (spn _) 
    hip = {!!}

  -- * Two deletions are never mergeoint,
  --   since a patch is never mergeoitn from itself.
  mergeAlμ (del C₁ s₁) (del C₂ s₂) 
    hip = {!!}
  

  -- * mergeCtx makes sure that the contexts are aligned and the patches
  --   within them are mergeoint.
  mergeCtx (here alμ₁ rest₁) (here alμ₂ rest₂) hip = {!!}
  mergeCtx (there a₁ ctx₁)   (there a₂ ctx₂)   hip = {!!}
  mergeCtx _                 _                 hip = {!!}

  -- * mergeAtCtx makes sure that the All At part of the Scns spine
  --   is all identities on the deleted part of the context and is
  --   mergeoint in the field selected by the context.
  mergeAtCtx [] ()
  mergeAtCtx (fix a ∷ as) (here alμ rest) hip = {!!}
  mergeAtCtx (a ∷ as)     (there a' ctx)  hip = {!!}

