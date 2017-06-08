open import Prelude
open import Generic.Regular

module Regular.Predicates.Disjoint.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Predicates.Identity.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Functor (Fix μσ) _≟Fix_ Alμ identityAlμ
    renaming (module DisjSymmetry to DisjSymmetryF)
    public

  {-# TERMINATING #-}
  disjAlμ : Alμ → Alμ → Set
  disjCtx : ∀{π} → Ctx π → Ctx π → Set

  disjAtCtx : ∀{π} → All Atμ π → Ctx π → Set

  -- * Insertions are trivially disjoint from anything.
  disjAlμ (ins C₁ s₁) (ins C₂ s₂) = ⊥
  disjAlμ (ins C₁ s₁) s₂          = disjAlμ (getCtx s₁) s₂  
  disjAlμ s₁ (ins C₂ s₂)          = disjAlμ s₁ (getCtx s₂)

  -- * Two spines might be disjoint,
  disjAlμ (spn s₁) (spn s₂)       = disjS disjAlμ s₁ s₂

  -- * A deletion is disjoint from a copy
  disjAlμ (spn Scp) (del C₂ s₂)   = Unit

  -- * If the spine is a Scns and its recursive changes
  --   does NOT change the deleted context, they are still disjoint
  disjAlμ (spn (Scns C₁ at₁))  (del C₂ s₂)   
    = Σ (C₁ ≡ C₂) (λ { refl → disjAtCtx at₁ s₂ })

  -- * A Schg is never disjoint from a deletion.
  disjAlμ (spn _)              (del C₂ s₂)   
    = ⊥

  -- * Since disjointness is symmetric, here we just repeat the cases above.
  disjAlμ (del C₁ s₁) (spn Scp)   = Unit
  disjAlμ (del C₁ s₁) (spn (Scns C₂ at₂))   
    = Σ (C₁ ≡ C₂) (λ { refl → disjAtCtx at₂ s₁ })
  disjAlμ (del C₁ s₁) (spn _) 
    = ⊥

  -- * Two deletions are never disjoint,
  --   since a patch is never disjoitn from itself.
  disjAlμ (del C₁ s₁) (del C₂ s₂) 
    = ⊥
  

  -- * disjCtx makes sure that the contexts are aligned and the patches
  --   within them are disjoint.
  disjCtx (here alμ₁ rest₁) (here alμ₂ rest₂) = disjAlμ alμ₁ alμ₂
  disjCtx (there a₁ ctx₁)   (there a₂ ctx₂)   = disjCtx ctx₁ ctx₂
  disjCtx _                 _                 = ⊥

  -- * disjAtCtx makes sure that the All At part of the Scns spine
  --   is all identities on the deleted part of the context and is
  --   disjoint in the field selected by the context.
  disjAtCtx [] ()
  disjAtCtx (fix a ∷ as) (here alμ rest) = disjAlμ a alμ × All-set identityAtμ as 
  disjAtCtx (a ∷ as)     (there a' ctx)  = identityAtμ a × disjAtCtx as ctx

  module DisjSymmetry where

    {-# TERMINATING #-}
    disjAlμ-sym : (alμ₁ alμ₂ : Alμ) → disjAlμ alμ₁ alμ₂ → disjAlμ alμ₂ alμ₁
 
    open DisjSymmetryF disjAlμ disjAlμ-sym public
   
    disjAlμ-sym (ins C₁ s₁) (ins C₂ s₂) ()
    disjAlμ-sym (ins C₁ s₁) (del C₂ s₂) hip                 = disjAlμ-sym (getCtx s₁) (del C₂ s₂) hip
    disjAlμ-sym (ins C₁ s₁) (spn s₂) hip                    = disjAlμ-sym (getCtx s₁) (spn s₂) hip
    disjAlμ-sym (del C₁ s₁) (ins C₂ s₂) hip                 = disjAlμ-sym (del C₁ s₁) (getCtx s₂) hip
    disjAlμ-sym (spn s₁)    (ins C₂ s₂) hip                 = disjAlμ-sym (spn s₁) (getCtx s₂) hip
    disjAlμ-sym (spn s₁) (spn s₂) hip                       = disjS-sym s₁ s₂ hip
    disjAlμ-sym (spn Scp) (del C₂ s₂) hip                   = unit
    disjAlμ-sym (spn (Scns C₁ at₁)) (del C₂ s₂) (refl , h1) = refl , h1
    disjAlμ-sym (spn (Schg _ _ _)) (del C₂ s₂)    ()
    disjAlμ-sym (del C₁ s₁) (spn Scp) hip                   = unit
    disjAlμ-sym (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , h1) = refl , h1
    disjAlμ-sym (del C₁ s₁) (spn (Schg _ _ _))  ()
    disjAlμ-sym (del C₁ s₁) (del C₂ s₂)  ()
