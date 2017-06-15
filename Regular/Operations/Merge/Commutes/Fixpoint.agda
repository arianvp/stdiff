open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Commutes.Fixpoint (σμ : Sum) where

  -- * Basic patches-over-fixpoints functionality
  open import Regular.Internal.Fixpoint σμ
  open import Regular.Internal.Functor (Fix σμ) _≟Fix_
  open import Regular.Fixpoint σμ using (module FixpointApplication)
  open FixpointApplication
  open import Regular.Predicates.Identity.Fixpoint σμ
  open import Regular.Predicates.Disjoint.Fixpoint σμ
  open import Regular.Operations.Merge.Fixpoint σμ
  
  -- * Symmetry of disjAlμ
  open DisjSymmetry
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

  -- * We need the proofs we developed for functors
  open import Regular.Operations.Merge.Commutes.Functor
                (Fix σμ) _≟Fix_ Alμ makeidAlμ identityAlμ disjAlμ disjAlμ-sym disjAlμ-sym-inv
                mergeAlμ ⟪_⟫μ

  -- *******************************************
  -- *
  -- * The final result is mergeAlμ-commute;
  -- *
  -- *
  {-# TERMINATING #-}
  mergeAlμ-commute : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂)
                   → ∀ x → (⟪ mergeAlμ alμ₁ alμ₂ hip ⟫μ ∙ ⟪ alμ₁ ⟫μ) x 
                         ≡ (⟪ mergeAlμ alμ₂ alμ₁ (disjAlμ-sym alμ₁ alμ₂ hip) ⟫μ ∙ ⟪ alμ₂ ⟫μ) x

  -- * which needs to be passed to our previously developed proof for functors.
  open MergeCommutesHip mergeAlμ-commute

  
  ⟪⟫-spn-spn-fusion
    : (s₁ s₂ : Patch Alμ σμ)
    → ∀ x → (⟪ spn s₁ ⟫μ ∙ ⟪ spn s₂ ⟫μ) x
          ≡ ((λ x → just ⟨ x ⟩) ∙ ⟪ s₁ ⟫S ∙ ⟪ s₂ ⟫S ∙ (just ∘ unfix)) x
  ⟪⟫-spn-spn-fusion s₁ s₂ x = {!!}
{-
  ⟪⟫Scns-inCtx-commute
    : ⟪ spn (Scns C ats) ⟫μ ∙ ((⟨_⟩ ∘ inj C) <$> inCtx ctx x)
    ≡ inCtx 
-}
  mergeAlμ-commute (ins C₁ s₁) (ins C₂ s₂) ()
  mergeAlμ-commute (ins C₁ s₁) (spn s₂)    hip ⟨ x ⟩ 
    = cong id {!!}
  mergeAlμ-commute (ins C₁ s₁) (del C₂ s₂) hip x
    = {!!}
  mergeAlμ-commute (spn s₁)   (ins C₂ s₂)  hip x 
    = {!!}
  mergeAlμ-commute (del C s₁) (ins C₂ s₂)  hip x 
    = {!!}

  mergeAlμ-commute (spn s₁) (spn s₂)       hip ⟨ x ⟩ 
    rewrite mergeS-commute s₁ s₂ hip x 
          | ⟪⟫-spn-spn-fusion s₁ s₂ ⟨ x ⟩
          = {!!}
          -- | mergeS-commute s₁ s₂ hip x
          -- = {!!}
  mergeAlμ-commute (spn Scp) (del C₂ s₂)   hip x 
    = {!!}
  mergeAlμ-commute (spn (Scns C₁ at₁))  (del C₂ s₂) hip x 
    = {!!}
  mergeAlμ-commute (spn (Schg _ _ _)) (del C₂ s₂) ()
  mergeAlμ-commute (del C₁ s₁) (spn Scp)   hip x
    = {!!}
  mergeAlμ-commute (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , hip) x
    = {!!}
  mergeAlμ-commute (del C₁ s₁) (spn (Schg _ _ _)) ()
  mergeAlμ-commute (del C₁ s₁) (del C₂ s₂) ()

