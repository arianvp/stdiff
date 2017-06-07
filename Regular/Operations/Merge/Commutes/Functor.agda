
open import Prelude
open import Generic.Regular

module Regular.Predicates.Disjoint.Merge.Commutes.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
       (mergeRec  : (p₁ p₂ : PatchRec)(hip : disjRec p₁ p₂) → PatchRec)
       (applyRec  : PatchRec → Rec → Maybe Rec)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor 
                Rec _≟Rec_ PatchRec identityR
  open import Regular.Predicates.Disjoint.Functor 
                Rec _≟Rec_ PatchRec identityR disjRec
  open import Regular.Predicates.Disjoint.Merge.Functor
                Rec _≟Rec_ PatchRec identityR disjRec mergeRec

  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  applyS-seq : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(x : ⟦ σ ⟧S Rec)
             → Maybe (⟦ σ ⟧S Rec)
  applyS-seq s₁ s₂ x = applySAlAt applyRec s₁ x >>= applySAlAt applyRec s₂

  mergeS-commute1 : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂)
                  → ∀ x → applyS-seq s₁ s₂ x 
                        ≡ applySAlAt applyRec (mergeS s₁ s₂ hip) x
  mergeS-commute1 Scp s₂ hip x = refl
  mergeS-commute1 (Scns C₁ at₁) Scp hip x 
    with applySAlAt applyRec (Scns C₁ at₁) x 
  ...| nothing = refl
  ...| just x' = refl
  mergeS-commute1 (Schg C₁ C₂ {q} al) Scp hip x 
    with applySAlAt applyRec (Schg C₁ C₂ {q} al) x
  ...| nothing = refl 
  ...| just x' = refl
  mergeS-commute1 (Schg _ _ _) (Schg _ _ _) () _
  mergeS-commute1 {σ} (Scns C₁ at₁)    (Scns _ at₂) (refl , hip) x 
    with sop x
  ...| tag Cx Px with Cx ≟F C₁
  ...| no _  = {!!}
  ...| yes _ = {!!} 
  mergeS-commute1 (Scns C₁ at₁)    (Schg C₂ C₃ {q} al₂) (refl , hip) x = {!!}
  mergeS-commute1 (Schg C₁ C₂ {q} al₁) (Scns C₃ at₂) (refl , hip) x = {!!}
  
