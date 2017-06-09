
open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Commutes.Functor
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
  open import Regular.Operations.Merge.Functor
                Rec _≟Rec_ PatchRec identityR disjRec mergeRec

  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  -- * Kleisli composition of application functions.
  applyS-seq : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(x : ⟦ σ ⟧S Rec)
             → Maybe (⟦ σ ⟧S Rec)
  applyS-seq s₁ s₂ x = applySAlAt applyRec s₁ x >>= applySAlAt applyRec s₂

  applySP-seq : {π : Prod}(p₁ p₂ : All (At PatchRec) π)(x : ⟦ π ⟧P Rec)
              → Maybe (⟦ π ⟧P Rec)
  applySP-seq p₁ p₂ x = applySP (applyAt applyRec) p₁ x >>= applySP (applyAt applyRec) p₂

  -- * Whenever s₁ and s₂ are disjoint, merging applies both changes.
  {-# TERMINATING #-}
  mergeS-commute : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂)
                  → ∀ x → applyS-seq s₁ s₂ x 
                        ≡ applySAlAt applyRec (mergeS s₁ s₂ hip) x

  mergeSP-commute : {π : Prod}(p₁ p₂ : All (At PatchRec) π)(hip : disjAts p₁ p₂)
                  → ∀ x → applySP-seq p₁ p₂ x
                        ≡ applySP (applyAt applyRec) (mergeAts p₁ p₂ hip) x

  mergeAtAll-commute : ∀{π₁ π₂}(ats : All (At PatchRec) π₁)(al : Al (At PatchRec) π₁ π₂)
                       (hip : disjAtAll ats al)
                     → ∀ x → (applySP (applyAt applyRec) ats x >>= applyAl (applyAt applyRec) al)
                           ≡ applyAl (applyAt applyRec) (mergeAtAll ats al hip) x
  private
    aux-lemma-1 : ∀{π₁ π₂}(at : All (At PatchRec) π₁)(al : Al (At PatchRec) π₁ π₂)
                → (hip : disjAtAll at al){Px Px' : ⟦ π₁ ⟧P Rec}
                → applySP (applyAt applyRec) at Px  ≡ just Px'
                → applyAl (applyAt applyRec) al Px  ≡ nothing
                → applyAl (applyAt applyRec) al Px' ≡ nothing
    aux-lemma-1 at al hip spJ alN = {!!}

    aux-lemma-2 : ∀{π₁ π₂}(at : All (At PatchRec) π₁)(al : Al (At PatchRec) π₁ π₂)
                → (hip : disjAtAll at al){Px Px' : ⟦ π₁ ⟧P Rec}{Px'' : ⟦ π₂ ⟧P Rec}
                → applySP (applyAt applyRec) at Px  ≡ just Px'
                → applyAl (applyAt applyRec) al Px  ≡ just Px'' 
                → applyAl (applyAt applyRec) al Px' ≡ {!!}
    aux-lemma-2 at al hip spJ alN = {!!}


  mergeS-commute Scp s₂ hip x = refl
  mergeS-commute (Scns C₁ at₁) Scp hip x 
    with applySAlAt applyRec (Scns C₁ at₁) x 
  ...| nothing = refl
  ...| just x' = refl
  mergeS-commute (Schg C₁ C₂ {q} al) Scp hip x 
    with applySAlAt applyRec (Schg C₁ C₂ {q} al) x
  ...| nothing = refl 
  ...| just x' = refl
  mergeS-commute (Schg _ _ _) (Schg _ _ _) () _
  mergeS-commute {σ} (Scns C₁ at₁) (Scns _ at₂) (refl , hip) x 
    with sop x
  ...| tag Cx Px with C₁ ≟F Cx
  ...| no   _   = refl
  ...| yes refl 
    rewrite sym (mergeSP-commute at₁ at₂ hip Px)
    with applySP (applyAt applyRec) at₁ Px
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} Cx Px' 
    with Cx ≟F Cx
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl
  mergeS-commute {σ} (Scns C₁ at₁) (Schg C₂ C₃ {q} al₂) (refl , hip) x 
    with sop x
  ...| tag Cx Px with C₁ ≟F Cx
  ...| no _     = refl
  ...| yes refl 
    rewrite sym (mergeAtAll-commute at₁ al₂ hip Px)
    with applySP (applyAt applyRec) at₁ Px
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} Cx Px'
    with Cx ≟F Cx
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl 
  mergeS-commute {σ} (Schg C₁ C₂ {q} al₁) (Scns C₃ at₂) (refl , hip) x
    with sop x
  ...| tag Cx Px with C₁ ≟F Cx
  ...| no _     = refl
  ...| yes refl
    rewrite sym (mergeAtAll-commute at₂ al₁ hip Px)
    with applySP (applyAt applyRec) at₂ Px | inspect (applySP (applyAt applyRec) at₂) Px
  ...| nothing  | [ appSP ] 
    with applyAl (applyAt applyRec) al₁ Px 
  ...| nothing = refl
  ...| just Px'' 
    rewrite sop-inj-lemma {σ} C₂ Px''
    with Cx ≟F C₂
  ...| no  _   = refl
  ...| yes abs = ⊥-elim (q abs)
  mergeS-commute {σ}  (Schg C₁ C₂ {q} al₁) (Scns C₃ at₂) (refl , hip) x
     | tag Cx Px | yes refl | just Px' | [ appSP ] 
     with applyAl (applyAt applyRec) al₁ Px | inspect (applyAl (applyAt applyRec) al₁) Px
  ...| nothing | [ appAL1 ] rewrite aux-lemma-1 at₂ al₁ hip appSP appAL1 = refl
  ...| just Qx | [ appAL1 ] = {!!}


  mergeSP-commute = {!!}

  mergeAtAll-commute = {!!}
