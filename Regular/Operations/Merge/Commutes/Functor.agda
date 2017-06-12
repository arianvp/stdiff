open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Commutes.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (makeidR   : Rec → PatchRec)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
       (disjRecSym    : (r₁ r₂ : PatchRec) → disjRec r₁ r₂ → disjRec r₂ r₁) 
       (disjRecSymInv : (r₁ r₂ : PatchRec)(h : disjRec r₁ r₂)
                      → disjRecSym r₂ r₁ (disjRecSym r₁ r₂ h) ≡ h) 
       (mergeRec  : (p₁ p₂ : PatchRec)(hip : disjRec p₁ p₂) → PatchRec)
       (applyRec  : PatchRec → Rec → Maybe Rec)
    where

  -- * Basic patches-over-functors functionality and predicates.
  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor 
                Rec _≟Rec_ PatchRec makeidR identityR
  open import Regular.Predicates.Disjoint.Functor 
                Rec _≟Rec_ PatchRec makeidR identityR disjRec
  open import Regular.Operations.Merge.Functor
                Rec _≟Rec_ PatchRec makeidR identityR disjRec mergeRec

  -- * Disjointness is symmetric
  open DisjSymmetry disjRecSym disjRecSymInv

  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

  -- * Renames the application functions to ⟪_⟫ ; makes life easier.
  open import Regular.Functor Rec _≟Rec_ using (module FunctorApplication)
  open FunctorApplication PatchRec applyRec

  -- * XXX: To be refactored:
  --   Auxiliary lemmas about application
  
  ⟪⟫Scns-comp : {σ : Sum}{C : Constr σ}{a₁ a₂ : All (At PatchRec) (typeOf σ C)}
              → ∀ x → (⟪ Scns {σ = σ} C a₁ ⟫S ∙ ⟪ Scns C a₂ ⟫S) x
                    ≡ ((just ∘ inj {σ} C) ∙ ⟪ a₁ ⟫SP ∙ ⟪ a₂ ⟫SP ∙ match C) x
  ⟪⟫Scns-comp {σ} {C} {a₁} {a₂} x with sop x
  ...| tag Cx Px with C ≟F Cx 
  ...| no _     = refl
  ...| yes refl 
    with ⟪ a₂ ⟫SP Px 
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} Cx Px' 
    with Cx ≟F Cx
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl

  ⟪⟫Schg-inj-natural : {σ : Sum}{C D : Constr σ}{q : C ≢ D}
                       (al : Al (At PatchRec) (typeOf σ C) (typeOf σ D))
                       (at : All (At PatchRec) (typeOf σ C))
                     → ∀ x → (Maybe-map (inj {σ} C) (⟪ at ⟫SP x) 
                             >>= ⟪ Schg {σ = σ} C D {q} al ⟫S )
                           ≡ ((just ∘ inj {σ} D) ∙ ⟪ al ⟫P ∙ ⟪ at ⟫SP) x
  ⟪⟫Schg-inj-natural {σ} {C} {D} {q} al at x 
    with ⟪ at ⟫SP x
  ...| nothing = refl
  ...| just x' 
    rewrite sop-inj-lemma {σ} C x'
    with C ≟F C
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl


  -- * We need a bunch of commutation proofs; one for each "level" of the universe.
  --

  merge-At-Al-commute : ∀{π₁ π₂}(ats : All (At PatchRec) π₁)(al : Al (At PatchRec) π₁ π₂)
                      → (hip : disj-At-Al ats al)
                      → ∀ x → (⟪ merge-At-Al ats al hip ⟫P ∙ ⟪ ats ⟫SP) x
                            ≡ (⟪ merge-Al-At al ats (disj-At-Al-sym ats al hip) ⟫SP ∙ ⟪ al ⟫P) x
  merge-At-Al-commute = {!!}


  -- * Whenever s₁ and s₂ are disjoint, merging applies both changes.
  {-# TERMINATING #-}
  mergeS-commute : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂)
                  → ∀ x → (⟪ mergeS s₁ s₂ hip ⟫S ∙ ⟪ s₁ ⟫S) x
                        ≡ (⟪ mergeS s₂ s₁ (disjS-sym s₁ s₂ hip) ⟫S ∙ ⟪ s₂ ⟫S) x

  mergeAt-commute : {α : Atom}(a₁ a₂ : At PatchRec α)(hip : disjAt a₁ a₂)
                  → ∀ x → (⟪ mergeAt a₁ a₂ hip ⟫A ∙ ⟪ a₁ ⟫A) x
                        ≡ (⟪ mergeAt a₂ a₁ (disjAt-sym a₁ a₂ hip) ⟫A ∙ ⟪ a₂ ⟫A) x
  mergeAt-commute a₁ a₂ hip x = {!!}


  mergeSP-commute : {π : Prod}(p₁ p₂ : All (At PatchRec) π)(hip : disjAts p₁ p₂)
                  → ∀ x → (⟪ mergeAts p₁ p₂ hip ⟫SP ∙ ⟪ p₁ ⟫SP) x
                        ≡ (⟪ mergeAts p₂ p₁ (disjAts-sym p₁ p₂ hip) ⟫SP ∙ ⟪ p₂ ⟫SP) x

  mergeSP-commute []         []         hip x = refl
  mergeSP-commute (a₁ ∷ as₁) (a₂ ∷ as₂) (h0 , h1) (x ∷ xs)
    = {!!} 

  mergeS-commute Scp Scp hip x = refl
  mergeS-commute Scp (Scns C₂ at₂) hip x 
    with ⟪ Scns C₂ at₂ ⟫S x 
  ...| nothing = refl
  ...| just x' = refl
  mergeS-commute Scp (Schg C₂ C₃ {q} al₂) hip x 
    with ⟪ Schg C₂ C₃ {q} al₂ ⟫S x
  ...| nothing = refl
  ...| just x' = refl
  mergeS-commute (Scns C₁ at₁) Scp hip x 
    with ⟪ Scns C₁ at₁ ⟫S x 
  ...| nothing = refl
  ...| just x' = refl
  mergeS-commute (Schg C₁ C₂ {q} al) Scp hip x 
    with ⟪ Schg C₁ C₂ {q} al ⟫S x
  ...| nothing = refl
  ...| just x' = refl
  mergeS-commute (Schg _ _ _) (Schg _ _ _) () _
  mergeS-commute {σ} (Scns C₁ at₁) (Scns _ at₂) (refl , hip) x 
    rewrite ⟪⟫Scns-comp {σ} {C₁} {mergeAts at₁ at₂ hip} {at₁} x
          | ⟪⟫Scns-comp {σ} {C₁} {at₂} {mergeAts at₂ at₁ (disjAts-sym at₁ at₂ hip)} x 
    with sop x
  ...| tag Cx Px with C₁ ≟F Cx
  ...| no _     = refl
  ...| yes refl 
    rewrite mergeSP-commute at₁ at₂ hip Px
    with ⟪ at₂ ⟫SP Px
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} Cx Px'
    with Cx ≟F Cx
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl
  mergeS-commute {σ} (Scns C₁ at₁) (Schg C₂ C₃ {q} al₂) (refl , hip) x 
    with sop x
  ...| tag Cx Px 
    with C₁ ≟F Cx
  ...| no C₁≢Cx 
    with C₃ ≟F Cx
  ...| no C₃≢Cx = refl
  ...| yes refl with ⟪ merge-Al-At al₂ at₁ (disj-At-Al-sym at₁ al₂ hip) ⟫SP Px
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} Cx Px'
    with C₁ ≟F Cx
  ...| no _    = refl
  ...| yes abs = ⊥-elim (C₁≢Cx abs)
  mergeS-commute {σ} (Scns C₁ at₁) (Schg C₂ C₃ {q} al₂) (refl , hip) x
     | tag Cx Px 
     | yes refl
    rewrite ⟪⟫Schg-inj-natural {σ} {Cx} {C₃} {q} (merge-At-Al at₁ al₂ hip) at₁ Px
          | merge-At-Al-commute at₁ al₂ hip Px
       with ⟪ al₂ ⟫P Px
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} C₃ Px'
    with C₃ ≟F C₃
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl
  mergeS-commute {σ} (Schg C₁ C₂ {q} al₁) (Scns _ at₂) (refl , hip) x
    with sop x
  ...| tag Cx Px with C₁ ≟F Cx
  ...| no C₁≢Cx with C₂ ≟F Cx
  ...| no C₂≢Cx = refl
  ...| yes refl with ⟪ merge-Al-At al₁ at₂ hip ⟫SP Px
  ...| nothing  = refl
  ...| just Px'
    rewrite sop-inj-lemma {σ} Cx Px'
    with C₁ ≟F Cx
  ...| no _    = refl
  ...| yes abs = ⊥-elim (C₁≢Cx abs)
  mergeS-commute {σ} (Schg C₁ C₂ {q} al₁) (Scns _ at₂) (refl , hip) x
     | tag Cx Px | yes refl 
    rewrite ⟪⟫Schg-inj-natural {σ} {Cx} {C₂} {q} 
                               (merge-At-Al at₂ al₁ (disj-Al-At-sym al₁ at₂ hip)) 
                               at₂ Px
          | merge-At-Al-commute at₂ al₁ (disj-Al-At-sym al₁ at₂ hip) Px
          | disj-Al-At-sym-inv al₁ at₂ hip
       with ⟪ al₁ ⟫P Px
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} C₂ Px'
    with C₂ ≟F C₂
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl

{-
    with sop x
  ...| tag Cx Px with C₁ ≟F Cx
  ...| no _     = {!!}
  ...| yes refl = {!!}
-}
{-

  mergeSP-commute = {!!}

  mergeAtAll-commute = {!!}
-}
