open import Prelude
open import Generic.Regular

module Regular.Predicates.Disjoint.Merge.Domain.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
       (mergeRec  : (p₁ p₂ : PatchRec)(hip : disjRec p₁ p₂) → PatchRec)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (_∈domRec_ : Rec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor Rec _≟Rec_ PatchRec identityR
  open import Regular.Predicates.Disjoint.Functor Rec _≟Rec_ PatchRec identityR disjRec
  open import Regular.Predicates.Disjoint.Merge.Functor
    Rec _≟Rec_ PatchRec identityR disjRec mergeRec
  open import Regular.Predicates.Domain.Functor
    Rec _≟Rec_ PatchRec applyRec _∈domRec_


  -- XXX: This is more or less what I had in mind
  --      for estabilishing the domain of the merge,
  --     
  --      A proof that the application commutes
  --      might be more interesting.
  dom-mergeS : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)
             → (hip : disjS s₁ s₂)
             → ∀ x → x ∈domS (mergeS s₁ s₂ hip)
                   → x ∈domS s₁ × x ∈domS s₂

  dom-mergeS Scp          s₂  hip x hipx = unit , hipx
  dom-mergeS (Scns _ _)   Scp hip x hipx = hipx , unit
  dom-mergeS (Schg _ _ _) Scp hip x hipx = hipx , unit
  dom-mergeS s₁ s₂ hip x hipx = {!!}
