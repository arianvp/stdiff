open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Soundness.Functor 
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (AppRec-ok : (x y : Rec)(p : PatchRec)
                  → applyRec p x ≡ just y
                  → AppRec x y p)
    where

  open import Regular.Functor Rec _≟Rec_
  open FunctorApplication PatchRec applyRec
  open import Regular.Predicates.Applies.Functor
    Rec _≟Rec_ PatchRec AppRec

  AppAt-sound : ∀{α}{a₁ a₂ : ⟦ α ⟧A Rec}{p : At PatchRec α}
                → ⟪ p ⟫A a₁ ≡ just a₂
                → AppAt a₁ a₂ p
  AppAt-sound hip = {!!}

  AppAl-sound : ∀{π₁ π₂}{p₁ : ⟦ π₁ ⟧P Rec}{p₂ : ⟦ π₂ ⟧P Rec}
                → {al : Al (At PatchRec) π₁ π₂}
                → ⟪ al ⟫P p₁ ≡ just p₂
                → AppAl p₁ p₂ al
  AppAl-sound hip = {!!}


  AppSP-sound : ∀{π}{p₁ p₂ : ⟦ π ⟧P Rec}
                → {ps : All (At PatchRec) π}
                → ⟪ ps ⟫SP p₁ ≡ just p₂
                → All-zip3-set AppAt p₁ p₂ ps
  AppSP-sound hip = {!!}

  
  AppS-sound : ∀{σ}{s₁ s₂ : ⟦ σ ⟧S Rec}{p : Patch PatchRec σ}
               → ⟪ p ⟫S s₁ ≡ just s₂
               → AppS s₁ s₂ p
  AppS-sound hip = {!!}
