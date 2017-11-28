open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Correctness.Functor 
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (AppRec-ok : (x y : Rec)(p : PatchRec)
                  → AppRec x y p
                  → applyRec p x ≡ just y)
    where

  open import Regular.Functor Rec _≟Rec_
  open FunctorApplication PatchRec applyRec
  open import Regular.Predicates.Applies.Functor
    Rec _≟Rec_ PatchRec AppRec

  AppAt-correct : ∀{α}{a₁ a₂ : ⟦ α ⟧A Rec}{p : At PatchRec α}
                → AppAt a₁ a₂ p
                → ⟪ p ⟫A a₁ ≡ just a₂
  AppAt-correct hip = {!!}

  AppAl-correct : ∀{π₁ π₂}{p₁ : ⟦ π₁ ⟧P Rec}{p₂ : ⟦ π₂ ⟧P Rec}
                → {al : Al (At PatchRec) π₁ π₂}
                → AppAl p₁ p₂ al
                → ⟪ al ⟫P p₁ ≡ just p₂
  AppAl-correct hip = {!!}


  AppSP-correct : ∀{π}{p₁ p₂ : ⟦ π ⟧P Rec}
                → {ps : All (At PatchRec) π}
                → All-zip3-set AppAt p₁ p₂ ps
                → ⟪ ps ⟫SP p₁ ≡ just p₂
  AppSP-correct hip = {!!}

  
  AppS-correct : ∀{σ}{s₁ s₂ : ⟦ σ ⟧S Rec}{p : Patch PatchRec σ}
               → AppS s₁ s₂ p
               → ⟪ p ⟫S s₁ ≡ just s₂
  AppS-correct hip = {!!}
