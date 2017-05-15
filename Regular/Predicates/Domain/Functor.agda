open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Functor
       (Rec      : Set)
       (_≟Rec_   : (x y : Rec) → Dec (x ≡ y))
       (PatchRec : Set)
       (applyRec : PatchRec → Rec → Maybe Rec)
    where

  open import Regular.Internal.Functor Rec _≟Rec_

  _∈domS_ : {σ : Sum} → ⟦ σ ⟧S Rec → S (At PatchRec) (Al (At PatchRec)) σ 
          → Set
  s ∈domS sp = IsJust (applyS (applyAt applyRec) (applyAl (applyAt applyRec)) sp s)

  _∈domAl_ : {π₁ π₂ : Prod} → ⟦ π₁ ⟧P Rec → Al (At PatchRec) π₁ π₂ → Set
  p ∈domAl al = IsJust (applyAl (applyAt applyRec) al p)

  _∈domAt_ : {α : Atom} → ⟦ α ⟧A Rec → At PatchRec α → Set
  a ∈domAt at = IsJust (applyAt applyRec at a)
