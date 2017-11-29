open import Prelude
open import Generic.Regular

module Regular.Predicates.Normal.Functor
      (Rec       : Set)
      (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
      (PatchRec  : Set)
      (normRec   : PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_

  normAt : ∀{α} → At PatchRec α → Set
  normAt (set k₁k₂) = Unit
  normAt (fix rec)  = normRec rec

  normAl : ∀{π₁ π₂} → Al (At PatchRec) π₁ π₂ → Set
  normAl A0           = Unit
  normAl (AX at al)   = normAl al
  normAl (Ains at al) = normAl al
  normAl (Adel at A0)            = Unit
  normAl (Adel at (Ains _ _))    = ⊥
  normAl (Adel at (AX at' al))   = normAl al
  normAl (Adel at (Adel {α = α} at' al)) = normAl (Adel {α = α} at' al)

  normSP : ∀{π} → All (At PatchRec) π → Set
  normSP = {!!}

  normS : ∀{σ} → Patch PatchRec σ → Set
  normS = {!!}



