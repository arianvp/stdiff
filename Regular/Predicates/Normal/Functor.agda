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


  -- * The only part of the Functor-layer that 
  --   requires some fixing is the Alignment.
  --
  --   We say that a patch is in normal form
  --   iff it has the form:
  --
  --     (del* ins* mod*)*
  --
  -- 
  normAl normAl-I normAl-M normAl-D 
    : ∀{π₁ π₂} → Al (At PatchRec) π₁ π₂ → Set

  normAl = normAl-D

  normAl-D A0           = Unit
  normAl-D (Adel at al) = normAl-D al
  normAl-D (Ains at al) = normAl-I al
  normAl-D (AX _ _)     = ⊥

  normAl-I A0           = Unit
  normAl-I (Ains at al) = normAl-I al
  normAl-I (AX at al)   = normAl-M al
  normAl-I (Adel _ _)   = ⊥

  normAl-M A0           = Unit
  normAl-M (AX at al)   = normAl-M al 
  normAl-M (Adel at al) = normAl-D al
  normAl-M (Ains _ _)   = ⊥

  normSP : ∀{π} → All (At PatchRec) π → Set
  normSP = All-set normAt

  normS : ∀{σ} → Patch PatchRec σ → Set
  normS Scp           = Unit
  normS (Scns _ ats)  = normSP ats
  normS (Schg _ _ al) = normAl al



