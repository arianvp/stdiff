open import Prelude
open import Generic.Regular

module Regular.Operations.Inverse.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (invRec    : PatchRec → PatchRec)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  
  invAt : ∀{α} → At PatchRec α → At PatchRec α
  invAt (set (k₁ , k₂)) = set (k₂ , k₁)
  invAt (fix rec)       = fix (invRec rec)

  invAl : ∀{π₁ π₂} → Al (At PatchRec) π₁ π₂ → Al (At PatchRec) π₂ π₁
  invAl A0 = A0
  invAl (Ains C al) = Adel C (invAl al)
  invAl (Adel C al) = Ains C (invAl al)
  invAl (AX at  al) = AX (invAt at) (invAl al)

  invS  : ∀{σ} → Patch PatchRec σ → Patch PatchRec σ
  invS Scp                 = Scp
  invS (Scns C ats)        = Scns C (All-map invAt ats)
  invS (Schg C₁ C₂ {q} al) = Schg C₂ C₁ {q ∘ sym} (invAl al)
