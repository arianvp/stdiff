open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (_∈domRec_ : Rec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_


  _∈domS_  : {σ : Sum}       → ⟦ σ ⟧S Rec  → Patch PatchRec σ       → Set
  _∈domAl_ : {π₁ π₂ : Prod}  → ⟦ π₁ ⟧P Rec → Al (At PatchRec) π₁ π₂ → Set
  _∈domAt_ : {α : Atom}      → ⟦ α ⟧A Rec  → At PatchRec α          → Set

  s ∈domS Scp = Unit
  s ∈domS Scns C ats with match C s
  ...| nothing = ⊥
  ...| just p  = All-set (uncurry _∈domAt_) (zipd p ats)
  s ∈domS Schg C₁ C₂ al with match C₁ s
  ...| nothing = ⊥
  ...| just p  = p ∈domAl al  

  []       ∈domAl A0          = Unit
  p        ∈domAl (Ains x al) = p  ∈domAl al
  (p ∷ ps) ∈domAl (Adel x al) = ps ∈domAl al
  (p ∷ ps) ∈domAl (AX at  al) = p ∈domAt at × ps ∈domAl al 

  a ∈domAt set (k₁ , k₂) 
    with k₁ ≟K k₂
  ...| yes _ = Unit
  ...| no  _ = a ≡ k₁
  a ∈domAt fix x = a ∈domRec x
