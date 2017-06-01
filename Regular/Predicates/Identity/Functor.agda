open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (identityR : PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  
  identityS  : {σ     : Sum}(s : Patch PatchRec σ) → Set
  identityAl : {π₁ π₂ : Prod}(p : Al (At PatchRec) π₁ π₂) → Set
  identityAt : {α     : Atom}(a : At PatchRec α) → Set

  identityS Scp = Unit
  identityS _   = ⊥

  identityAl A0         = Unit
  identityAl (AX at al) = identityAt at × identityAl al
  identityAl _          = ⊥

  identityK : {κ : Konst} → TrivialK κ → Set
  identityK (k₁ , k₂) = k₁ ≡ k₂

  identityAt (set k₁k₂) = identityK k₁k₂
  identityAt (fix rec)  = identityR rec

