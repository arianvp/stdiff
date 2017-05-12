open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Functor
       (Rec      : Set)
       (_≟Rec_   : (x y : Rec) → Dec (x ≡ y))
       (PatchRec : Set)
       (idRec    : PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_

  identityS  : {σ     : Sum}  → S (At PatchRec) (Al (At PatchRec)) σ → Set
  identityAl : {π₁ π₂ : Prod} → Al (At PatchRec) π₁ π₂          → Set
  identityAt : {α     : Atom} → At PatchRec α                   → Set

  identityS Scp = Unit
  identityS (Scns C₁ al) = all-identityAt al
    where
      all-identityAt : ∀{l} → All (At PatchRec) l → Set
      all-identityAt []       = Unit
      all-identityAt (a ∷ as) = identityAt a × all-identityAt as
  identityS _   = ⊥

  identityAl A0         = Unit
  identityAl (AX at al) = identityAt at × identityAl al
  identityAl _          = ⊥

  identityAt (set ks)  = proj₁ ks ≡ proj₂ ks
  identityAt (fix spμ) = idRec spμ
