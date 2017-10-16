open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (makeidR   : Rec → PatchRec)
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

  makeidS  : {σ : Sum } → ⟦ σ ⟧S Rec → Patch PatchRec σ
  makeidAl : {π : Prod} → ⟦ π ⟧P Rec → Al (At PatchRec) π π
  makeidAt : {α : Atom} → ⟦ α ⟧A Rec → At PatchRec α
  
  makeidS _ = Scp

  makeidAl []       = A0
  makeidAl (a ∷ as) = AX (makeidAt a) (makeidAl as)

  makeidAt {I}   x = fix (makeidR x)
  makeidAt {K κ} x = set (x , x)

  module IdentityPropertiesF 
         (applyRec            : PatchRec → Rec → Maybe Rec)
         (identityRec-correct : (p : PatchRec)(hip : identityR p) 
                              → ∀ x → applyRec p x ≡ just x)
         (makeidRec-correct   : (r : Rec) → identityR (makeidR r))
      where

    identityS-correct : {σ : Sum}(s : Patch PatchRec σ)(hip : identityS s)
                      → ∀ x → applyPatch applyRec s x ≡ just x
    identityS-correct Scp hip x = refl
    identityS-correct (Scns _ _) () x
    identityS-correct (Schg _ _ _) () x

    identityAt-correct : {α : Atom}(a : At PatchRec α)(hip : identityAt a)
                      → ∀ x → applyAt applyRec a x ≡ just x
    identityAt-correct (set (k₁ , k₂)) hip x 
      with k₁ ≟K k₂ 
    ...| no abs   = ⊥-elim (abs hip) 
    ...| yes refl = refl
    identityAt-correct (fix rec) hip x 
      = identityRec-correct rec hip x

    makeidAt-correct : {α : Atom}(a : ⟦ α ⟧A Rec) → identityAt {α} (makeidAt a)
    makeidAt-correct {I}   a = makeidRec-correct a
    makeidAt-correct {K κ} a = refl

    makeidS-correct : {σ : Sum}(s : ⟦ σ ⟧S Rec) → identityS {σ} (makeidS s)
    makeidS-correct _ = unit
