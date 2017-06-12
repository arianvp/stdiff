open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (makeidR   : Rec → PatchRec)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
       (mergeRec  : (p₁ p₂ : PatchRec)(hip : disjRec p₁ p₂) → PatchRec)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor Rec _≟Rec_ PatchRec makeidR identityR
  open import Regular.Predicates.Disjoint.Functor Rec _≟Rec_ PatchRec makeidR identityR disjRec

  mergeS  : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂) → Patch PatchRec σ

  mergeAt : {α : Atom}(a₁ a₂ : At PatchRec α)(hip : disjAt a₁ a₂)
          → At PatchRec α

  merge-At-Al : ∀{l₁ l₂}(ats : All (At PatchRec) l₁)(al : Al (At PatchRec) l₁ l₂)
             → (hip : disj-At-Al ats al) 
             → Al (At PatchRec) l₁ l₂ 
  merge-At-Al []       al  hip = al
  merge-At-Al (a ∷ as) (Ains at al) hip 
    = Ains at (merge-At-Al (a ∷ as) al hip)
  merge-At-Al (a ∷ as) (Adel at al) (ida , hip) 
    = Adel at (merge-At-Al as al hip)
  merge-At-Al (a ∷ as) (AX at al)   (ha , hip) 
    = AX (mergeAt a at ha) (merge-At-Al as al hip)

  merge-Al-At : ∀{l₁ l₂}(al : Al (At PatchRec) l₁ l₂)(ats : All (At PatchRec) l₁)
             → (hip : disj-Al-At al ats) 
             → All (At PatchRec) l₂ 
  merge-Al-At A0 []  hip = []
  merge-Al-At (Ains at al) [] hip 
    = makeidAt at ∷ merge-Al-At al [] hip
  merge-Al-At (Ains at al) (a ∷ as) hip 
    = makeidAt at ∷ merge-Al-At al (a ∷ as) hip
  merge-Al-At (Adel at al) (a ∷ as) (ida , hip) 
    = merge-Al-At al as hip
  merge-Al-At (AX at al)   (a ∷ as)   (ha , hip) 
    = at ∷ merge-Al-At al as hip

  mergeAts : ∀{l}(a₁ a₂ : All (At PatchRec) l)(hip : disjAts a₁ a₂) → All (At PatchRec) l
  mergeAts []         []         hip = []
  mergeAts (a₁ ∷ as₁) (a₂ ∷ as₂) (ha , hip) = mergeAt a₁ a₂ ha ∷ mergeAts as₁ as₂ hip

  mergeS Scp              s   hip = s
  mergeS s                Scp hip = Scp 

  mergeS {σ} (Scns C₁ at₁)    (Scns C₂ at₂) (refl , hip) 
    = Scns C₁ (mergeAts at₁ at₂ hip)

  mergeS (Scns C₁ at₁)    (Schg C₂ C₃ {q} al₂) (refl , hip)
    = Schg C₁ C₃ {q} (merge-At-Al at₁ al₂ hip)

  mergeS (Schg C₁ C₂ {q} al₁) (Scns C₃ at₂) (refl , hip)
    = Scns C₂ (merge-Al-At al₁ at₂ hip)

  mergeS (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂) ()

  mergeAt (set ks₁)  (set ks₂)  (inj₁ _) = set ks₂
  mergeAt (set ks₁)  (set ks₂)  (inj₂ _) = set ks₁
  mergeAt (fix spμ₁) (fix spμ₂) hip      = fix (mergeRec spμ₁ spμ₂ hip)

  module MergeSymmetry 
         (disjRecSym    : (r₁ r₂ : PatchRec) → disjRec r₁ r₂ → disjRec r₂ r₁)
         (disjRecSymInv : (r₁ r₂ : PatchRec)(h : disjRec r₁ r₂)
                        → disjRecSym r₂ r₁ (disjRecSym r₁ r₂ h) ≡ h) 
         (mergeRecSym   : (r₁ r₂ : PatchRec)(h : disjRec r₁ r₂)
                        → mergeRec r₁ r₂ h ≡ mergeRec r₂ r₁ (disjRecSym r₁ r₂ h))
      where

    open DisjSymmetry disjRecSym disjRecSymInv
{-
    mergeS-sym : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂) 
               → mergeS s₁ s₂ hip ≡ mergeS s₂ s₁ (disjS-sym s₁ s₂ hip)

    mergeAt-sym : {α : Atom}(a₁ a₂ : At PatchRec α)(hip : disjAt a₁ a₂)
                → mergeAt a₁ a₂ hip ≡ mergeAt a₂ a₁ (disjAt-sym a₁ a₂ hip)

    mergeAts-sym : ∀{l}(a₁ a₂ : All (At PatchRec) l)(hip : disjAts a₁ a₂) 
             → mergeAts a₁ a₂ hip ≡ mergeAts a₂ a₁ (disjAts-sym a₁ a₂ hip)
    mergeAts-sym []         []         hip = refl
    mergeAts-sym (a₁ ∷ as₁) (a₂ ∷ as₂) (ha , hip) 
      = cong₂ _∷_ (mergeAt-sym a₁ a₂ ha) (mergeAts-sym as₁ as₂ hip)

    mergeAt-sym (set ks₁)  (set ks₂)  (inj₁ _) = refl
    mergeAt-sym (set ks₁)  (set ks₂)  (inj₂ _) = refl
    mergeAt-sym (fix spμ₁) (fix spμ₂) hip      
      = cong fix (mergeRecSym spμ₁ spμ₂ hip)

    mergeS-sym Scp              (Scns _ _)   hip = refl
    mergeS-sym Scp              (Schg _ _ _)   hip = refl
    mergeS-sym Scp               Scp hip = refl
    mergeS-sym (Scns _ _)        Scp hip = refl
    mergeS-sym (Schg _ _ _)      Scp hip = refl
    mergeS-sym {σ} (Scns C₁ at₁)    (Scns C₂ at₂) (refl , hip) 
      = cong (Scns C₁) (mergeAts-sym at₁ at₂ hip)
    mergeS-sym (Scns C₁ at₁)    (Schg C₂ C₃ {q} al₂) (refl , hip)
      = cong (Schg C₁ C₃ {q}) refl
    mergeS-sym (Schg C₁ C₂ {q} al₁) (Scns C₃ at₂) (refl , hip)
      = cong (Schg C₁ C₂ {q}) refl
    mergeS-sym (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂) ()
-}
