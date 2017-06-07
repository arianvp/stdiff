open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
       (mergeRec  : (p₁ p₂ : PatchRec)(hip : disjRec p₁ p₂) → PatchRec)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor Rec _≟Rec_ PatchRec identityR
  open import Regular.Predicates.Disjoint.Functor Rec _≟Rec_ PatchRec identityR disjRec

  mergeS  : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂) → Patch PatchRec σ

  mergeAt : {α : Atom}(a₁ a₂ : At PatchRec α)(hip : disjAt a₁ a₂)
          → At PatchRec α

  mergeAtAll : ∀{l₁ l₂}(ats : All (At PatchRec) l₁)(al : Al (At PatchRec) l₁ l₂)
             → (hip : disjAtAll ats al) 
             → Al (At PatchRec) l₁ l₂ 
  mergeAtAll []       al  hip = al
  mergeAtAll (a ∷ as) (Ains at al) hip 
    = Ains at (mergeAtAll (a ∷ as) al hip)
  mergeAtAll (a ∷ as) (Adel at al) (ida , hip) 
    = Adel at (mergeAtAll as al hip)
  mergeAtAll (a ∷ as) (AX at al)   (ha , hip) 
    = AX (mergeAt a at ha) (mergeAtAll as al hip)


  mergeAts : ∀{l}(a₁ a₂ : All (At PatchRec) l)(hip : disjAts a₁ a₂) → All (At PatchRec) l
  mergeAts []         []         hip = []
  mergeAts (a₁ ∷ as₁) (a₂ ∷ as₂) (ha , hip) = mergeAt a₁ a₂ ha ∷ mergeAts as₁ as₂ hip

  mergeS Scp              s   hip = s
  mergeS s                Scp hip = s

  mergeS {σ} (Scns C₁ at₁)    (Scns C₂ at₂) (refl , hip) 
    = Scns C₁ (mergeAts at₁ at₂ hip)

  mergeS (Scns C₁ at₁)    (Schg C₂ C₃ {q} al₂) (refl , hip)
    = Schg C₁ C₃ {q} (mergeAtAll at₁ al₂ hip)

  mergeS (Schg C₁ C₂ {q} al₁) (Scns C₃ at₂) (refl , hip)
    = Schg C₁ C₂ {q} (mergeAtAll at₂ al₁ hip)

  mergeS (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂) ()

  mergeAt (set ks₁)  (set ks₂)  (inj₁ _) = set ks₂
  mergeAt (set ks₁)  (set ks₂)  (inj₂ _) = set ks₁
  mergeAt (fix spμ₁) (fix spμ₂) hip      = fix (mergeRec spμ₁ spμ₂ hip)
