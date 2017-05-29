open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Correctness.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (_∈domRec_ : Rec → PatchRec → Set)
       (domRecExt : (x : Rec)(p : PatchRec) → x ∈domRec p → IsJust (applyRec p x))
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Domain.Functor Rec _≟Rec_ PatchRec applyRec _∈domRec_

  IsJust-map : {A B : Set}{f : A → B}{x : Maybe A}
             → IsJust x
             → IsJust (Maybe-map f x)
  IsJust-map {f = f} (indeed x) = indeed (f x)

  IsJust-magic : ∀{a}{A : Set a} → IsJust {A = A} nothing → ⊥
  IsJust-magic ()

  domS-ok : {σ : Sum}(s : ⟦ σ ⟧S Rec)(ps : Patch PatchRec σ)
          → s ∈domS ps
          → IsJust (applySAlAt applyRec ps s)

  domAl-ok : {π₁ π₂ : Prod}(p : ⟦ π₁ ⟧P Rec)(ps : Al (At PatchRec) π₁ π₂)
           → p ∈domAl ps
           → IsJust (applyAl (applyAt applyRec) ps p)

  domAt-ok : {α : Atom}(a : ⟦ α ⟧A Rec)(ps : At PatchRec α)
           → a ∈domAt ps
           → IsJust (applyAt applyRec ps a)

  domSP-ok : ∀{π}(p : ⟦ π ⟧P Rec)(ats : All (At PatchRec) π)
           → All-set (uncurry _∈domAt_) (zipd p ats)
           → IsJust (applySP (applyAt applyRec) ats p)
  domSP-ok [] [] hip = indeed []
  domSP-ok (p ∷ ps) (at ∷ ats) (h , hs)
    with domAt-ok p at h | domSP-ok ps ats hs
  ...| atok | atsok
    with applyAt applyRec at p 
  ...| nothing  = ⊥-elim (IsJust-magic atok)
  ...| just p' 
    with applySP (applyAt applyRec) ats ps
  ...| nothing  = ⊥-elim (IsJust-magic atsok)
  ...| just ps' = indeed (p' ∷ ps')

  domS-ok s  Scp hip = indeed s
  domS-ok s (Scns C ats) hip with sop s
  ...| tag Cs Ps with C ≟F Cs 
  ...| no _     = ⊥-elim hip
  ...| yes refl = IsJust-map {f = inj Cs} (domSP-ok Ps ats hip) 
  domS-ok s (Schg C₁ C₂ al) hip = {!!}  

  domAl-ok = {!!}

  domAt-ok = {!!}
