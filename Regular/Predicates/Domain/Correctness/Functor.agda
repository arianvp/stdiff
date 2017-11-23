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
  open DecEq Rec _≟Rec_

  open import Regular.Predicates.Domain.Functor Rec _≟Rec_ PatchRec applyRec _∈domRec_


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
    with IsJust-ext (domAt-ok p at h)
       | IsJust-ext (domSP-ok ps ats hs)
  ...| kat , atok | kats , atsok
    rewrite atok | atsok = indeed (kat ∷ kats)


  domS-ok s  Scp hip = indeed s
  domS-ok s (Scns C ats) hip with sop s
  ...| tag Cs Ps with C ≟F Cs 
  ...| no _     = ⊥-elim hip
  ...| yes refl = IsJust-map {f = inj Cs} (domSP-ok Ps ats hip) 
  domS-ok s (Schg C₁ C₂ al) hip with sop s
  ...| tag Cs Ps with C₁ ≟F Cs
  ...| no _     = ⊥-elim hip 
  ...| yes refl = IsJust-map {f = inj C₂} (domAl-ok Ps al hip)  

  domAl-ok []       A0           hip = indeed []
  domAl-ok []       (Ains a' al) hip = IsJust-map (domAl-ok [] al hip)
  domAl-ok (a ∷ as) (Ains a' al) hip = IsJust-map (domAl-ok (a ∷ as) al hip)
  domAl-ok (a ∷ as) (Adel {α} a' al) (refl , hip) 
    rewrite dec-refl (_≟A_ {α}) a = domAl-ok as al hip
  domAl-ok (a ∷ as) (AX   at al) (hipAt , hipAl) 
    with IsJust-ext (domAt-ok a at hipAt) 
       | IsJust-ext (domAl-ok as al hipAl)
  ...| kat , atok | kal , alok 
    rewrite atok | alok = indeed (kat ∷ kal)

  domAt-ok a (set (k₁ , k₂)) hip
    with k₁ ≟K k₂ 
  ...| yes refl = indeed a
  ...| no  _ with k₁ ≟K a
  ...| no abs = ⊥-elim (abs (sym hip))
  ...| yes _  = indeed k₂
  domAt-ok a (fix rec) hip = domRecExt a rec hip

