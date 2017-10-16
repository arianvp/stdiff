open import Prelude
open import Generic.Regular

module Regular.Predicates.Domain.Correctness.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (_∈domRec_ : Rec → PatchRec → Set)
       (domRecExt : (x : Rec)(p : PatchRec) → x ∈domRec p → IsJust (applyRec p x))
       -- (domRecCpt : (x : Rec)(p : PatchRec) → IsJust (applyRec p x) → x ∈domRec p)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
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
  domAl-ok (a ∷ as) (Adel a' al) hip = domAl-ok as al hip
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
{-
  -- XXX: Prove compleness: IsJust (apply p x) ⇒ x ∈dom p
  -- 
  domS-cplt : {σ : Sum}(s : ⟦ σ ⟧S Rec)(ps : Patch PatchRec σ)
          → IsJust (applySAlAt applyRec ps s)
          → s ∈domS ps

  domAl-cplt : {π₁ π₂ : Prod}(p : ⟦ π₁ ⟧P Rec)(ps : Al (At PatchRec) π₁ π₂)
           → IsJust (applyAl (applyAt applyRec) ps p)
           → p ∈domAl ps

  domAt-cplt : {α : Atom}(a : ⟦ α ⟧A Rec)(ps : At PatchRec α)
           → IsJust (applyAt applyRec ps a)
           → a ∈domAt ps

  domSP-cplt : ∀{π}(p : ⟦ π ⟧P Rec)(ats : All (At PatchRec) π)
           → IsJust (applySP (applyAt applyRec) ats p)
           → All-set (uncurry _∈domAt_) (zipd p ats)
  domSP-cplt [] [] hip = unit 
  domSP-cplt (p ∷ ps) (at ∷ ats) hip
    with applyAt applyRec at p | inspect (applyAt applyRec at) p
  ...| nothing | _ = ⊥-elim (IsJust-magic hip)
  ...| just p' | [ P ]
    with applySP (applyAt applyRec) ats ps | inspect (applySP (applyAt applyRec) ats) ps
  ...| nothing  | _ = ⊥-elim (IsJust-magic hip)
  ...| just ps' | [ PS ]
      = domAt-cplt p at (subst IsJust (sym P) (indeed p')) 
      , domSP-cplt ps ats (subst IsJust (sym PS) (indeed ps'))


  domS-cplt s Scp hip = unit
  domS-cplt s (Scns C ats) hip with sop s
  ...| tag Cs Ps with C ≟F Cs 
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = domSP-cplt Ps ats (IsJust-unmap hip)
  domS-cplt s (Schg C₁ C₂ al) hip with sop s
  ...| tag Cs Ps with C₁ ≟F Cs
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = domAl-cplt Ps al (IsJust-unmap hip)

  domAl-cplt []       A0 _             = unit
  domAl-cplt []       (Ains a' al) hip = domAl-cplt [] al (IsJust-unmap hip)
  domAl-cplt (a ∷ as) (Ains a' al) hip = domAl-cplt (a ∷ as) al (IsJust-unmap hip)
  domAl-cplt (a ∷ as) (Adel a' al) hip = domAl-cplt as al hip
  domAl-cplt (a ∷ as) (AX at al) hip   
    with applyAt applyRec at a | inspect (applyAt applyRec at) a
  ...| nothing  | _ = ⊥-elim (IsJust-magic hip)
  ...| just a'  | [ A ]
    with applyAl (applyAt applyRec) al as | inspect (applyAl (applyAt applyRec) al) as 
  ...| nothing  | _ = ⊥-elim (IsJust-magic hip)
  ...| just as' | [ AS ] 
    = domAt-cplt a at (subst IsJust (sym A) (indeed a')) 
    , domAl-cplt as al (subst IsJust (sym AS) (indeed as'))

  domAt-cplt x (set (k₁ , k₂)) hip 
    with k₁ ≟K k₂
  ...| yes _ = unit
  ...| no  _ 
    with k₁ ≟K x 
  ...| yes k₁≡x = sym k₁≡x
  ...| no  _    = ⊥-elim (IsJust-magic hip)
  domAt-cplt x (fix rec) hip = domRecCpt x rec hip
-}
