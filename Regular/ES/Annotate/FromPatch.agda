open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.Annotate.FromPatch (μσ : Sum) where

  open import Regular.Functor (Fix μσ) _≟Fix_
  open import Regular.Fixpoint μσ
  open import Regular.Operations.Inverse.Fixpoint μσ

  open DecEq (Fix μσ) _≟Fix_
  open FixpointApplication

  -- * General purpose 'all-copy' and 'all-move'

  ann-all : Ann → Fix μσ → Fixₐ μσ
  ann-all ann = cata (λ s → ⟨ ann , s ⟩)
  
  annAt-all : ∀{α} → Ann → ⟦ α ⟧A (Fix μσ) → ⟦ α ⟧A (Fixₐ μσ)
  annAt-all {K _} _   x = x
  annAt-all {I}   ann x = ann-all ann x

  -- * Some general lemmas about application functions;
  --   Mainly stating sufficient conditions for infering a 
  --   given application succeeds.
  --   To be moved, perhaps.

  IsJust-inCtx⇒getCtx
    : ∀{π}(δ : Ctx π)(x : Fix μσ)
    → IsJust (inCtx δ x)
    → IsJust (⟪ getCtx δ ⟫μ x)
  IsJust-inCtx⇒getCtx (here spμ rest) x hip = IsJust-unmap hip
  IsJust-inCtx⇒getCtx (there at δ) x hip = IsJust-inCtx⇒getCtx δ x (IsJust-unmap hip)

  IsJust-ins⇒getCtx
    : (C₁ : Constr μσ)(δ : Ctx (typeOf μσ C₁))(x : Fix μσ)
    → IsJust (⟪ ins C₁ δ ⟫μ x)
    → IsJust (⟪ getCtx δ ⟫μ x)
  IsJust-ins⇒getCtx C₁ δ x hip
    = IsJust-inCtx⇒getCtx δ x (IsJust-unmap hip)

  IsJust-inCtx⇒getCtx-inv
    : ∀{π}(δ : Ctx π)(x : Fix μσ)
    → IsJust (inCtx (invCtx δ) x)
    → IsJust (⟪ invAlμ (getCtx δ) ⟫μ x)
  IsJust-inCtx⇒getCtx-inv (here spμ rest) x hip = IsJust-unmap hip
  IsJust-inCtx⇒getCtx-inv (there at δ) x hip 
    = IsJust-inCtx⇒getCtx-inv δ x (IsJust-unmap hip)

  IsJust-del⇒getCtx
    : (C₁ : Constr μσ)(δ : Ctx (typeOf μσ C₁))(x : Fix μσ)
    → IsJust (⟪ invAlμ (del C₁ δ) ⟫μ x)
    → IsJust (⟪ invAlμ (getCtx δ) ⟫μ x)
  IsJust-del⇒getCtx C₁ δ x hip
    = IsJust-inCtx⇒getCtx-inv δ x (IsJust-unmap hip)

  IsJust-SP-elim
    : ∀{α π}(x : ⟦ α ⟧A (Fix μσ))(xs : ⟦ π ⟧P (Fix μσ))
    → (p : At Alμ α)(ps : All (At Alμ) π)
    → IsJust (⟪ p ∷ ps ⟫SP (x ∷ xs))
    → IsJust (⟪ p ⟫A x) × IsJust (⟪ ps ⟫SP xs)
  IsJust-SP-elim x xs p ps hip with ⟪ p ⟫A x
  ...| nothing  = ⊥-elim (IsJust-magic hip)
  ...| just px with ⟪ ps ⟫SP xs
  ...| nothing  = ⊥-elim (IsJust-magic hip)
  ...| just pxs = indeed px , indeed pxs

  IsJust-AX-elim
    : ∀{α π₁ π₂}(x : ⟦ α ⟧A (Fix μσ))(xs : ⟦ π₁ ⟧P (Fix μσ))
    → (p : At Alμ α)(ps : Al (At Alμ) π₁ π₂)
    → IsJust (⟪ AX p ps ⟫P (x ∷ xs))
    → IsJust (⟪ p ⟫A x) × IsJust (⟪ ps ⟫P xs)
  IsJust-AX-elim x xs p ps hip  with ⟪ p ⟫A x
  ...| nothing  = ⊥-elim (IsJust-magic hip)
  ...| just px with ⟪ ps ⟫P xs
  ...| nothing  = ⊥-elim (IsJust-magic hip)
  ...| just pxs = indeed px , indeed pxs


  -- * First we use a patch between a value x and y
  --   to generate annotated versions of x and y;
  --   After, we prove that extracting a patch
  --   from those, gives back the original patch.

  -- * Annotating the source; one function for each part
  --   of the universe.


  -- ** Annotating Fixpoints with Alμ's;
  {-# TERMINATING #-}
  annAlμ-src : (x : Fix μσ)(p : Alμ)
             → (hip : IsJust (⟪ p ⟫μ x))
             → Fixₐ μσ 

  -- ** Annotating Atoms
  annAt-src : ∀{α}(x : ⟦ α ⟧A (Fix μσ))(a : At Alμ α)
            → (hip : IsJust (⟪ a ⟫A x))
            → ⟦ α ⟧A (Fixₐ μσ)
  annAt-src x (set k₁₂) hip = x
  annAt-src x (fix  xi) hip = annAlμ-src x xi hip

  -- ** Annotating Lists of Atoms
  annAt*-src : ∀{π}(x : ⟦ π ⟧P (Fix μσ))(p : All (At Alμ) π)
             → (hip : IsJust (⟪ p ⟫SP x))
             → ⟦ π ⟧P (Fixₐ μσ)
  annAt*-src []       []       hip = []
  annAt*-src (x ∷ xs) (px ∷ p) hip 
    = let h₀ , h₁ = IsJust-SP-elim x xs px p hip 
       in annAt-src x px h₀ ∷ annAt*-src xs p h₁ 


  -- ** Annotating Alignments
  annAl-src : ∀{π₁ π₂}(x : ⟦ π₁ ⟧P (Fix μσ))(p : Al (At Alμ) π₁ π₂)
            → (hip : IsJust (⟪ p ⟫P x))
            → ⟦ π₁ ⟧P (Fixₐ μσ)
  annAl-src x A0                 hip = []
  annAl-src xs       (Ains at p) hip 
    = annAl-src xs p (IsJust-unmap hip)
  annAl-src (x ∷ xs) (Adel {α} at p) hip 
    = annAt-all {α} M x ∷ annAl-src xs p hip 
  annAl-src (x ∷ xs) (AX   ax p) hip
    = let h₀ , h₁ = IsJust-AX-elim x xs ax p hip 
       in annAt-src x ax h₀ ∷ annAl-src xs p h₁ 

  -- ** Annotating Sums with spines;
  annS-src : ∀{σ}(x : ⟦ σ ⟧S (Fix μσ))(s : Patch Alμ σ)
           → (hip : IsJust (⟪ s ⟫S x))
           → ⟦ σ ⟧S (Fixₐ μσ) 
  annS-src x Scp hip = fmapS (ann-all C) x
  annS-src x (Scns C₁ ats) hip with sop x
  ...| tag Cₓ Pₓ with C₁ ≟F Cₓ
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = inj Cₓ (annAt*-src Pₓ ats (IsJust-unmap hip))
  annS-src x (Schg C₁ C₂ al) hip with sop x
  ...| tag Cₓ Pₓ with C₁ ≟F Cₓ
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = inj Cₓ (annAl-src Pₓ al (IsJust-unmap hip))

  -- ** Annotating Products with Contexts
  annP-src : ∀{π}(x : ⟦ π ⟧P (Fix μσ))(δ : Ctx π)
           → (hip : IsJust (matchCtx δ x))
           → ⟦ π ⟧P (Fixₐ μσ)
  annP-src {I ∷ π} (x ∷ xs) (here spμ atμs) hip 
    = annAlμ-src x spμ hip ∷ All-map (λ {α} → annAt-all {α} M) xs
  annP-src {α ∷ π} (x ∷ xs) (there atμ δ) hip 
    = annAt-all {α} M x ∷ annP-src xs δ hip 

  -- ** Actual definition, closing the mutual recursion.
  annAlμ-src ⟨ x ⟩ (spn sp) hip     
    = ⟨ C , annS-src x sp (IsJust-unmap hip) ⟩
  annAlμ-src ⟨ x ⟩ (ins C₁ spμ) hip 
    = annAlμ-src ⟨ x ⟩ (getCtx spμ) (IsJust-ins⇒getCtx C₁ spμ ⟨ x ⟩ hip)
  annAlμ-src ⟨ x ⟩ (del C₁ spμ) hip with sop x
  ...| tag Cₓ Pₓ with C₁ ≟F Cₓ 
  ...| no  abs  = ⊥-elim (IsJust-magic hip)
  ...| yes refl = ⟨ M , inj Cₓ (annP-src Pₓ spμ hip) ⟩
  
  -- ** Annotating Fixpoints with Alμ's;
  {-# TERMINATING #-}
  annAlμ-dst : (x : Fix μσ)(p : Alμ)
             → (hip : IsJust (⟪ invAlμ p ⟫μ x))
             → Fixₐ μσ 

  -- ** Annotating Atoms
  annAt-dst : ∀{α}(x : ⟦ α ⟧A (Fix μσ))(a : At Alμ α)
            → (hip : IsJust (⟪ invAt a ⟫A x))
            → ⟦ α ⟧A (Fixₐ μσ)
  annAt-dst x (set k₁₂) hip = x
  annAt-dst x (fix  xi) hip = annAlμ-dst x xi hip

  -- ** Annotating Lists of Atoms
  annAt*-dst : ∀{π}(x : ⟦ π ⟧P (Fix μσ))(p : All (At Alμ) π)
             → (hip : IsJust (⟪ All-map invAt p ⟫SP x))
             → ⟦ π ⟧P (Fixₐ μσ)
  annAt*-dst []       []       hip = []
  annAt*-dst (x ∷ xs) (px ∷ p) hip 
    = let h₀ , h₁ = IsJust-SP-elim x xs (invAt px) (All-map invAt p) hip 
       in annAt-dst x px h₀ ∷ annAt*-dst xs p h₁ 


  -- ** Annotating Alignments
  annAl-dst : ∀{π₁ π₂}(x : ⟦ π₂ ⟧P (Fix μσ))(p : Al (At Alμ) π₁ π₂)
            → (hip : IsJust (⟪ invAl p ⟫P x))
            → ⟦ π₂ ⟧P (Fixₐ μσ)
  annAl-dst x A0                 hip = []
  annAl-dst xs       (Adel at p) hip 
    = annAl-dst xs p (IsJust-unmap hip)
  annAl-dst (x ∷ xs) (Ains {α} at p) hip 
    = annAt-all {α} M x ∷ annAl-dst xs p hip
  annAl-dst (x ∷ xs) (AX   ax p) hip 
    = let h₀ , h₁ = IsJust-AX-elim x xs (invAt ax) (invAl p) hip
       in annAt-dst x ax h₀ ∷ annAl-dst xs p h₁

  -- ** Annotating Sums with spines;
  annS-dst : ∀{σ}(x : ⟦ σ ⟧S (Fix μσ))(s : Patch Alμ σ)
           → (hip : IsJust (⟪ invS s ⟫S x))
           → ⟦ σ ⟧S (Fixₐ μσ) 
  annS-dst x Scp hip = fmapS (ann-all C) x
  annS-dst x (Scns C₁ ats) hip with sop x
  ...| tag Cₓ Pₓ with C₁ ≟F Cₓ
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = inj Cₓ (annAt*-dst Pₓ ats (IsJust-unmap hip))
  annS-dst x (Schg C₁ C₂ al) hip with sop x
  ...| tag Cₓ Pₓ with C₂ ≟F Cₓ
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = inj Cₓ (annAl-dst Pₓ al (IsJust-unmap hip))

  -- ** Annotating Products with Contexts
  annP-dst : ∀{π}(x : ⟦ π ⟧P (Fix μσ))(δ : Ctx π)
           → (hip : IsJust (matchCtx (invCtx δ) x))
           → ⟦ π ⟧P (Fixₐ μσ)
  annP-dst {I ∷ π} (x ∷ xs) (here spμ atμs) hip 
    = annAlμ-dst x spμ hip ∷ All-map (λ {α} → annAt-all {α} M) xs
  annP-dst {α ∷ π} (x ∷ xs) (there atμ δ) hip 
    = annAt-all {α} M x ∷ annP-dst xs δ hip 

  -- ** Actual definition, closing the mutual recursion.
  annAlμ-dst ⟨ x ⟩ (spn sp) hip     
    = ⟨ C , annS-dst x sp (IsJust-unmap hip) ⟩
  annAlμ-dst ⟨ x ⟩ (ins C₁ spμ) hip with sop x
  ...| tag Cₓ Pₓ with C₁ ≟F Cₓ
  ...| no _     = ⊥-elim (IsJust-magic hip)
  ...| yes refl = ⟨ M , inj Cₓ (annP-dst Pₓ spμ hip) ⟩
  annAlμ-dst ⟨ x ⟩ (del C₁ spμ) hip 
    = annAlμ-dst ⟨ x ⟩ (getCtx spμ) (IsJust-del⇒getCtx C₁ spμ ⟨ x ⟩ hip)
