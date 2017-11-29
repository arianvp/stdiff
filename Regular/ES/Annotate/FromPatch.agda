open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.Annotate.FromPatch (μσ : Sum) where

  open import Regular.Functor (Fix μσ) _≟Fix_
  open import Regular.Fixpoint μσ

  open import Regular.Predicates.Applies.Fixpoint μσ

  open DecEq (Fix μσ) _≟Fix_
  open FixpointApplication

  -- * General purpose 'all-copy' and 'all-move'

  ann-all : Ann → Fix μσ → Fixₐ μσ
  ann-all ann = cata (λ s → ⟨ ann , s ⟩)
  
  annAt-all : ∀{α} → Ann → ⟦ α ⟧A (Fix μσ) → ⟦ α ⟧A (Fixₐ μσ)
  annAt-all {K _} _   x = x
  annAt-all {I}   ann x = ann-all ann x

  -- * First we use a patch between a value x and y
  --   to generate annotated versions of x and y;
  --   After, we prove that extracting a patch
  --   from those, gives back the original patch.

  -- * Annotating the source; one function for each part
  --   of the universe.


  -- ** Annotating Fixpoints with Alμ's;
  {-# TERMINATING #-}
  annAlμ-src : {x y : Fix μσ}{p : Alμ}
             → AppAlμ x y p 
             → Fixₐ μσ 

  -- ** Annotating Atoms
  annAt-src : ∀{α}{x y : ⟦ α ⟧A (Fix μσ)}{p : At Alμ α}
            → AppAt x y p
            → ⟦ α ⟧A (Fixₐ μσ)
  annAt-src (AppSet k₁ k₂ q)   = k₁
  annAt-src (AppSetId k a)     = a
  annAt-src (AppFix r₁ r₂ p x) = annAlμ-src x

  -- ** Annotating Lists of Atoms
  annAt*-src : ∀{π}{x y : ⟦ π ⟧P (Fix μσ)}{p : All (At Alμ) π}
             → All-zip3-set AppAt x y p
             → ⟦ π ⟧P (Fixₐ μσ)
  annAt*-src {[]}    {[]}     {[]}     {[]}     hip 
    = []
  annAt*-src {α ∷ π} {x ∷ xs} {y ∷ ys} {p ∷ ps} (h , hip) 
    = annAt-src h ∷ annAt*-src hip

  -- ** Annotating Alignments
  annAl-src : ∀{π₁ π₂}{x : ⟦ π₁ ⟧P (Fix μσ)}{y : ⟦ π₂ ⟧P (Fix μσ)}
            → {p : Al (At Alμ) π₁ π₂}
            → AppAl x y p
            → ⟦ π₁ ⟧P (Fixₐ μσ)
  annAl-src AppA0 = []
  annAl-src (AppAX x y xs ys px pxs h hip) 
    = annAt-src h ∷ annAl-src hip
  annAl-src (AppAins y xs ys al hip) 
    = annAl-src hip
  annAl-src (AppAdel {α = α} x x' xs ys al hip) 
    = annAt-all {α} M x ∷ annAl-src hip

  -- ** Annotating Sums with spines;
  annS-src : ∀{σ}{x y : ⟦ σ ⟧S (Fix μσ)}{s : Patch Alμ σ}
           → AppS x y s
           → ⟦ σ ⟧S (Fixₐ μσ) 
  annS-src (AppScp x) 
    = fmapS (ann-all C) x
  annS-src (AppScns C₁ Pxs Pys pxy x) 
    = inj C₁ (annAt*-src x)
  annS-src (AppSchg C₁ C₂ q Pxs Pys al x) 
    = inj C₁ (annAl-src x)

  -- ** Annotating Products with Contexts
  annP-src : ∀{π}{x : ⟦ π ⟧P (Fix μσ)}{y : Fix μσ}{δ : Ctx π}
           → AppCtxDel x y δ
           → ⟦ π ⟧P (Fixₐ μσ)
  annP-src (AppDelHere x y spμ pxs pxs' h) 
    = annAlμ-src h ∷ All-map (λ {α} → annAt-all {α} M) pxs 
  annP-src (AppDelThere {α = α} x x' y pxs δ hip) 
    = annAt-all {α} M x ∷ annP-src hip

  -- ** Actual definition, closing the mutual recursion.
  annAlμ-src (AppSpn x y s h) 
    = ⟨ C , annS-src h ⟩
  annAlμ-src (AppIns x C₁ Pys δ h) 
    = annAlμ-src (proj₂ (AppCtxIns⇒AppAlμ h))
  annAlμ-src (AppDel C₁ Pxs y δ h) 
    = ⟨ M , inj C₁ (annP-src h) ⟩


  -- ** Annotating Fixpoints with Alμ's;
  {-# TERMINATING #-}
  annAlμ-dst : {x y : Fix μσ}{p : Alμ}
             → AppAlμ x y p 
             → Fixₐ μσ 

  -- ** Annotating Atoms
  annAt-dst : ∀{α}{x y : ⟦ α ⟧A (Fix μσ)}{p : At Alμ α}
            → AppAt x y p
            → ⟦ α ⟧A (Fixₐ μσ)
  annAt-dst (AppSet k₁ k₂ q)   = k₂
  annAt-dst (AppSetId k a)     = a
  annAt-dst (AppFix r₁ r₂ p x) = annAlμ-dst x

  -- ** Annotating Lists of Atoms
  annAt*-dst : ∀{π}{x y : ⟦ π ⟧P (Fix μσ)}{p : All (At Alμ) π}
             → All-zip3-set AppAt x y p
             → ⟦ π ⟧P (Fixₐ μσ)
  annAt*-dst {[]}    {[]}     {[]}     {[]}     hip 
    = []
  annAt*-dst {α ∷ π} {x ∷ xs} {y ∷ ys} {p ∷ ps} (h , hip) 
    = annAt-dst h ∷ annAt*-dst hip

  -- ** Annotating Alignments
  annAl-dst : ∀{π₁ π₂}{x : ⟦ π₁ ⟧P (Fix μσ)}{y : ⟦ π₂ ⟧P (Fix μσ)}
            → {p : Al (At Alμ) π₁ π₂}
            → AppAl x y p
            → ⟦ π₂ ⟧P (Fixₐ μσ)
  annAl-dst AppA0 = []
  annAl-dst (AppAX x y xs ys px pxs h hip) 
    = annAt-dst h ∷ annAl-dst hip
  annAl-dst (AppAdel {α = α} x x' xs ys al hip) 
    = annAl-dst hip
  annAl-dst (AppAins {α = α} y xs ys al hip) 
    = annAt-all {α} M y ∷ annAl-dst hip

  -- ** Annotating Sums with spines;
  annS-dst : ∀{σ}{x y : ⟦ σ ⟧S (Fix μσ)}{s : Patch Alμ σ}
           → AppS x y s
           → ⟦ σ ⟧S (Fixₐ μσ) 
  annS-dst (AppScp x) 
    = fmapS (ann-all C) x
  annS-dst (AppScns C₁ Pxs Pys pxy x) 
    = inj C₁ (annAt*-dst x)
  annS-dst (AppSchg C₁ C₂ q Pxs Pys al x) 
    = inj C₂ (annAl-dst x)

  -- ** Annotating Products with Contexts
  annP-dst : ∀{π}{x : Fix μσ}{y : ⟦ π ⟧P (Fix μσ)}{δ : Ctx π}
           → AppCtxIns x y δ
           → ⟦ π ⟧P (Fixₐ μσ)
  annP-dst (AppInsHere x y spμ pys h) 
    = annAlμ-dst h ∷ All-map (λ {α} → annAt-all {α} M) pys
  annP-dst (AppInsThere {α = α} x y pys δ hip) 
    = annAt-all {α} M y ∷ annP-dst hip

  -- ** Actual definition, closing the mutual recursion.
  annAlμ-dst (AppSpn x y s h) 
    = ⟨ C , annS-dst h ⟩
  annAlμ-dst (AppIns x C₁ Pys δ h) 
    = ⟨ M , inj C₁ (annP-dst h) ⟩ 
  annAlμ-dst (AppDel C₁ Pxs y δ h) 
    = annAlμ-dst (proj₂ (AppCtxDel⇒AppAlμ h))

