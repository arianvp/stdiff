open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.Annotate.Soundness (μσ : Sum) where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ
  open import Regular.Predicates.Applies.Fixpoint μσ
  --   open import Regular.Predicates.Normal.Fixpoint μσ

  open import Regular.ES.Annotate.FromPatch μσ
  open import Regular.ES.Annotate.Enum μσ

  open DecEq (Fix μσ) _≟Fix_
  open AnnCounter

  -- * We will invariantly need to prove that stiff is sound;
  --   This will require soundness from the annotation functions, that is:
  --
  --      (hip : AppAlμ x y p) → fmap 𝓤 (annAlμ-src hip) ≡ x
  --
  --



  if-has-copies-elim
    : ∀{a b}{A : Set a}{P : A → Set b}(z : ⟦ μσ ⟧S (Fixₐ μσ))
    → {hascpy : 1 ≤ count-CS z → A}
    → {nocpy  : 0 ≡ count-CS z → A}
    → (hascpyP : (hip : 1 ≤ count-CS z) → P (hascpy hip))
    → (nocpyP  : (hip : 0 ≡ count-CS z) → P (nocpy hip))
    → P (if-has-copies z hascpy nocpy)
  if-has-copies-elim z hascpyP nocpyP 
    with count-CS z | inspect count-CS z
  ...| zero   | [ CZ ] = nocpyP refl
  ...| suc cz | [ CZ ] = hascpyP (s≤s z≤n)

  sound : {x y : Fix μσ}{p : Alμ}
        → (hip : AppAlμ x y p)
        → AppAlμ x y (diffAlμ (annAlμ-src hip) (annAlμ-dst hip))

  sound-CtxDelMax
    : ∀{α π}{Pxs : ⟦ α ∷ π ⟧P (Fix μσ)}{y : Fix μσ}
    → (z : Fixₐ μσ)
    → (δ' : ⟦ α ∷ π ⟧P (Fixₐ μσ))
    → (δᵢ  : Fin (length (α ∷ π)))
    → (1≤ca : let α₀ , a₀ = all-lookup δᵢ δ'
               in 1 ≤ count-CA {μσ} {α₀} a₀ )
    → AppCtxDel Pxs y (diffCtxMax CtxDel z δ' δᵢ 1≤ca)
  sound-CtxDelMax {K _} z (at ∷ ats) zero ()
  sound-CtxDelMax {I}  {Pxs = px ∷ pxs} {y} z (at ∷ ats) zero 1≤ca 
     = AppDelHere px y {!!} pxs (All-map (λ {α} → fmapA {α} 𝓤) ats) (sound {!!})
  sound-CtxDelMax {α} z δ' δᵢ 1≤ca = {!!}

  sound-CtxDel-Here-lemma
    : ∀{π}{x y : Fix μσ}{spμ : Alμ}{pxs pxs' : ⟦ π ⟧P (Fix μσ)}
    → (hip : AppAlμ x y spμ)
    → vec-max (count-C* (annP-src (AppDelHere x y spμ pxs pxs' hip))) 
    ≡ zero
  sound-CtxDel-Here-lemma = {!!}

  sound-CtxDelMaxHere
    : ∀{π}{x y : Fix μσ}{z : Fixₐ μσ}{spμ : Alμ}{xs xs' : ⟦ π ⟧P (Fix μσ)}
    → (hip  : AppAlμ x y spμ)
    -- → (1≤ca : 1 ≤ count-CA {μσ} {I} (annAlμ-src hip))
    → diffCtx CtxDel z (annP-src (AppDelHere x y spμ xs xs' hip)) {!!}
    ≡ here {!!} xs
{-
    → AppCtxDel (x ∷ xs) y 
                (diffCtxMax CtxDel z (annP-src (AppDelHere x y spμ xs xs' hip)) zero 1≤ca)
-}
  sound-CtxDelMaxHere = {!!}

  sound-CtxDel
    : ∀{π}{Pxs : ⟦ π ⟧P (Fix μσ)}{y : Fix μσ}{z : Fixₐ μσ}{δ : Ctx π}
    → (hip : AppCtxDel Pxs y δ)
    → (hipz : annAlμ-dst (proj₂ (AppCtxDel⇒AppAlμ hip)) ≡ z )
    → (1≤cx : 1 ≤ count-C*-sum (annP-src hip))
    → AppCtxDel Pxs y (diffCtx CtxDel z (annP-src hip) 1≤cx)
  sound-CtxDel {[]}    ()
  sound-CtxDel {α ∷ π} {z} (AppDelHere x y spμ pxs pxs' hip) hipz 1≤cx
    = {!!}

{-
    rewrite sound-CtxDelMaxHere {x = x} {y} {z} {spμ} {pxs} {pxs'} hip
    = {! sound-CtxDelMaxHere !}
-}
{-
    rewrite sound-CtxDel-Here-lemma {π = π} {x = x} {y} {pxs = pxs} {pxs'} hip 
          = {!!}
-}
  sound-CtxDel {α ∷ π} {z} (AppDelThere x x' y pxs δ hip) hipz 1≤cx 
    = {!!}
{-
    with annP-src hip | inspect annP-src hip
  ...| r ∷ rs | [ R ] 
     -- Annotating anything with the ctx δ, will give 0 copies everywhere
     -- but in the 'here' constructor of the context.
     = sound-CtxDelMax {!!} (r ∷ rs) 
         (vec-max (count-C* {π = α ∷ π} (r ∷ rs))) 
         (count-maxCS-CA-lemma {μσ} {π} {α} r rs 1≤cx)
-}
{-
  sound-CtxDel (AppDelHere x y spμ pxs pxs' hip) hipz 1≤cx 
    = {!AppDelHere!}
  sound-CtxDel (AppDelThere x x' y pys δ hip) hipz 1≤cx = {!!}
-}

  sound-del 
    : (C₁ : Constr μσ){Pxs : ⟦ typeOf μσ C₁ ⟧P (Fix μσ)}{y : Fix μσ}
    → {δ : Ctx (typeOf μσ C₁)}
    → (hip : AppCtxDel Pxs y δ)
    → (z : Fixₐ μσ)
    → (hipz : annAlμ-dst (proj₂ (AppCtxDel⇒AppAlμ hip)) ≡ z )
    → (1≤cx : 1 ≤ count-CS {μσ} (inj C₁ (annP-src hip)))
    → AppAlμ ⟨ inj C₁ Pxs ⟩ y (diff-del (inj C₁ (annP-src hip)) z 1≤cx)
  sound-del C₁ {Pxs} {y} {δ} hip z hipz 1≤cx 
    rewrite sop-inj-lemma {μσ} C₁ (annP-src hip) 
      =  AppDel C₁ Pxs y (diffCtx CtxDel z (annP-src hip) 
            (subst (_≤_ 1) (count-CS≡C*-lemma {μσ} C₁ (annP-src hip)) 1≤cx)) 
            (sound-CtxDel hip hipz 
              (subst (_≤_ 1) (count-CS≡C*-lemma {μσ} C₁ (annP-src hip)) 1≤cx)) 

  sound (AppDel C₁ Pxs y δ hip) 
    with annAlμ-dst (proj₂ (AppCtxDel⇒AppAlμ hip)) 
       | inspect annAlμ-dst (proj₂ (AppCtxDel⇒AppAlμ hip))
  ...| ⟨ M , z' ⟩ | [ HIPZ ]
     = if-has-copies-elim 
         {P = AppAlμ ⟨ inj C₁ Pxs ⟩ y}
         (inj C₁ (annP-src hip)) 
         (λ 1≤cx → sound-del C₁ hip ⟨ M , z' ⟩ HIPZ 1≤cx)
         (λ 0≡cx → {!!})
  ...| ⟨ C , z' ⟩ | [ z'≡annz ] = {!!}
  sound (AppIns x C₁ Pys δ hip) = {!!}
  sound (AppSpn x y s hip) = {!!}
{-
  sound-I : {x y : Fix μσ}{p : Alμ}
          → (np  : normAlμ-I p)
          → (hip : AppAlμ x y p)
          → diffAlμ (annAlμ-src hip) (annAlμ-dst hip) ≡ p

  sound-M : {x y : Fix μσ}{p : Alμ}
          → (np  : normAlμ-M p)
          → (hip : AppAlμ x y p)
          → diffAlμ (annAlμ-src hip) (annAlμ-dst hip) ≡ p


  sound-D p (AppDel C₁ Pxs y δ hip) = {!!}
  sound-D p (AppIns x C₁ Pys δ hip) = {!!}
  sound-D () (AppSpn x y s hip)

  sound-I p (AppIns x C₁ Pys δ hip) = {!!}
  sound-I p (AppSpn x y s hip)     = {!!}
  sound-I () (AppDel C₁ Pxs y δ hip) 

  sound-M p (AppSpn x y s hip) = cong spn {!!}
  sound-M () (AppIns x C₁ Pys δ hip) 
  sound-M () (AppDel C₁ Pxs y δ hip) 
-}



  -- Here, we'll need to look at the patch;
  -- if it has no copies, it really is the 'stiff-diff' of
  -- x and y, if it has a copy, the proof goes by induction.
  --
  -- Now, obviously, everything happen modulo 'normal' patch.
  -- We could use some insight on that.
