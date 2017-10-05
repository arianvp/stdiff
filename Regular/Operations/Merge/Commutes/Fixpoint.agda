open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Commutes.Fixpoint (μσ : Sum) where

  -- * Basic patches-over-fixpoints functionality
  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Fixpoint μσ using (module FixpointApplication)
  open FixpointApplication
  open import Regular.Predicates.Identity.Fixpoint μσ
  open import Regular.Predicates.Disjoint.Fixpoint μσ
  open import Regular.Operations.Merge.Fixpoint μσ
  
  -- * Symmetry of disjAlμ
  open DisjSymmetry
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

  -- * We need the proofs we developed for functors
  open import Regular.Operations.Merge.Commutes.Functor
                (Fix μσ) _≟Fix_ Alμ makeidAlμ identityAlμ disjAlμ disjAlμ-sym disjAlμ-sym-inv
                mergeAlμ ⟪_⟫μ

  -- *******************************************
  -- *
  -- * The final result is mergeAlμ-commute;
  -- *
  -- *
  {-# TERMINATING #-}
  mergeAlμ-commute : (alμ₁ alμ₂ : Alμ)(hip : disjAlμ alμ₁ alμ₂)
                   → ∀ x → (⟪ mergeAlμ alμ₁ alμ₂ hip ⟫μ ∙ ⟪ alμ₁ ⟫μ) x 
                         ≡ (⟪ mergeAlμ alμ₂ alμ₁ (disjAlμ-sym alμ₁ alμ₂ hip) ⟫μ ∙ ⟪ alμ₂ ⟫μ) x

  -- * which needs to be passed to our previously developed proof for functors.
  open MergeCommutesHip mergeAlμ-commute

  ⟪⟫-spn-spn-fusion
    : (s₁ s₂ : Patch Alμ μσ)
    → ∀ x → (⟪ spn s₁ ⟫μ ∙ ⟪ spn s₂ ⟫μ) x
          ≡ ((λ x → just ⟨ x ⟩) ∙ (⟪ s₁ ⟫S ∙ ⟪ s₂ ⟫S)) (unfix x)
  ⟪⟫-spn-spn-fusion s₁ s₂ ⟨ x ⟩
    with ⟪ s₂ ⟫S x | inspect ⟪ s₂ ⟫S x
  ...| nothing | [ S2 ] rewrite S2 = {!!}
  ...| just x' | [ S2 ] = {!!}

  maybe-∘-cong
    : ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
    → (g : B → Maybe C){f f' : A → Maybe B}(x y : Maybe A)
    → maybe {B = const (Maybe B)} f nothing x ≡ maybe f' nothing y
    → maybe {B = const (Maybe C)} (maybe g nothing ∘ f) nothing x
    ≡ maybe                       (maybe g nothing ∘ f') nothing y
  maybe-∘-cong g nothing nothing hip = refl
  maybe-∘-cong g nothing (just y) hip = cong (maybe g nothing) hip
  maybe-∘-cong g (just x) nothing hip = cong (maybe g nothing) hip
  maybe-∘-cong g (just x) (just y) hip = cong (maybe g nothing) hip

  mergeAtCtx-commute
    : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)
    → (hip : disjAtCtx atμs ctx)
    → ∀ x → (inCtx (mergeAtCtx atμs ctx hip) ∙ ⟪ selectA atμs ctx ⟫μ) x
          ≡ (inCtx (mergeCtxAt ctx  atμs (disjAtCtx-sym atμs ctx hip)) ∙ ⟪ getCtx ctx ⟫μ) x
  mergeAtCtx-commute (fix atμ ∷ atμs) (here spμ rest) (h , hip) x
    = maybe-∘-cong (λ x → just (x ∷ rest)) 
                   {f  = applyAlμ (mergeAlμ atμ spμ h)} 
                   {f' = applyAlμ (mergeAlμ spμ atμ (disjAlμ-sym atμ spμ h))} 
                   (applyAlμ atμ x) (applyAlμ spμ x) 
                   (mergeAlμ-commute atμ spμ h x)
  mergeAtCtx-commute (fix atμ ∷ atμs) (there atμ' ctx) (h , hip) x 
    = maybe-∘-cong (λ x → just (atμ' ∷ x)) 
                   {f  = inCtx (mergeAtCtx atμs ctx hip)} 
                   {f' = inCtx (mergeCtxAt ctx atμs (disjAtCtx-sym atμs ctx hip))} 
                   (applyAlμ (selectA atμs ctx) x) 
                   (applyAlμ (getCtx ctx) x) 
                   (mergeAtCtx-commute atμs ctx hip x)
  mergeAtCtx-commute (set atμ ∷ atμs) (there atμ' ctx) (h , hip) x
    = maybe-∘-cong (λ x → just (atμ' ∷ x)) 
                   {f  = inCtx (mergeAtCtx atμs ctx hip)} 
                   {f' = inCtx (mergeCtxAt ctx atμs (disjAtCtx-sym atμs ctx hip))} 
                   (applyAlμ (selectA atμs ctx) x) 
                   (applyAlμ (getCtx ctx) x) 
                   (mergeAtCtx-commute atμs ctx hip x)


{-
  injμ : (C : Constr μσ) → ⟦ typeOf μσ C ⟧P (Fix μσ) → Maybe (Fix μσ)
  injμ C as = just ⟨ inj C as ⟩

  ⟪⟫Scns-inj-inCtx 
    : {C : Constr μσ}(spμ : Ctx (typeOf μσ C))(ats : All Atμ (typeOf μσ C))
    → (hip : disjAtCtx ats spμ)
    → ∀ x → (⟪ spn (Scns C ats) ⟫μ ∙ injμ C ∙ inCtx spμ) x
          ≡ ( injμ C ∙ inCtx (mergeAtCtx ats spμ hip) ∙ ⟪ selectA ats spμ ⟫μ) x
  ⟪⟫Scns-inj-inCtx hip spμ ats x 
    rewrite mergeAtCtx-commute = {!!}

  -- If an insertion is disjoitn from a spine; the context is, in particular,
  -- disjoint.
  disjAlμ⇒disjAtCtx  
    : {π : Prod}(spμ : Ctx π)(s : S Atμ (Al Atμ) μσ)
    → (hip : disjAlμ (getCtx spμ) (spn s)) → disjAtCtx (mergeCtxAlμ spμ (spn s) hip) spμ
  disjAlμ⇒disjAtCtx (here  alμ' rest) s hip = {!!}
  disjAlμ⇒disjAtCtx (there a    ctx)  s hip = {!!}


  ⟪⟫Scns-inCtx-commute
    : ⟪ spn (Scns C ats) ⟫μ ∙ ((⟨_⟩ ∘ inj C) <$> inCtx ctx x)
    ≡ inCtx 
-}
  mergeAlμ-commute (ins C₁ s₁) (ins C₂ s₂) ()
  mergeAlμ-commute (ins C₁ s₁) (spn s₂)    hip x
    rewrite mergeAtCtx-commute (mergeCtxAlμ s₁ (spn s₂) hip) s₁ {!!} x
      = {!!}
  mergeAlμ-commute (ins C₁ s₁) (del C₂ s₂) hip x
    = {!!}
  mergeAlμ-commute (spn s₁)   (ins C₂ s₂)  hip x 
    = {!!}
  mergeAlμ-commute (del C s₁) (ins C₂ s₂)  hip x 
    = {!!}

  mergeAlμ-commute (spn Scp) (del C₂ s₂)   hip x 
    = {!!}
  mergeAlμ-commute (spn (Scns C₁ at₁))  (del C₂ s₂) hip x 
    = {!!}
  mergeAlμ-commute (spn (Schg _ _ _)) (del C₂ s₂) ()
  mergeAlμ-commute (del C₁ s₁) (spn Scp)   hip x
    = {!!}
  mergeAlμ-commute (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , hip) x
    = {!!}
  mergeAlμ-commute (del C₁ s₁) (spn (Schg _ _ _)) ()
  mergeAlμ-commute (del C₁ s₁) (del C₂ s₂) ()

  mergeAlμ-commute (spn s₁) (spn s₂)       hip ⟨ x ⟩ 
    rewrite ⟪⟫-spn-spn-fusion (mergeS s₁ s₂ hip) s₁ ⟨ x ⟩
          | mergeS-commute s₁ s₂ hip x
    with applyS (applyAt applyAlμ) (applyAl (applyAt applyAlμ)) s₂ x
  ...| res = {!!}
