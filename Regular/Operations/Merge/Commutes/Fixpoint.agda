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

  -- * We need properties from identity patches
  open IdentityProperties
  
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

  maybe-kleisli-lift
    : ∀{a b c}{A A' : Set a}{B : Set b}{C : Set c}
    → {g : B → Maybe C}{f : A → Maybe B}{f' : A' → Maybe B}(x : Maybe A)(y : Maybe A')
    → maybe {B = const (Maybe B)} f nothing x ≡ maybe f' nothing y
    → maybe {B = const (Maybe C)} (maybe g nothing ∘ f) nothing x
    ≡ maybe                       (maybe g nothing ∘ f') nothing y
  maybe-kleisli-lift nothing nothing hip   = refl
  maybe-kleisli-lift {g = g} nothing (just y) hip  = cong (maybe g nothing) hip
  maybe-kleisli-lift {g = g} (just x) nothing hip  = cong (maybe g nothing) hip
  maybe-kleisli-lift {g = g} (just x) (just y) hip = cong (maybe g nothing) hip
{-
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

-}
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
-}

  maybe-nothing-nothing≡nothing
    : ∀{a b}{A : Set a}{B : Set b}(x : Maybe A)
    → maybe {B = const (Maybe B)} (const nothing) nothing x ≡ nothing
  maybe-nothing-nothing≡nothing nothing = refl
  maybe-nothing-nothing≡nothing (just _) = refl

  mergeAlμCtx-commute
    : ∀{π}(alμ : Alμ)(ctx : Ctx π)
    → (hip : disjAlμ alμ (getCtx ctx))
    → ∀ x → (inCtx (mergeAlμCtx alμ ctx hip) ∙ ⟪ alμ ⟫μ) x
          ≡ (⟪ mergeCtxAlμ ctx alμ (disjAlμ-sym alμ (getCtx ctx) hip) ⟫SP ∙ inCtx ctx) x
  mergeAlμCtx-commute alμ (here alμ' rest) hip x
    = {!!}
  mergeAlμCtx-commute {α ∷ π} alμ (there a ctx)    hip x
    rewrite maybe-kleisli-lift {C = ⟦ α ∷ π ⟧P (Fix μσ)} { g = λ k → just (a ∷ k)}
                  {f  = inCtx (mergeAlμCtx alμ ctx hip) }
                  {f' =  ⟪ mergeCtxAlμ ctx alμ (disjAlμ-sym alμ (getCtx ctx) hip) ⟫SP}
                  (applyAlμ alμ x) 
                  (inCtx ctx x)
                  (mergeAlμCtx-commute alμ ctx hip x)
    with inCtx ctx x
  ...| nothing = refl
  ...| just x' with ⟪ mergeCtxAlμ ctx alμ (disjAlμ-sym alμ (getCtx ctx) hip) ⟫SP x'
  ...| x'' rewrite identityAtμ-uni {α} a a
     = refl


  mergeAlμ-commute (ins C₁ s₁) (ins C₂ s₂) ()
  mergeAlμ-commute (ins C₁ s₁) (spn s₂)    hip x
    rewrite maybe-kleisli-lift 
              {g  = λ k → just ⟨ inj C₁ k ⟩}
              {f  = inCtx (mergeAlμCtx (spn s₂) s₁ (disjAlμ-sym (getCtx s₁) (spn s₂) hip)) }
              {f' = ⟪ mergeCtxAlμ s₁ (spn s₂)
                      (disjAlμ-sym (spn s₂) (getCtx s₁)
                       (disjAlμ-sym (getCtx s₁) (spn s₂) hip)) ⟫SP }
              ( ⟪ spn s₂ ⟫μ x )
              (inCtx s₁ x)
              (mergeAlμCtx-commute (spn s₂) s₁ 
                (disjAlμ-sym (getCtx s₁) (spn s₂) hip) x)
    with inCtx s₁ x
  ...| nothing = refl
  ...| just x' 
    rewrite sop-inj-lemma {μσ} C₁ x'
    with C₁ ≟F C₁
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl 
    rewrite disjAlμ-sym-inv (getCtx s₁) (spn s₂) hip
    with ⟪ mergeCtxAlμ s₁ (spn s₂) hip ⟫SP x'
  ...| nothing  = refl
  ...| just x'' = refl
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
