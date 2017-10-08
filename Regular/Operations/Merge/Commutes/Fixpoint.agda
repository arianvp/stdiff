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


  -- * Auxiliary functions on the Maybe monad;
  maybe-nothing-nothing≡nothing
    : ∀{a b}{A : Set a}{B : Set b}(x : Maybe A)
    → maybe {B = const (Maybe B)} (const nothing) nothing x ≡ nothing
  maybe-nothing-nothing≡nothing nothing = refl
  maybe-nothing-nothing≡nothing (just _) = refl

  maybe-just-nothing≡id
    : ∀{a}{A : Set a}(x : Maybe A)
    → maybe just nothing x ≡ x
  maybe-just-nothing≡id nothing  = refl
  maybe-just-nothing≡id (just x) = refl
  

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

  -- * Auxiliary commutation lemmas;
  --
  --    Merging a Alμ into a Ctx commutes.
  --
  mergeAlμCtx-commute
    : ∀{π}(alμ : Alμ)(ctx : Ctx π)
    → (hip : disjAlμ alμ (getCtx ctx))
    → ∀ x → (inCtx (mergeAlμCtx alμ ctx hip) ∙ ⟪ alμ ⟫μ) x
          ≡ (⟪ mergeCtxAlμ ctx alμ (disjAlμ-sym alμ (getCtx ctx) hip) ⟫SP ∙ inCtx ctx) x
  mergeAlμCtx-commute {π} alμ (here alμ' rest) hip x
    rewrite maybe-kleisli-lift {C = ⟦ π ⟧P (Fix μσ)} { g = λ k → just (k ∷ rest) }
               {f  = applyAlμ (mergeAlμ alμ alμ' hip)}
               {f' = applyAlμ (mergeAlμ alμ' alμ (disjAlμ-sym alμ alμ' hip))}
               (applyAlμ alμ x)
               (applyAlμ alμ' x)
               (mergeAlμ-commute alμ alμ' hip x)
    with applyAlμ alμ' x
  ...| nothing = refl
  ...| just x' 
    rewrite makeidAllAt-uni rest rest
    with ⟪ mergeAlμ alμ' alμ (disjAlμ-sym alμ alμ' hip) ⟫μ x'
  ...| nothing = refl
  ...| just x'' = refl
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

  -- And vice-versa;
  mergeCtxAlμ-commute
    : ∀{π}(ctx : Ctx π)(alμ : Alμ)
    → (hip : disjAlμ (getCtx ctx) alμ)
    → ∀ x → (⟪ mergeCtxAlμ ctx alμ hip ⟫SP ∙ inCtx ctx) x
          ≡ (inCtx (mergeAlμCtx alμ ctx (disjAlμ-sym (getCtx ctx) alμ hip)) ∙ ⟪ alμ ⟫μ) x
  mergeCtxAlμ-commute ctx alμ hip x
    rewrite mergeAlμCtx-commute alμ ctx (disjAlμ-sym (getCtx ctx) alμ hip) x
          | disjAlμ-sym-inv (getCtx ctx) alμ hip
          = refl

  -- * Merging Ats and Ctx also commutes!
  mergeAtCtx-commute
    : ∀{π}(atμs : All Atμ π)(ctx : Ctx π)
    → (hip : disjAtCtx atμs ctx)
    → ∀ x → (matchCtx (mergeAtCtx atμs ctx hip) ∙ ⟪ atμs ⟫SP) x
          ≡ (⟪ mergeCtxAt ctx atμs (disjAtCtx-sym atμs ctx hip) ⟫μ ∙ matchCtx ctx) x
  mergeAtCtx-commute = {!!}

  mergeCtxAt-commute
    : ∀{π}(ctx : Ctx π)(atμs : All Atμ π)
    → (hip : disjCtxAt ctx atμs)
    → ∀ x → (⟪ mergeCtxAt ctx atμs hip ⟫μ ∙ matchCtx ctx) x
          ≡ (matchCtx (mergeAtCtx atμs ctx (disjCtxAt-sym ctx atμs hip)) ∙ ⟪ atμs ⟫SP) x
  mergeCtxAt-commute ctx atμs hip x
    rewrite mergeAtCtx-commute atμs ctx (disjCtxAt-sym ctx atμs hip) x
          | disjAtCtx-sym-inv atμs ctx hip
          = refl

{-
    → ∀ x → (inCtx (mergeAtCtx atμs ctx hip) ∙ ⟪ selectA atμs ctx ⟫μ) x
          ≡ (inCtx (mergeCtxAt ctx  atμs (disjAtCtx-sym atμs ctx hip)) ∙ ⟪ getCtx ctx ⟫μ) x
-}
{-
  mergeAtCtx-commute (fix atμ ∷ atμs) (here spμ rest) (h , hip) x
    = maybe-kleisli-lift {g = λ x → just (x ∷ rest)} 
                   {f  = applyAlμ (mergeAlμ atμ spμ h)} 
                   {f' = applyAlμ (mergeAlμ spμ atμ (disjAlμ-sym atμ spμ h))} 
                   (applyAlμ atμ x) (applyAlμ spμ x) 
                   (mergeAlμ-commute atμ spμ h x)
  mergeAtCtx-commute (fix atμ ∷ atμs) (there atμ' ctx) (h , hip) x 
    = maybe-kleisli-lift {g = λ x → just (atμ' ∷ x)} 
                   {f  = inCtx (mergeAtCtx atμs ctx hip)} 
                   {f' = inCtx (mergeCtxAt ctx atμs (disjAtCtx-sym atμs ctx hip))} 
                   (applyAlμ (selectA atμs ctx) x) 
                   (applyAlμ (getCtx ctx) x) 
                   (mergeAtCtx-commute atμs ctx hip x)
  mergeAtCtx-commute (set atμ ∷ atμs) (there atμ' ctx) (h , hip) x
    = maybe-kleisli-lift {g = λ x → just (atμ' ∷ x)} 
                   {f  = inCtx (mergeAtCtx atμs ctx hip)} 
                   {f' = inCtx (mergeCtxAt ctx atμs (disjAtCtx-sym atμs ctx hip))} 
                   (applyAlμ (selectA atμs ctx) x) 
                   (applyAlμ (getCtx ctx) x) 
                   (mergeAtCtx-commute atμs ctx hip x)
-}

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
    rewrite maybe-kleisli-lift 
              {g  = λ k → just ⟨ inj C₁ k ⟩}
              {f  = inCtx (mergeAlμCtx (del C₂ s₂) s₁ (disjAlμ-sym (getCtx s₁) (del C₂ s₂) hip)) }
              {f' = ⟪ mergeCtxAlμ s₁ (del C₂ s₂)
                      (disjAlμ-sym (del C₂ s₂) (getCtx s₁)
                       (disjAlμ-sym (getCtx s₁) (del C₂ s₂) hip)) ⟫SP }
              ( ⟪ del C₂ s₂ ⟫μ x )
              (inCtx s₁ x)
              (mergeAlμCtx-commute (del C₂ s₂) s₁ 
                (disjAlμ-sym (getCtx s₁) (del C₂ s₂) hip) x)
    with inCtx s₁ x
  ...| nothing = refl
  ...| just x' 
    rewrite sop-inj-lemma {μσ} C₁ x'
    with C₁ ≟F C₁
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl 
    rewrite disjAlμ-sym-inv (getCtx s₁) (del C₂ s₂) hip
    with ⟪ mergeCtxAlμ s₁ (del C₂ s₂) hip ⟫SP x'
  ...| nothing  = refl
  ...| just x'' = refl
  mergeAlμ-commute (spn s₁)   (ins C₂ s₂)  hip x 
    rewrite maybe-kleisli-lift { g = λ k → just ⟨ inj C₂ k ⟩ }
              { f  = inCtx (mergeAlμCtx (spn s₁) s₂ hip) }
              { f' = ⟪ mergeCtxAlμ s₂ (spn s₁) (disjAlμ-sym (spn s₁) (getCtx s₂) hip) ⟫SP }
              ( ⟪ spn s₁ ⟫μ x )
              (inCtx s₂ x)
              (mergeAlμCtx-commute (spn s₁) s₂ hip x)
    with inCtx s₂ x
  ...| nothing = refl
  ...| just x' 
    rewrite sop-inj-lemma {μσ} C₂ x'
    with C₂ ≟F C₂
  ...| no abs = ⊥-elim (abs refl)
  ...| yes refl 
    with ⟪ mergeCtxAlμ s₂ (spn s₁) (disjAlμ-sym (spn s₁) (getCtx s₂) hip) ⟫SP x'
  ...| nothing = refl
  ...| just x'' = refl
  mergeAlμ-commute (del C₁ s₁) (ins C₂ s₂)  hip x 
    rewrite maybe-kleisli-lift { g = λ k → just ⟨ inj C₂ k ⟩ }
              { f  = inCtx (mergeAlμCtx (del C₁ s₁) s₂ hip) }
              { f' = ⟪ mergeCtxAlμ s₂ (del C₁ s₁) (disjAlμ-sym (del C₁ s₁) (getCtx s₂) hip) ⟫SP }
              ( ⟪ del C₁ s₁ ⟫μ x )
              (inCtx s₂ x)
              (mergeAlμCtx-commute (del C₁ s₁) s₂ hip x)
    with inCtx s₂ x
  ...| nothing = refl
  ...| just x' 
    rewrite sop-inj-lemma {μσ} C₂ x'
    with C₂ ≟F C₂
  ...| no abs = ⊥-elim (abs refl)
  ...| yes refl 
    with ⟪ mergeCtxAlμ s₂ (del C₁ s₁) (disjAlμ-sym (del C₁ s₁) (getCtx s₂) hip) ⟫SP x'
  ...| nothing = refl
  ...| just x'' = refl

  mergeAlμ-commute (spn Scp) (del C₂ s₂)   hip ⟨ x ⟩ 
    with sop x
  ...| tag Cx Dx
    with C₂ ≟F Cx
  ...| no abs = refl
  ...| yes refl 
    with matchCtx s₂ Dx
  ...| nothing  = refl
  ...| just dx' = cong just (sym (fix-unfix-lemma dx'))
  mergeAlμ-commute (spn (Scns C₁ at₁))  (del C₂ s₂) (refl , hip) ⟨ x ⟩
    with sop x
  ...| tag Cx Dx
    with C₁ ≟F Cx
  ...| no _ = refl
  ...| yes refl 
    rewrite sym (mergeAtCtx-commute at₁ s₂ hip Dx)
    with ⟪ at₁ ⟫SP Dx
  ...| nothing  = refl
  ...| just Dx' 
    rewrite sop-inj-lemma {μσ} Cx Dx' 
    with Cx ≟F Cx
  ...| no abs = ⊥-elim (abs refl)
  ...| yes refl with matchCtx (mergeAtCtx at₁ s₂ hip) Dx' 
  ...| nothing = refl
  ...| just Dx'' = refl
  mergeAlμ-commute (spn (Schg _ _ _)) (del C₂ s₂) ()
  mergeAlμ-commute (del C₁ s₁) (spn Scp)   hip ⟨ x ⟩
    with sop x
  ...| tag Cx Dx
    with C₁ ≟F Cx
  ...| no abs = refl
  ...| yes refl 
    with matchCtx s₁ Dx
  ...| nothing  = refl
  ...| just dx' = cong just (fix-unfix-lemma dx')
  mergeAlμ-commute (del C₁ s₁) (spn (Scns C₂ at₂)) (refl , hip) ⟨ x ⟩
    with sop x
  ...| tag Cx Dx
    with C₁ ≟F Cx
  ...| no _ = refl
  ...| yes refl 
    rewrite mergeCtxAt-commute s₁ at₂ hip Dx
    with ⟪ at₂ ⟫SP Dx
  ...| nothing  = refl
  ...| just Dx' 
    rewrite sop-inj-lemma {μσ} Cx Dx' 
    with Cx ≟F Cx
  ...| no abs = ⊥-elim (abs refl)
  ...| yes refl with matchCtx (mergeAtCtx at₂ s₁ (disjCtxAt-sym s₁ at₂ hip)) Dx'
  ...| nothing = refl
  ...| just Dx'' = refl
  mergeAlμ-commute (del C₁ s₁) (spn (Schg _ _ _)) ()
  mergeAlμ-commute (del C₁ s₁) (del C₂ s₂) ()

  mergeAlμ-commute (spn s₁) (spn s₂)       hip ⟨ x ⟩ 
    rewrite ⟪⟫-spn-spn-fusion (mergeS s₁ s₂ hip) s₁ ⟨ x ⟩
          | mergeS-commute s₁ s₂ hip x
    with ⟪ s₂ ⟫S x
  ...| nothing = {!!}
  ...| just x' = {!!}
