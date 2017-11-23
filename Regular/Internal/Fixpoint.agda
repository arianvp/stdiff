open import Prelude
open import Generic.Regular

module Regular.Internal.Fixpoint (μσ : Sum) where

  open DecEq (Fix μσ) _≟Fix_
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

-- ** Universe

  data Alμ : Set
  data Ctx : Prod → Set
  Atμ : Atom → Set

  data Alμ where
    spn : (sp : S Atμ (Al Atμ) μσ) → Alμ
    ins : (C : Constr μσ)(spμ : Ctx (typeOf μσ C)) → Alμ
    del : (C : Constr μσ)(spμ : Ctx (typeOf μσ C)) → Alμ

  data Ctx where
    here  : ∀{π} → (spμ : Alμ)(atμs : All (λ α → ⟦ α ⟧A (Fix μσ)) π) → Ctx (I ∷ π)
    there : ∀{α π} → (atμ : ⟦ α ⟧A (Fix μσ))(alμs : Ctx π) → Ctx (α ∷ π)

  Atμ = At Alμ

  getCtx : ∀{π} → Ctx π → Alμ
  getCtx (there _ ctx) = getCtx ctx
  getCtx (here res _)  = res

  selectP : ∀{π} → ⟦ π ⟧P (Fix μσ) → Ctx π → Fix μσ
  selectP [] ()
  selectP (p ∷ ps) (here _ _)  = p
  selectP (p ∷ ps) (there _ c) = selectP ps c

  selectA : ∀{π}(atμs : All Atμ π)(ctx : Ctx π) → Alμ
  selectA [] ()
  selectA (fix x ∷ _) (here _ _) = x
  selectA (_ ∷ as) (there _ ctx) = selectA as ctx


-- ** Interpretation

  {-# TERMINATING #-}
  applyAlμ : Alμ → Fix μσ → Maybe (Fix μσ)
  inCtx : ∀ {π} → Ctx π → Fix μσ → Maybe (⟦ π ⟧P (Fix μσ))
  matchCtx : ∀ {π} → Ctx π → ⟦ π ⟧P (Fix μσ) → Maybe (Fix μσ)
  applyAtμ : ∀{α} → Atμ α → ⟦ α ⟧A (Fix μσ) → Maybe (⟦ α ⟧A (Fix μσ))

  applyAlμ (spn sp) x = Maybe-map ⟨_⟩ (applyS applyAtμ (applyAl applyAtμ) sp (unfix x))
  applyAlμ (ins C alμ) x = Maybe-map (⟨_⟩ ∘ inj C) (inCtx alμ x)
  applyAlμ (del C alμ) x = (matchCtx alμ ∙ match C) (unfix x)

  inCtx (here spμ atμs) x = Maybe-map (λ x → x ∷ atμs) (applyAlμ spμ x)
  inCtx (there atμ al) x = Maybe-map (λ ats → atμ ∷ ats) (inCtx al x)

  matchCtx (here spμ atμs) (x ∷ p) 
    = Dec-to-Maybe (atμs ≟P p) >> applyAlμ spμ x 
  matchCtx (there {α} atμ al) (at ∷ p) 
    = Dec-to-Maybe (_≟A_ {α} atμ at) >> matchCtx al p
  
  applyAtμ = applyAt applyAlμ 

-- ** Cost semantics

  {-# TERMINATING #-}
  costAlμ : Alμ → ℕ
  costAtμ : ∀{α} → Atμ α → ℕ
  costCtx : ∀{π} → Ctx π → ℕ

  costAlμ (spn sp) = costS costAtμ (costAl costAtμ) sp
  costAlμ (ins C al) = costCtx al
  costAlμ (del C al) = costCtx al

  costCtx {π} (here spμ atμs) = costAlμ spμ + length π
  costCtx     (there atμ alμ) = 1 + costCtx alμ

  costAtμ = costAt costAlμ

-- ** Aliasses

  Patchμ : Set
  Patchμ = Alμ

  applyμ : Patchμ → Fix μσ → Maybe (Fix μσ)
  applyμ = applyAlμ

  costμ : Patchμ → ℕ
  costμ = costAlμ
