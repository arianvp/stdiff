open import Prelude
open import Generic.Regular

module Regular.Internal.Fixpoint (μσ : Sum) where

  open DecEq (Fix μσ) _≟Fix_
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

-- ** Universe


  mutual
    data Alμ' (s : Sum → Set) : Set where
      spn : (sp : s μσ) → Alμ' s
      ins : (C : Constr μσ)(spμ : Ctx' s (typeOf μσ C)) → Alμ' s
      del : (C : Constr μσ)(spμ : Ctx' s (typeOf μσ C)) → Alμ' s

    data Ctx' (s : Sum → Set) : Prod → Set  where
      here  : ∀{π} → (spμ : Alμ' s)(atμs : All (λ α → ⟦ α ⟧A (Fix μσ)) π) 
            → Ctx' s (I ∷ π)
      there : ∀{α π} → (atμ : ⟦ α ⟧A (Fix μσ))(alμs : Ctx' s π) → Ctx' s (α ∷ π)

    Atμ : Atom → Set
    Atμ = At Alμ

    {-# TERMINATING #-}
    Alμ : Set
    Alμ = Alμ' (S Atμ (Al Atμ))

  Ctx : Prod → Set
  Ctx = Ctx' (S Atμ (Al Atμ))

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

  matchCtx (here spμ atμs) (x ∷ p) = applyAlμ spμ x 
  matchCtx (there {α} atμ al) (at ∷ p) = matchCtx al p
  
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
