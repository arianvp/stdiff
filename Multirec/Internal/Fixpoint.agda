open import Prelude
open import Generic.Multirec

module Multirec.Internal.Fixpoint {n : ℕ}(φ : Fam n) where

  open DecEq (Fix φ) _≟Fix_
  open import Multirec.Internal.Functor (Fix φ) _≟Fix_
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

  data Alμ : Fin n → Fin n → Set

  Alμᵒ : Fin n → Fin n → Set
  Alμᵒ ν₂ ν₁ = Alμ ν₁ ν₂

  Alμ↓ : Fin n → Set
  Alμ↓ ν = Alμ ν ν

  data Ctx (P : Fin n → Set) : Prod n → Set where
    here  : ∀{ν π}(spμ : P ν)(atμs : All (λ α → ⟦ α ⟧A (Fix φ)) π) 
          → Ctx P (I ν ∷ π)
    there : ∀{α π}(atμ : ⟦ α ⟧A (Fix φ))(alμs : Ctx P π) 
          → Ctx P (α ∷ π)

  data Alμ where
    spn : ∀{ν}(sp : Patch Alμ↓ (⟦ φ ⟧F ν)) → Alμ ν ν
    ins : ∀{ν₁ ν₂}(C : Constr' φ ν₂)
                  (δ : Ctx (Alμ ν₁) (typeOf' φ ν₂ C)) → Alμ ν₁ ν₂
    del : ∀{ν₁ ν₂}(C : Constr' φ ν₁)
                  (δ : Ctx (Alμᵒ ν₂) (typeOf' φ ν₁ C)) → Alμ ν₁ ν₂

-- ** Interpretation

  {-# TERMINATING #-}
  applyAlμ : ∀{ν₁ ν₂} → Alμ ν₁ ν₂ → Fix φ ν₁ → Maybe (Fix φ ν₂)
  insCtx : ∀{π ν} → Ctx (Alμ ν) π → Fix φ ν → Maybe (⟦ π ⟧P (Fix φ))
  delCtx : ∀{π ν} → Ctx (Alμᵒ ν) π → ⟦ π ⟧P (Fix φ) → Maybe (Fix φ ν)

  applyAlμ (spn sp) x 
    = Maybe-map ⟨_⟩ (applyPatch applyAlμ sp (unfix x))
  applyAlμ (ins C δ) x 
    = Maybe-map (⟨_⟩ ∘ inj C) (insCtx δ x)
  applyAlμ (del C δ) x 
    = (delCtx δ ∙ match C) (unfix x)
  
  insCtx (here spμ atμs) x = Maybe-map (_∷ atμs) (applyAlμ spμ x)
  insCtx (there atμ δ)   x = Maybe-map (atμ ∷_) (insCtx δ x)

  delCtx (here spμ atμs) (x ∷ xs) = applyAlμ spμ x
  delCtx (there atμ δ) (x ∷ xs) = delCtx δ xs

-- ** Cost semantics

  {-# TERMINATING #-}
  costAlμ : ∀{ν₁ ν₂} → Alμ ν₁ ν₂ → ℕ
  costCtx : ∀{π P}(costP : ∀{ν} → P ν → ℕ) → Ctx P π → ℕ 

  costAlμ (spn sp) = costS (costAt costAlμ) (costAl (costAt costAlμ)) sp
  costAlμ (ins C δ) = costCtx costAlμ δ 
  costAlμ (del C δ) = costCtx costAlμ δ

  costCtx {π} f (here spμ rest) = f spμ + length π 
  costCtx     f (there _ δ)     = 1 + costCtx f δ
