open import Prelude
open import Generic.Multirec
module Multirec.Internal.Fixpoint {n : ℕ}(φ : Fam n) where
  open DecEq (Fix φ) _≟Fix_
  open import Multirec.Internal.Functor (Fix φ) _≟Fix_
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  -- Heterogenous
  data Alμ : Fin n → Fin n → Set

  Alμᵒ : Fin n → Fin n → Set
  Alμᵒ = flip Alμ
  -- Homogeneous
  Alμ↓ : Fin n → Set
  Alμ↓ ν = Alμ ν ν

  data Ctx  (P : Fin n → Set) : Prod n → Set

  InsCtx : Fin n → Prod n → Set
  InsCtx ν = Ctx (Alμ ν)

  DelCtx : Fin n → Prod n → Set
  DelCtx ν = Ctx (Alμᵒ ν)


  data Ctx (P : Fin n → Set) where
    here  : {ν : Fin n}{π : Prod n} → (P ν) → ⟦ π ⟧P (Fix φ) → Ctx P (I ν ∷ π)
    there : {α : Atom n}{π : Prod n} → ⟦ α ⟧A (Fix φ) → Ctx P π → Ctx P (α ∷ π)

  data Alμ where
    spn : ∀{ν} → Patch Alμ↓ (⟦ φ ⟧F ν) → Alμ↓ ν
    ins : ∀ {ν₁ ν₂} (C : Constr' φ ν₂) → InsCtx ν₁ (typeOf' φ ν₂ C) → Alμ ν₁ ν₂
    del : ∀ {ν₁ ν₂} (C : Constr' φ ν₁) → DelCtx ν₂ (typeOf' φ ν₁ C) → Alμ ν₁ ν₂

  {-getCtx : {ν : Fin n}{π : Prod n} →  Ctx ν π → Alμ ν
  getCtx (here x _) = x
  getCtx (there _ x) = getCtx x
  -}


  {-# TERMINATING #-}
  applyAlμ : ∀{ν₁ ν₂} → Alμ ν₁ ν₂ → Fix φ ν₁ → Maybe (Fix φ ν₂)
  insCtx : ∀ {π ν} → InsCtx ν π → Fix φ ν → Maybe (⟦ π ⟧P (Fix φ))
  delCtx : ∀ {π ν} → DelCtx ν π → ⟦ π ⟧P (Fix φ) → Maybe (Fix φ ν)

  applyAlμ (spn sp) x₁ = ⟨_⟩ <$> (applyPatch applyAlμ sp (unfix x₁))
  applyAlμ (ins C x) x₁ =  ⟨_⟩ <$> (inj C <$> insCtx x x₁)
  applyAlμ (del C x) x₁ = (delCtx x <=< match C) (unfix x₁)

  insCtx (here x x₂) x₁ = _∷ x₂ <$> applyAlμ x x₁
  insCtx (there x x₂) x₁ = x ∷_ <$> insCtx x₂ x₁

  delCtx (here x x₁) (px ∷ x₂) = applyAlμ x px
  delCtx (there x x₁) (px ∷ x₂) = delCtx x₁ x₂
