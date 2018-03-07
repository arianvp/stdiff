open import Prelude
open import Generic.Multirec
module Multirec.Internal.Fixpoint {n : ℕ}(φ : Fam n) where
  open DecEq (Fix φ) _≟Fix_
  open import Multirec.Internal.Functor (Fix φ) _≟Fix_
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  data Alμ : Fin n → Set
  data Ctx  (ν : Fin n) : Prod n → Set

  data Ctx (ν : Fin n) where
    here  : {π : Prod n} → Alμ ν → All (λ α → ⟦ α ⟧A (Fix φ)) π → Ctx ν (I ν ∷ π)
    there : {α : Atom n}{π : Prod n} → ⟦ α ⟧A (Fix φ) → Ctx ν π → Ctx ν (α ∷ π)

  data Alμ where
    spn : {ν : Fin n}(sp : Patch (λ ν₁ → Alμ ν₁) (⟦ φ ⟧F ν)) → Alμ ν
    ins : {ν : Fin n}(C : Constr (⟦ φ ⟧F ν)) → Ctx ν (typeOf (⟦ φ ⟧F ν) C) → Alμ ν
    del : {ν : Fin n}(C : Constr (⟦ φ ⟧F ν)) → Ctx ν (typeOf (⟦ φ ⟧F ν) C) → Alμ ν


  getCtx : {ν : Fin n}{π : Prod n} →  Ctx ν π → Alμ ν
  getCtx (here x _) = x
  getCtx (there _ x) = getCtx x


  {-# TERMINATING #-}
  applyAlμ : {ν : Fin n} → Alμ ν → Fix φ ν → Maybe (Fix φ ν)
  insCtx : ∀ {π ν} → Ctx ν π → Fix φ ν → Maybe (⟦ π ⟧P (Fix φ))
  delCtx : ∀ {π ν} → Ctx ν π → ⟦ π ⟧P (Fix φ) → Maybe (Fix φ ν)

  applyAlμ (spn sp) x₁ = ⟨_⟩ <$> (applyPatch applyAlμ sp (unfix x₁))
  applyAlμ (ins C x) x₁ =  ⟨_⟩ <$> (inj C <$> insCtx x x₁)
  applyAlμ (del C x) x₁ = (delCtx x <=< match C) (unfix x₁)

  insCtx (here x x₂) x₁ = _∷ x₂ <$> applyAlμ x x₁
  insCtx (there x x₂) x₁ = x ∷_ <$> insCtx x₂ x₁

  delCtx (here x x₁) (px ∷ x₂) = applyAlμ x px
  delCtx (there x x₁) (px ∷ x₂) = delCtx x₁ x₂
