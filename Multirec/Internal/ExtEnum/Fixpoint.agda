open import Prelude
open import Generic.Multirec

module Multirec.Internal.ExtEnum.Fixpoint
         {n : ℕ}
         (φ : Fam n)
         (M : Set → Set)(m : RawMonadPlus M)
       where

  open import Multirec.Internal.Functor (Fix φ) _≟Fix_
  open DecEq (Fix φ) _≟Fix_
  open import Multirec.Internal.Fixpoint φ
  open import Multirec.Internal.ExtEnum.Functor (Fix φ) _≟Fix_ M m

  open RawMonadPlus m


  {-# TERMINATING #-}
  diffCtx : ∀ {π ν} → Fix φ ν → ⟦ π ⟧P (Fix φ) → M (Ctx (Alμ ν) π)
  diffAlμ : (ν₁ ν₂ : Fin n) → Fix φ ν₁ → Fix φ ν₂ → M (Alμ ν₁ ν₂)

  diffCtx x₁ [] = ∅
  diffCtx {K _ ∷ _} x₁ (k₂ ∷ ats₂) = there k₂ <$> diffCtx x₁ ats₂
  diffCtx {I ν₁ ∷ _} {ν} x₁ (x₂ ∷ ats₂) = flip here ats₂ <$> diffAlμ ν ν₁ x₁ x₂
                              ∣ there x₂ <$> diffCtx x₁ ats₂

 
  diffAlμ ν₁ ν₂ ⟨ x ⟩ ⟨ y ⟩ 
       = diff-mod x y
       ∣ diff-ins (⟨ x ⟩) y
       ∣ diff-del x (⟨ y ⟩)
    where diff-del : ⟦ ? ⟧S (Fix φ) → Fix φ ν₁ → M (Alμ ν₁ ν₂)
          diff-del s₁ x₂ with sop s₁ 
          ... | tag C₁ p₁ = del C₁ <$> diffCtx x₂ p₁

          diff-ins : Fix φ → ⟦ ? ⟧S (Fix φ) → M Alμ
          diff-ins x₁ s₂ with sop s₂
          ... | tag C₂ p₂ = ins C₂ <$> diffCtx x₁ p₂

          diff-mod : ⟦ ? ⟧S (Fix φ) → ⟦ ? ⟧S (Fix φ) → M Alμ
          diff-mod s₁ s₂ = spn <$> diffS diffAlμ s₁ s₂


  diff = diffAlμ
