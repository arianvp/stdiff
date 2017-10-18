open import Prelude
open import Generic.Regular

module Regular.Internal.ExtEnum.Fixpoint
         (μσ : Sum)
         (M : Set → Set)(m : RawMonadPlus M)
       where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open DecEq (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.ExtEnum.Functor (Fix μσ) _≟Fix_ M m

  open RawMonadPlus m


  {-# TERMINATING #-}
  diffCtx : ∀ {π} → Fix μσ → ⟦ π ⟧P (Fix μσ) → M (Ctx π)
  diffAlμ : Fix μσ → Fix μσ → M Alμ

  diffCtx x₁ [] = ∅
  diffCtx {K _ ∷ _} x₁ (k₂ ∷ ats₂) = there k₂ <$> diffCtx x₁ ats₂ 
  diffCtx {I ∷ _} x₁ (x₂ ∷ ats₂) = flip here ats₂ <$> diffAlμ x₁ x₂
                              ∣ there x₂ <$> diffCtx x₁ ats₂

 
  diffAlμ ⟨ x ⟩ ⟨ y ⟩ 
       = diff-mod x y
       ∣ diff-ins (⟨ x ⟩) y
       ∣ diff-del x (⟨ y ⟩)
    where diff-del : ⟦ μσ ⟧S (Fix μσ) → Fix μσ → M Alμ
          diff-del s₁ x₂ with sop s₁ 
          ... | tag C₁ p₁ = del C₁ <$> diffCtx x₂ p₁

          diff-ins : Fix μσ → ⟦ μσ ⟧S (Fix μσ) → M Alμ
          diff-ins x₁ s₂ with sop s₂
          ... | tag C₂ p₂ = ins C₂ <$> diffCtx x₁ p₂

          diff-mod : ⟦ μσ ⟧S (Fix μσ) → ⟦ μσ ⟧S (Fix μσ) → M Alμ
          diff-mod s₁ s₂ = spn <$> diffS diffAlμ s₁ s₂


  diff = diffAlμ
