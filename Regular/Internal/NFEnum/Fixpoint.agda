open import Prelude
open import Generic.Regular

module Regular.Internal.NFEnum.Fixpoint
         (μσ : Sum)
         (M : Set → Set)(m : RawMonadPlus M)
       where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open DecEq (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.NFEnum.Functor (Fix μσ) _≟Fix_ M m

  open RawMonadPlus m

  data Sign : Set where
    Pos Neg : Sign

  {-# TERMINATING #-}
  diffCtx : ∀ {π} → Phase → Sign → Fix μσ → ⟦ π ⟧P (Fix μσ) → M (Ctx π)
  diffAlμ' : Phase → Fix μσ → Fix μσ → M Alμ

  diffAlμ : Fix μσ → Fix μσ → M Alμ
  diffAlμ = diffAlμ' C

  diffCtx _ x₁ s [] = ∅
  diffCtx {K _ ∷ _} P s x₁ (k₂ ∷ ats₂) = there k₂ <$> diffCtx P s x₁ ats₂ 
  diffCtx {I ∷ _} P Neg x₁ (x₂ ∷ ats₂) 
    = flip here ats₂ <$> diffAlμ' P x₂ x₁
    ∣ there x₂ <$> diffCtx P Neg x₁ ats₂
  diffCtx {I ∷ _} P Pos x₁ (x₂ ∷ ats₂) 
    = flip here ats₂ <$> diffAlμ' P x₁ x₂
    ∣ there x₂ <$> diffCtx P Pos x₁ ats₂


  diff-del : ⟦ μσ ⟧S (Fix μσ) → Fix μσ → M Alμ
  diff-del s₁ x₂ with sop s₁ 
  ... | tag C₁ p₁ = del C₁ <$> diffCtx D Neg x₂ p₁

  diff-ins : Fix μσ → ⟦ μσ ⟧S (Fix μσ) → M Alμ
  diff-ins x₁ s₂ with sop s₂
  ... | tag C₂ p₂ = ins C₂ <$> diffCtx I Pos x₁ p₂

  diff-mod : ⟦ μσ ⟧S (Fix μσ) → ⟦ μσ ⟧S (Fix μσ) → M Alμ
  diff-mod s₁ s₂ = spn <$> diffS (diffAlμ' C) s₁ s₂
 
  diffAlμ' C ⟨ x ⟩ ⟨ y ⟩ 
       = diff-mod x y
       ∣ diff-ins ⟨ x ⟩ y
       ∣ diff-del x ⟨ y ⟩ 
  diffAlμ' D ⟨ x ⟩ ⟨ y ⟩ 
       = diff-mod x y
       ∣ diff-del x ⟨ y ⟩
  diffAlμ' I ⟨ x ⟩ ⟨ y ⟩ 
       = diff-ins ⟨ x ⟩ y
       ∣ diff-del x ⟨ y ⟩

  diff = diffAlμ
