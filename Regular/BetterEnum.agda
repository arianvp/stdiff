open import Prelude
open import Generic.Regular

module Regular.BetterEnum (μσ : Sum) where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open DecEq (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ

  _<$>_ : {A B : Set} → (A → B) → List A → List B
  f <$> xs = List-map f xs

  Alμ⋆ : Set
  Alμ⋆ = List Alμ

  Atμ⋆ : Atom → Set
  Atμ⋆ = At Alμ⋆

  S⋆ : Set
  S⋆ = S Atμ⋆ (Al Atμ⋆) μσ

  diffAlμ⋆ : Fix μσ → Fix μσ → Alμ⋆
  diffAlμ⋆ ⟨ x ⟩ ⟨ y ⟩ 
    = {!!}
    where diff-del : ⟦ μσ ⟧S (Fix μσ) → Fix μσ → Alμ⋆
          diff-del s₁ x₂ with sop s₁ 
          ... | tag C₁ p₁ = del C₁ <$> {!!} --  diffCtx x₂ p₁

          diff-ins : Fix μσ → ⟦ μσ ⟧S (Fix μσ) → Alμ⋆
          diff-ins x₁ s₂ with sop s₂
          ... | tag C₂ p₂ = ins C₂ <$> {!!} -- diffCtx x₁ p₂

          diff-mod : ⟦ μσ ⟧S (Fix μσ) → ⟦ μσ ⟧S (Fix μσ) → Alμ⋆
          diff-mod s₁ s₂ = spn <$> {!!} -- diffS diffAlμ s₁ s₂
