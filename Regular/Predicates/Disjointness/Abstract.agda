open import Prelude

module Regular.Predicates.Disjointness.Abstract where

  record Disjoint (A : Set) : Set₁ where
    field
      Pred : A → A → Set
      
      comm : ∀{a₁ a₂} → Pred a₁ a₂ → Pred a₂ a₁
      
