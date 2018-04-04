open import Prelude
open import Generic.Multirec
module Multirec.Internal.Fixpoint {n : ℕ}(φ : Fam n) where
  open DecEq (Fix φ) _≟Fix_
  open import Multirec.Internal.Functor (Fix φ) _≟Fix_
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus
  open Paths
  
  data Alμ : Fin n → Set where
    peel : ∀ {ν₁ ν₂} (del : ∂ φ ν₁ ν₂)(ins :  ∂ φ ν₂ ν₁) → Patch Alμ (⟦ φ ⟧F ν₂) → Alμ ν₁

  {-# TERMINATING #-}
  applyAlμ : ∀ {ν} → Alμ ν → Fix φ ν → Maybe (Fix φ ν)
  applyAlμ (peel del₁ ins₁ sp) x₁ =
    match-∂ del₁ x₁ >>=  λ x →
    (⟨_⟩ <$> applyPatch applyAlμ sp  (unfix x)) >>=  λ x →
    match-∂ ins₁ x


