open import Prelude
open import Generic.Regular

module Regular.Predicates.Span.Fixpoint (σμ : Sum) where

  open import Regular.Internal.Fixpoint σμ
  open import Regular.Internal.Functor (Fix σμ) _≟Fix_
  open import Regular.Predicates.Domain.Fixpoint σμ
  open import Regular.Predicates.Domain.Functor (Fix σμ) _≟Fix_ Alμ applyAlμ _∈domAlμ_
  open import Regular.Predicates.Span.Functor (Fix σμ) _≟Fix_ Alμ applyAlμ _∈domAlμ_
    public

  {-# TERMINATING #-}
  spanAlμ : Alμ → Alμ → Set
  spanCtx : ∀{π} → Ctx π → Ctx π → Set

  spanAtCtx : ∀{π} → All Atμ π → Ctx π → Set


  spanAlμ (ins C₁ s₁) s₂          = spanAlμ (getCtx s₁) s₂
  spanAlμ s₁ (ins C₂ s₂)          = spanAlμ s₁ (getCtx s₂)
  spanAlμ (spn s₁) (spn s₂)       = spanS spanAlμ s₁ s₂
  spanAlμ (spn Scp) (del C₂ s₂)   = Unit
  -- * If the spine is a Scns and its recursive changes
  --   matches the deletion context, they still make a span.
  spanAlμ (spn (Scns C₁ at₁))  (del C₂ s₂)   
    = Σ (C₁ ≡ C₂) (λ { refl → spanAtCtx at₁ s₂ })

  spanAlμ (spn _)              (del C₂ s₂)   
    = ⊥

  spanAlμ (del C₁ s₁) (spn Scp)   = Unit
  spanAlμ (del C₁ s₁) (spn (Scns C₂ at₂))   
    = Σ (C₁ ≡ C₂) (λ { refl → spanAtCtx at₂ s₁ })
  spanAlμ (del C₁ s₁) (spn _) 
    = ⊥
  spanAlμ (del C₁ s₁) (del C₂ s₂) 
    = Σ (C₁ ≡ C₂) (λ { refl → spanCtx s₁ s₂ })
  
  spanCtx (here alμ₁ rest₁) (here alμ₂ rest₂) = spanAlμ alμ₁ alμ₂ × rest₁ ≡ rest₂
  spanCtx (there a₁ ctx₁)   (there a₂ ctx₂)   = a₁ ≡ a₂ × spanCtx ctx₁ ctx₂
  spanCtx _                 _                 = ⊥


  all-∈domAt : ∀{l} → All (λ α → ⟦ α ⟧A (Fix σμ)) l → All Atμ l → Set
  all-∈domAt [] [] = Unit
  all-∈domAt (a ∷ as) (at ∷ ats) = a ∈domAt at × all-∈domAt as ats


  spanAtCtx [] ()
  spanAtCtx (fix a ∷ as) (here alμ rest) = spanAlμ a alμ × all-∈domAt rest as 
  spanAtCtx (a ∷ as) (there a' ctx)      = (a' ∈domAt a) × spanAtCtx as ctx
