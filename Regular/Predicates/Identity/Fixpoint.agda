open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Fixpoint (μσ : Sum) where
  
  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_

  makeidAlμ : Fix μσ → Alμ

  open import Regular.Predicates.Identity.Functor (Fix μσ) _≟Fix_ Alμ makeidAlμ
    public
  
  {-# TERMINATING #-}
  identityAlμ : Alμ → Set
  identityAlμ (spn sp) = identityS identityAlμ sp
  identityAlμ _        = ⊥

  identityAtμ : ∀{α} → Atμ α → Set
  identityAtμ = identityAt identityAlμ

  makeidAlμ ⟨ x ⟩ = spn (makeidS identityAlμ x)

  makeidAtμ : ∀{α} → ⟦ α ⟧A (Fix μσ) → Atμ α
  makeidAtμ {I}   x = fix (spn Scp)
  makeidAtμ {K κ} x = set (x , x)
