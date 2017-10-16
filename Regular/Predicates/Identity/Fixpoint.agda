open import Prelude
open import Generic.Regular

module Regular.Predicates.Identity.Fixpoint (μσ : Sum) where
  
  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Fixpoint μσ using (module FixpointApplication)
  open FixpointApplication

  makeidAlμ : Fix μσ → Alμ

  {-# TERMINATING #-}
  identityAlμ : Alμ → Set

  open import Regular.Predicates.Identity.Functor (Fix μσ) _≟Fix_ Alμ makeidAlμ identityAlμ
    public
  
  identityAlμ (spn sp) = identityS sp
  identityAlμ _        = ⊥

  identityAtμ : ∀{α} → Atμ α → Set
  identityAtμ = identityAt

  makeidAlμ ⟨ x ⟩ = spn (makeidS x)

  makeidAtμ : ∀{α} → ⟦ α ⟧A (Fix μσ) → Atμ α
  makeidAtμ {I}   x = fix (spn Scp)
  makeidAtμ {K κ} x = set (x , x)

  module IdentityProperties
      where
    
    {-# TERMINATING #-}
    identityAlμ-correct : (a : Alμ)(hip : identityAlμ a)
                        → ∀ x → applyAlμ a x ≡ just x

    makeidAlμ-correct : (r : Fix μσ) → identityAlμ (makeidAlμ r)

    open IdentityPropertiesF applyAlμ identityAlμ-correct makeidAlμ-correct
    
    identityAlμ-correct (spn sp) hip ⟨ x ⟩ 
      with identityS-correct sp hip x
    ...| aux with applyPatch applyAlμ sp x
    ...| nothing = {!!}
    ...| just x' = {!!}
    identityAlμ-correct (ins C ctx) () x
    identityAlμ-correct (del C ctx) () x

    makeidAlμ-correct r = {!!}

    postulate
      identityAtμ-correct : {α : Atom}(a : Atμ α)(hip : identityAtμ a)
                          → ∀ x → applyAtμ a x ≡ just x

      makeidAtμ-correct : {α : Atom}(a : ⟦ α ⟧A (Fix μσ)) 
                        → identityAtμ {α} (makeidAtμ a)

    identityAtμ-uni : ∀{α}(a x : ⟦ α ⟧A (Fix μσ)) 
                    → applyAtμ {α} (makeidAtμ a) x ≡ just x
    identityAtμ-uni {α} a x 
      = identityAtμ-correct {α} (makeidAtμ a) (makeidAtμ-correct {α} a) x

    postulate 
      makeidAllAt-uni : ∀{π}(a : All (λ α → ⟦ α ⟧A (Fix μσ)) π)
                      → ∀ x → ⟪ All-map makeidAtμ a ⟫SP x ≡ just x 

      identityAllAtμ-uni : ∀{π}(atμs : All Atμ π)(hip : All-set identityAtμ atμs)
                         → ∀ xs → ⟪ atμs ⟫SP xs ≡ just xs
 
