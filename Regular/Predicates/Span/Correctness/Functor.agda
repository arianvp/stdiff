open import Prelude
open import Generic.Regular

module Regular.Predicates.Span.Correctness.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (_∈domRec_ : Rec → PatchRec → Set)
       (spanRec   : PatchRec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Domain.Functor Rec _≟Rec_ PatchRec applyRec _∈domRec_
  open import Regular.Predicates.Span.Functor Rec _≟Rec_ PatchRec applyRec _∈domRec_ spanRec

  -- XXX: 
  -- This is false.
  -- Take the following two patches:
  -- 
  --          / \
  --         /   \
  --        / \ / \
  --        1 2 1 2
  --     ↙ₚ          ↘ᵣ
  -- 
  --    / \          / \
  --   /   \        /   \
  --  / \ / \      / \ / \
  --  3 2 1 2      1 2 3 2
  -- 
  -- we have that (dom p ∩ dom r ≢ ∅), but they are not comparable.

  subdomS : {σ : Sum}(s₁ s₂ : Patch PatchRec σ) → Set
  subdomS s₁ s₂ = ∀ x → x ∈domS s₁ → x ∈domS s₂

  subdomAl : {π₁ π₂ : Prod}(p₁ p₂ : Al (At PatchRec) π₁ π₂) → Set
  subdomAl p₁ p₂ = ∀ x → x ∈domAl p₁ → x ∈domAl p₂

  subdomAt : {α : Atom}(a₁ a₂ : At PatchRec α) → Set
  subdomAt a₁ a₂ = ∀ x → x ∈domAt a₁ → x ∈domAt a₂

  spanS-ok : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : spanS s₁ s₂)
           → subdomS s₁ s₂ ⊎ subdomS s₂ s₁
  
  spanAl-ok : {π₁ π₂ : Prod}(p₁ p₂ : Al (At PatchRec) π₁ π₂) 
            → (hip : spanAl p₁ p₂)
            → subdomAl p₁ p₂ ⊎ subdomAl p₂ p₁
  
  spanAt-ok : {α : Atom}(a₁ a₂ : At PatchRec α)
           → (hip : spanAt a₁ a₂)
           → subdomAt a₁ a₂ ⊎ subdomAt a₂ a₂
  
  spanS-ok Scp s₂ hip = inj₂ (λ _ _ → unit)
  spanS-ok s₁ Scp hip = inj₁ (λ _ _ → unit)
  spanS-ok (Scns C₁ at₁) (Scns .C₁ at₂) (refl , hip)
    = {!!}
  spanS-ok s₁ s₂ hip = {!!}

  spanAl-ok = {!!}

  spanAt-ok = {!!}
