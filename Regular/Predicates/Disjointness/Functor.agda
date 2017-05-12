open import Prelude
open import Generic.Regular
open import Regular.Predicates.Disjointness.Abstract

module Regular.Predicates.Disjointness.Functor
       (Rec     : Set)
       (_≟Rec_  : (x y : Rec) → Dec (x ≡ y))
       (RecDisj : Disjoint Rec)
    where

  open import Regular.Internal.Functor Rec _≟Rec_

  disjS'  : {σ     : Sum}  → (s₁ s₂ : S (At Rec) (Al (At Rec)) σ) → Set
  disjAl' : {π₁ π₂ : Prod} → (π₁ π₂ : Al (At Rec) π₁ π₂)          → Set
  disjAt' : {α     : Atom} → (a₁ a₂ : At Rec α)                   → Set

  disjS' Scp              s   = Unit
  disjS' s                Scp = Unit
  disjS' (Scns C₁ at₁)    (Scns C₂ at₂) 
    = {!!}
  disjS' (Scns C₁ at₁)    (Schg C₂ C₃ al₂)
    = {!!}
  disjS' (Schg C₁ C₂ al₁) (Scns C₃ at₂)
    = {!!}
  disjS' (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂)
    = {!!}

  disjAl' = {!!}

  disjAt' = {!!}

  private
    disjSpred : {σ : Sum}{At : Atom → Set}{Al : Rel Prod _} 
              → (disjAt : ∀ {α}     → Disjoint (At α))
              → (disjAl : ∀ {π₁ π₂} → Disjoint (Al π₁ π₂))
              → (s₁ s₂ : S At Al σ) → Set
    disjSpred disjAt disjAl Scp s₂ = Unit
    disjSpred disjAt disjAl s₁ Scp = Unit
    disjSpred disjAt disjAl (Scns C₁ at₁) (Scns C₂ at₂)   = {!!}
    disjSpred disjAt disjAl (Scns C₁ at₁) (Schg C₂ C₃ al) = {!!}
    disjSpred disjAt disjAl (Schg C₁ C₂ al) s₂ = {!!}
{-
  disjS : {σ : Sum}{At : Atom → Set}{Al : Rel Prod _}
        → (disjAt : ∀ {α}     → Disjoint (At α))
        → (disjAl : ∀ {π₁ π₂} → Disjoint (Al π₁ π₂))
        → Disjoint (S At Al σ)
  disjS disjAt disjAl 
    = record { Pred = {!!} 
             ; comm = {!!} 
             }
-}
