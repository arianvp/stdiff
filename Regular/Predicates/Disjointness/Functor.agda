open import Prelude
open import Generic.Regular
open import Regular.Predicates.Disjointness.Abstract

module Regular.Predicates.Disjointness.Functor
       (Rec      : Set)
       (_≟Rec_   : (x y : Rec) → Dec (x ≡ y))
       (PatchRec : Set)
       (applyRec : PatchRec → Rec → Maybe Rec)
       (spanRec  : PatchRec → PatchRec → Set)
       (disjRec  : PatchRec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Span.Functor Rec _≟Rec_ PatchRec applyRec spanRec

  disjS  : {σ     : Sum}  
         → (s₁ s₂ : S (At PatchRec) (Al (At PatchRec)) σ) 
         → (hip   : spanS s₁ s₂)
         → Set
  disjAl : {π₁ π₂ : Prod} → (π₁ π₂ : Al (At Rec) π₁ π₂)          → Set
  disjAt : {α     : Atom} → (a₁ a₂ : At PatchRec α)              → Set

  disjS Scp              s   hip = Unit
  disjS s                Scp hip = Unit
  disjS (Scns C₁ at₁)    (Scns .C₁ at₂) (refl , hip)
    = All-set (uncurry {!!}) (zipd at₁ at₂)
  disjS (Scns C₁ at₁)    (Schg .C₁ C₃ al₂) (refl , hip)
    = {!!}
  disjS (Schg C₁ C₂ al₁) (Scns .C₁ at₂) (refl , hip)
    = {!!}
  disjS (Schg C₁ C₂ al₁) (Schg .C₁ C₄ al₂) (refl , hip)
    = {!!}

  disjAl = {!!}

  disjAt = {!!}

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
