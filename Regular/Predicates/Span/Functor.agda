open import Prelude
open import Generic.Regular

module Regular.Predicates.Span.Functor
       (Rec      : Set)
       (_≟Rec_   : (x y : Rec) → Dec (x ≡ y))
       (PatchRec : Set)
       (idRec    : PatchRec → Set)
       (spanRec  : PatchRec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor Rec _≟Rec_ PatchRec idRec

  spanS  : {σ        : Sum}  → (s₁ s₂ : S (At PatchRec) (Al (At PatchRec)) σ) → Set
  spanAl : {π₁ π₂ π₃ : Prod} → Al (At PatchRec) π₁ π₂ → Al (At PatchRec) π₁ π₃ → Set
  spanAt : {α        : Atom} → (a₁ a₂ : At PatchRec α)                   → Set

  spanAtAll : ∀{l₁ l₂} → All (At PatchRec) l₁ → Al (At PatchRec) l₁ l₂ → Set
  spanAtAll []       _  = Unit
  spanAtAll (a ∷ as) (Ains at al) = spanAtAll (a ∷ as) al
  spanAtAll (a ∷ as) (Adel at al) = identityAt a × spanAtAll as al
  spanAtAll (a ∷ as) (AX at al)   = spanAt a at × spanAtAll as al

  -- * When one spine is a copy, they are obviously a span.
  spanS Scp              s   = Unit
  spanS s                Scp = Unit

  -- * For two changes to be a span we need their
  --   constructors to be the same and the recursive
  --   children to be pairwise spans.
  spanS {σ} (Scns C₁ at₁)    (Scns C₂ at₂) 
    = Σ (C₁ ≡ C₂) (λ { refl → spanAts at₁ at₂ })
    where
     spanAts : ∀{l}(a₁ a₂ : All (At PatchRec) l) → Set
     spanAts []         []         = Unit
     spanAts (a₁ ∷ as₁) (a₂ ∷ as₂) = spanAt a₁ a₂ × spanAts as₁ as₂

  -- * A constructor change can be a span with a change,
  --   as long as they start at the same constructor and their 
  --   changes are spanAtAll
  spanS (Scns C₁ at₁)    (Schg C₂ C₃ al₂)
    = Σ (C₁ ≡ C₂) (λ { refl → spanAtAll at₁ al₂ })

  -- * Span is obviously symmetric, so the definition here
  --   is the very same.
  spanS (Schg C₁ C₂ al₁) (Scns C₃ at₂)
    = Σ (C₁ ≡ C₃) (λ { refl → spanAtAll at₂ al₁ })

  -- * Two constructor changes are a span whenever they
  --   change the same constructor and their alignments are
  --   a span. 
  spanS (Schg C₁ C₂ al₁) (Schg C₃ C₄ al₂)
    = Σ (C₁ ≡ C₃) (λ { refl → spanAl al₁ al₂ })

  -- * Two alignments al₁ and al₂ make a span whenever
  --   dom (applyAl al₁) ≡ dom (applyAl al₂).
  --
  spanAl A0            A0            = Unit
  spanAl (Ains _ al₁)  al₂           = spanAl al₁ al₂
  spanAl al₁           (Ains _ al₂)  = spanAl al₁ al₂
  
  -- * Since we ignore the contents of a deletion in the application
  --   function, we do not require that a₁ and a₂ are equal.
  spanAl (Adel a₁ al₁) (Adel a₂ al₂) = spanAl al₁ al₂

  -- * If we have a change and a deletion, however, the change
  --   must be an identity.
  spanAl (Adel a₁ al₁) (AX at₂ al₂)  = identityAt at₂ × spanAl al₁ al₂
  spanAl (AX at₁ al₁)  (Adel a₂ al₂) = identityAt at₁ × spanAl al₁ al₂
  spanAl (AX at₁ al₁)  (AX at₂ al₂)  = spanAt at₁ at₂ × spanAl al₁ al₂

  spanAt (set ks₁)  (set ks₂)  = proj₁ ks₁ ≡ proj₁ ks₂
  spanAt (fix spμ₁) (fix spμ₂) = spanRec spμ₁ spμ₂
