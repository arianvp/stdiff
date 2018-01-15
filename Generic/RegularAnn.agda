-- Annotated version of our regular types;
-- The annotations consists in a insert, delete or copy flag
-- on each constructor of a value.
module Generic.RegularAnn where

open import Prelude
open import Generic.Regular
open import Generic.Opaque

-- An annotation represents either a moving part,
-- or a copied part. A moving part in the source represents
-- a deletion whereas a moving part in the destinationa
-- represents a insertion
data Ann : Set where
  M C : Ann

⟦_⟧Sₐ : Sum → Set → Set
⟦ σ ⟧Sₐ X = Ann × ⟦ σ ⟧S X

fmapSₐ : ∀{σ X Y} → (X → Y) → ⟦ σ ⟧Sₐ X → ⟦ σ ⟧Sₐ Y
fmapSₐ f (ann , x) = ann , fmapS f x

fmapSₐ-∘ : ∀{σ X Y Z}(g : Y → Z)(f : X → Y)(s : ⟦ σ ⟧Sₐ X)
         → fmapSₐ g (fmapSₐ f s) ≡ fmapSₐ (g ∘ f) s
fmapSₐ-∘ g f (ann , s) = cong (λ P → ann , P) (fmapS-∘ g f s)

fmapSₐ-id : ∀{σ X}(s : ⟦ σ ⟧Sₐ X) → fmapSₐ id s ≡ s
fmapSₐ-id (ann , s) = cong (λ P → ann , P) (fmapS-id s)

data Fixₐ (σ : Sum) : Set where
  ⟨_⟩ : ⟦ σ ⟧Sₐ (Fixₐ σ) → Fixₐ σ 

{-# TERMINATING #-}
𝓤 : ∀{σ} → Fixₐ σ → Fix σ
𝓤 ⟨ _ , x ⟩ = ⟨ fmapS 𝓤 x ⟩

unfixₐ : {σ : Sum} → Fixₐ σ → ⟦ σ ⟧Sₐ (Fixₐ σ)
unfixₐ ⟨ ann , x ⟩ = ann , x

{-# TERMINATING #-}
cataₐ : ∀{σ A} → (⟦ σ ⟧Sₐ A → A) → Fixₐ σ → A
cataₐ f ⟨ ann , x ⟩ = f (ann , fmapS (cataₐ f) x)

-- Handy projection
extractAnn : ∀{σ} → ⟦ I ⟧A (Fixₐ σ) → Ann
extractAnn ⟨ a , _ ⟩ = a

{-# TERMINATING #-}
cataₐ-uni : ∀{σ A}(f : ⟦ σ ⟧Sₐ A → A)(h : Fixₐ σ → A) 
          → (∀ x → h x ≡ f (fmapSₐ h (unfixₐ x)))
          → (x : Fixₐ σ)
          → cataₐ f x ≡ h x
cataₐ-uni f h hip ⟨ ann , x ⟩ 
  rewrite hip ⟨ ann , x ⟩ 
        = cong (λ P → f (ann , fmapS P x)) (fun-ext (cataₐ-uni f h hip))

-- * General purpose 'all-copy' and 'all-move'

ann-all : ∀{σ} → Ann → Fix σ → Fixₐ σ
ann-all ann = cata (λ s → ⟨ ann , s ⟩)

annAt-all : ∀{α σ} → Ann → ⟦ α ⟧A (Fix σ) → ⟦ α ⟧A (Fixₐ σ)
annAt-all {K _} _   x = x
annAt-all {I}   ann x = ann-all ann x

{-# TERMINATING #-}
ann-all-correct : ∀{σ}(a : Ann)(x : Fix σ)
                → 𝓤 (ann-all a x) ≡ x
ann-all-correct a ⟨ x ⟩ 
  = cong ⟨_⟩ (trans (fmapS-∘ 𝓤 (ann-all a) x) 
             (trans (cong (λ P → fmapS P x) 
                          (fun-ext {g = id} (ann-all-correct a))) 
                    (fmapS-id x)))

annAt-all-correct : ∀{α σ}(a : Ann)(x : ⟦ α ⟧A (Fix σ))
                  → fmapA {α} 𝓤 (annAt-all {α} a x) ≡ x
annAt-all-correct {K _} a x = refl
annAt-all-correct {I}   a x = ann-all-correct a x

module AnnCounter where
{-
  postulate magic : IsMonoid _≡_ _+_ 0 

  +-0-monoid : Monoid _ _
  +-0-monoid = record 
    { Carrier = ℕ 
    ; _≈_ = _≡_ 
    ; _∙_ = _+_
    ; ε = 0 
    ; isMonoid = magic
    }

  -- open import Data.Nat.Properties using (+-0-monoid)
  open RegularConsume +-0-monoid
-}
  open RegularConsume

  count-Ann : Ann → ℕ
  count-Ann C = 1
  count-Ann M = 0

  count-C : ∀{σ} → Fixₐ σ → ℕ
  count-C = cataₐ (λ { (ann , s) → count-Ann ann + consumeS s })

  count-CS : ∀{σ₁ σ₂} → ⟦ σ₁ ⟧S (Fixₐ σ₂) → ℕ
  count-CS = consumeS ∘ fmapS count-C

  count-CA : ∀{σ α} → ⟦ α ⟧A (Fixₐ σ) → ℕ
  count-CA {σ} {α} = consumeA {α} ∘ fmapA {α} count-C

  count-C* : ∀{σ π} → ⟦ π ⟧P (Fixₐ σ) → All (λ _ → ℕ) π
  count-C* {σ}         []       = []
  count-C* {σ} {α ∷ π} (a ∷ ps) = count-CA {σ} {α} a ∷ count-C* ps

  count-C*-sum : ∀{σ π} → ⟦ π ⟧P (Fixₐ σ) → ℕ
  count-C*-sum = all-foldr _+_ 0 ∘ count-C*

  count-CS≡C*-lemma
    : ∀{σ₁ σ₂}(C : Constr σ₁)(p : ⟦ typeOf σ₁ C ⟧P (Fixₐ σ₂))
    → count-CS {σ₁} {σ₂} (inj C p) ≡ count-C*-sum p
  count-CS≡C*-lemma {[]} () p
  count-CS≡C*-lemma {σ ∷ σs} (suc c) p = count-CS≡C*-lemma {σs} c p
  count-CS≡C*-lemma {σ ∷ σs} zero p    
    = auxP p
    where
      auxP : ∀{σ π}(p : ⟦ π ⟧P (Fixₐ σ))
           → consumeP (fmapP count-C p) ≡ count-C*-sum p
      auxP []       = refl
      auxP (px ∷ p) rewrite auxP p = refl

  count-C*-sum-base-lemma
    : ∀{σ α}(p : ⟦ α ⟧A (Fixₐ σ))
    → count-C*-sum {σ} {α ∷ []} (p ∷ []) ≡ count-CA {σ} {α} p
  count-C*-sum-base-lemma {σ} {α} p 
    = +-comm (count-CA {σ} {α} p) 0
