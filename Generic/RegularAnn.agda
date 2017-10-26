-- Annotated version of our regular types;
-- The annotations consists in a insert, delete or copy flag
-- on each constructor of a value.
module Generic.RegularAnn where

open import Prelude
open import Generic.Regular
open import Generic.Opaque
  public

data Ann : Set where
  I D C : Ann

⟦_⟧Sₐ : Sum → Set → Set
⟦ σ ⟧Sₐ X = Ann × ⟦ σ ⟧S X

data Fixₐ (σ : Sum) : Set where
  ⟨_⟩ : ⟦ σ ⟧Sₐ (Fixₐ σ) → Fixₐ σ 

{-
unfixₐ : {σ : Sum} → Fixₐ σ → ⟦ σ ⟧S (Fixₐ σ)
unfixₐ ⟨ _ , x ⟩ = x

fixₐ-unfixₐ-lemma : {σ : Sum}(x : Fixₐ σ) → ⟨ unfixₐ x ⟩ ≡ x
fixₐ-unfixₐ-lemma ⟨ x ⟩ = refl
-}
