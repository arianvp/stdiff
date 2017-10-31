open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.AnnEnum (μσ : Sum) where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ
  open DecEq (Fix μσ) _≟Fix_

  TrivialAₐ : Atom → Set
  TrivialAₐ α = ⟦ α ⟧A (Fixₐ μσ) × ⟦ α ⟧A (Fixₐ μσ)

  TrivialPₐ : Rel Prod _
  TrivialPₐ π₁ π₂ = ⟦ π₁ ⟧P (Fixₐ μσ) × ⟦ π₂ ⟧P (Fixₐ μσ)

  spine : ∀ {σ} → ⟦ σ ⟧S (Fixₐ μσ) → ⟦ σ ⟧S (Fixₐ μσ) 
        → S TrivialAₐ TrivialPₐ σ
  spine s₁ s₂ with fmapS 𝓤 s₁ ≟S fmapS 𝓤 s₂
  ...| yes _ = Scp
  ...| no ¬p  with sop s₁ | sop s₂
  ...| tag C₁ p₁ | tag C₂ p₂ with C₁ ≟F C₂
  ...| yes refl = Scns C₁ (zipd p₁ p₂)
  ...| no ¬q = Schg C₁ C₂ {¬q} (p₁ , p₂)

  extractAnn : ⟦ I ⟧A (Fixₐ μσ) → Ann
  extractAnn ⟨ a , _ ⟩ = a

  hasCopy : ⟦ I ⟧A (Fixₐ μσ) → Bool
  hasCopy = cataₐ gene
    where
      consumeP : ∀{π} → ⟦ π ⟧P Bool → Bool
      consumeP [] = false
      consumeP {K _ ∷ _} (x ∷ xs) = consumeP xs
      consumeP {I   ∷ _} (true  ∷ xs) = true
      consumeP {I   ∷ _} (false ∷ xs) = consumeP xs
 
      consumeS : ∀{σ} → ⟦ σ ⟧S Bool → Bool
      consumeS (there x) = consumeS x
      consumeS (here x)  = consumeP x

      gene : ∀{σ} → ⟦ σ ⟧Sₐ Bool → Bool
      gene (C , x) = true
      gene (M , x) = consumeS x
  
  align : ∀{π₁ π₂} → ⟦ π₁ ⟧P (Fixₐ μσ) → ⟦ π₂ ⟧P (Fixₐ μσ) 
        → Al TrivialAₐ π₁ π₂
  align  [] [] = A0
  align  {_} {α ∷ _} [] (at₂ ∷ ats₂) 
    = Ains (fmapA {α} 𝓤 at₂) (align [] ats₂)
  align {α ∷ _} (at₁ ∷ ats₁) [] 
    = Adel (fmapA {α} 𝓤 at₁) (align ats₁ [])
  align {K κ₁ ∷ π₁} {K κ₂ ∷ π₂} (at₁ ∷ ats₁) (at₂ ∷ ats₂) 
    with κ₁ ≟Konst κ₂
  ...| yes refl = AX (at₁ , at₂) (align ats₁ ats₂) 
  ...| no  _    = Adel at₁ (Ains at₂ (align ats₁ ats₂))
  align {K κ₁ ∷ π₁} {I    ∷ π₂} (at₁ ∷ ats₁) (at₂ ∷ ats₂) 
    with extractAnn at₂
  ...| M = Ains (fmapA {I} 𝓤 at₂) (align (at₁ ∷ ats₁) ats₂)
  ...| C = Adel at₁ (align ats₁ (at₂ ∷ ats₂))
  align {I ∷ π₁}    {K κ₂ ∷ π₂} (at₁ ∷ ats₁) (at₂ ∷ ats₂) 
    with extractAnn at₁
  ...| M = Adel (fmapA {I} 𝓤 at₁) (align ats₁ (at₂ ∷ ats₂))
  ...| C = Ains at₂ (align (at₁ ∷ ats₁) ats₂) 
  align {I ∷ π₁}    {I ∷ π₂} (at₁ ∷ ats₁) (at₂ ∷ ats₂) 
    with extractAnn at₁ | extractAnn at₂
  ...| M | _ = Adel (fmapA {I} 𝓤 at₁) (align ats₁ (at₂ ∷ ats₂)) 
  ...| C | M = Ains (fmapA {I} 𝓤 at₂) (align (at₁ ∷ ats₁) ats₂) 
  ...| C | C = AX (at₁ , at₂) (align ats₁ ats₂)

  {-# TERMINATING #-}
  diffCtx : ∀ {π} → Fixₐ μσ → ⟦ π ⟧P (Fixₐ μσ) → Ctx π
  diffAlμ : Fixₐ μσ → Fixₐ μσ → Alμ

  diffAtμ : ∀{α} → ⟦ α ⟧A (Fixₐ μσ) → ⟦ α ⟧A (Fixₐ μσ) → Atμ α
  diffAtμ {K κ} x y = set (x , y)
  diffAtμ {I}   x y = fix (diffAlμ x y)

  diffCtx x₁ [] 
    = magic
    where postulate magic : Ctx []
  diffCtx {K _ ∷ _} x₁ (k₂ ∷ ats₂) 
    = there k₂ (diffCtx x₁ ats₂) 
  diffCtx {I ∷ _}   x₁ (x₂ ∷ ats₂) 
    with extractAnn x₂ 
  ...| M = there (fmapA {I} 𝓤 x₂) (diffCtx x₁ ats₂) 
  ...| C = here (diffAlμ x₁ x₂) (All-map (λ {α} → fmapA {α} 𝓤) ats₂)

  diff-del : ⟦ μσ ⟧S (Fixₐ μσ) → Fixₐ μσ → Alμ
  diff-ins : Fixₐ μσ → ⟦ μσ ⟧S (Fixₐ μσ) → Alμ
  diff-mod : ⟦ μσ ⟧S (Fixₐ μσ) → ⟦ μσ ⟧S (Fixₐ μσ) → Alμ

  diffAlμ ⟨ M , x ⟩ ⟨ ay , y ⟩ = diff-del x ⟨ ay , y ⟩
  diffAlμ ⟨ C , x ⟩ ⟨ M  , y ⟩ = diff-ins ⟨ C , x ⟩ y
  diffAlμ ⟨ C , x ⟩ ⟨ C , y ⟩  = diff-mod x y

  diff-del s₁ x₂ with sop s₁
  ...| tag C₁ p₁ = del C₁ (diffCtx x₂ p₁)

  diff-ins x₁ s₂ with sop s₂
  ...| tag C₂ p₂ = ins C₂ (diffCtx x₁ p₂) 

  diff-mod s₁ s₂ 
    = spn (S-map (uncurry diffAtμ) (al-map (uncurry diffAtμ) ∘ uncurry align) 
          (spine s₁ s₂))

