open import Prelude
open import Generic.Regular

module Regular.BetterEnum (μσ : Sum) where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open DecEq (Fix μσ) _≟Fix_

  Atμ⋆ : Atom → Set
  data Alμ : Set
  data Ctx⋆ : Prod → Set

  Alμ⋆ : Set
  Alμ⋆ = List Alμ

  S⋆ : Set
  S⋆ = S (λ α → Atμ⋆ α) (λ _ _ → ⊥) μσ


  data Alμ where
    spn : S⋆ → Alμ
    ins : (C : Constr μσ)(spμ : Ctx⋆ (typeOf μσ C)) → Alμ
    del : (C : Constr μσ)(spμ : Ctx⋆ (typeOf μσ C)) → Alμ

  data Ctx⋆ where
    here  : ∀{π} → (spμ : Alμ⋆)(atμs : All (λ α → ⟦ α ⟧A (Fix μσ)) π) → Ctx⋆ (I ∷ π)
    there : ∀{α π} → (atμ : ⟦ α ⟧A (Fix μσ))(alμs : Ctx⋆ π) → Ctx⋆ (α ∷ π)

  Atμ⋆ = At Alμ⋆


  module Height where
    mutual
      {-# TERMINATING #-}
      heightS : ∀{σ} → ⟦ σ ⟧S (Fix μσ) → ℕ
      heightS (here ps) = heightP ps
      heightS (there s) = heightS s 

      heightP : ∀{π} → ⟦ π ⟧P (Fix μσ) → ℕ
      heightP as = max 0 (All-map (λ {α} → heightA {α}) as)
        where
          max : {A : Set}{π : List A} → ℕ → All (λ _ → ℕ) π → ℕ
          max acc [] = acc
          max acc (x ∷ xs) with x ≤? acc
          ...| no  _ = max acc xs 
          ...| yes _ = max x xs 

      heightA : ∀{α} → ⟦ α ⟧A (Fix μσ) → ℕ
      heightA {K κ}   _   = 0
      heightA {I}   ⟨ x ⟩ = 1 + heightS x

  open Height

  _<$>_ : {A B : Set} → (A → B) → List A → List B
  f <$> xs = List-map f xs

  data CMP : Set where
    LT EQ GT : CMP

  compare-PI : ℕ → ℕ → CMP
  compare-PI n m with compare n m
  ...| less    _ _ = LT
  ...| equal   _   = EQ
  ...| greater _ _ = GT

  mutual
    diffAlμ⋆ : Fix μσ → Fix μσ → Alμ⋆
    diffAlμ⋆ ⟨ x ⟩ ⟨ y ⟩ 
      with x ≟S y
    ...| yes _ = spn Scp ∷ []
    ...| no  _
      with sop x | sop y
    ...| tag cx dx | tag cy dy
      with cx ≟F cy
    ...| yes refl = spn (Scns cx (All-map (λ axy → diffAtμ⋆ axy) (zipd dx dy))) ∷ []
    ...| no  _    = diffAlμInsDel⋆ ⟨ x ⟩ ⟨ y ⟩

    diffAtμ⋆ : ∀{α} → ⟦ α ⟧A (Fix μσ) × ⟦ α ⟧A (Fix μσ) → Atμ⋆ α
    diffAtμ⋆ {K κ} (x , y) = set (x , y)
    diffAtμ⋆ {I}   (x , y) = fix (diffAlμ⋆ x y)

    diffAlμInsDel⋆ : Fix μσ → Fix μσ → Alμ⋆
    diffAlμInsDel⋆ ⟨ x ⟩ ⟨ y ⟩ 
      with compare-PI (heightS x) (heightS y) 
    ...| LT = diff-ins ⟨ x ⟩ y
    ...| EQ = diff-ins ⟨ x ⟩ y ++ diff-del x ⟨ y ⟩
    ...| GT = diff-del x ⟨ y ⟩

    diff-del : ⟦ μσ ⟧S (Fix μσ) → Fix μσ → Alμ⋆
    diff-del s₁ x₂ with sop s₁ 
    ... | tag C₁ p₁ = del C₁ <$> diffCtx x₂ p₁

    diff-ins : Fix μσ → ⟦ μσ ⟧S (Fix μσ) → Alμ⋆
    diff-ins x₁ s₂ with sop s₂
    ... | tag C₂ p₂ = ins C₂ <$> diffCtx x₁ p₂

    {-# TERMINATING #-}
    diffCtx : ∀ {π} → Fix μσ → ⟦ π ⟧P (Fix μσ) → List (Ctx⋆ π)
    diffCtx x₁ [] = []
    diffCtx {K _ ∷ _} x₁ (k₂ ∷ ats₂) 
      = there k₂ <$> diffCtx x₁ ats₂ 
    diffCtx {I ∷ _} x₁ (x₂ ∷ ats₂) 
      = here (diffAlμ⋆ x₁ x₂) ats₂
      ∷ there x₂ <$> diffCtx x₁ ats₂

  open import Regular.Internal.Fixpoint μσ as BASE
    using ()

  S-map : {σ : Sum}
          {At₁ At₂ : Atom → Set}
          {Al₁ Al₂ : Rel Prod _}
        → (At₁ ⊆ At₂)
        → (∀{π₁ π₂} → Al₁ π₁ π₂ → Al₂ π₁ π₂)
        → S At₁ Al₁ σ → S At₂ Al₂ σ
  S-map f g Scp = Scp
  S-map f g (Scns C ps) = Scns C (All-map f ps)
  S-map f g (Schg C₁ C₂ {q} al) = Schg C₁ C₂ {q} (g al)

  minOn : ∀{a}{A : Set a}(f : A → ℕ) → List A → A
  minOn f [] = magic
    where postulate magic : ∀{a}{A : Set a} → A
  minOn f (x ∷ xs) = go f x xs
    where go : ∀{a}{A : Set a}(f : A → ℕ) → A → List A → A
          go f acc [] = acc
          go f acc (x ∷ xs)
            with f acc ≤? f x
          ...| yes _ = go f acc xs
          ...| no  _ = go f x xs


  {-# TERMINATING #-}
  crushAlμ : Alμ → BASE.Alμ
  crushAlμ⋆ : Alμ⋆ → BASE.Alμ
  crushCtx⋆ : ∀{π} → Ctx⋆ π → BASE.Ctx π

  crushAtμ⋆ : ∀{α} → Atμ⋆ α → BASE.Atμ α
  crushAtμ⋆ (set x) = set x
  crushAtμ⋆ (fix x) = fix (crushAlμ⋆ x )

  crushAlμ⋆ x = minOn BASE.costAlμ (List-map crushAlμ x)

  crushAlμ (spn x) = BASE.spn (S-map crushAtμ⋆ (λ ()) x)
  crushAlμ (ins C spμ) = BASE.ins C (crushCtx⋆ spμ)
  crushAlμ (del C spμ) = BASE.del C (crushCtx⋆ spμ)

  crushCtx⋆ (here spμ atμs) = BASE.here (crushAlμ⋆ spμ) atμs
  crushCtx⋆ (there atμ ctx) = BASE.there atμ (crushCtx⋆ ctx)
