open import Prelude
open import Generic.Regular

module Regular.Internal.ForkEnum.FunctorFix (μσ : Sum) where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ 
  open DecEq (Fix μσ) _≟Fix_

  -- *******************************************
  -- *
  -- * The extensive enumeration is a great characterization
  -- * of all possible patches; but is a horrible program for computing them.
  -- *
  -- * The Fork-family of types takes advantage of the intrinsic
  -- * disjointness of changes, when expressed as trees, by pushing
  -- * the relevant choice points (Forks) to where they actually need
  -- * to happen.
  -- *
  -- * This is a heuristic search and by no means total; nevertheless,
  -- * the algorithm starts with an eager phase where it consumes as many
  -- * equal constructors as possible; when it finds a difference, it tries
  -- * to insert or delete depending in the height of the trees in question.
  -- * 
  -- * The datatypes look like: 
  -- *
  ForkAtμ : Atom → Set
  data ForkAlμ : Set
  data ForkCtx : Prod → Set

  ForkS : Set
  ForkS = S (λ α → ForkAtμ α) (λ _ _ → ⊥) μσ

  data ForkAlμ where
    spn : ForkS → ForkAlμ
    ins : (C : Constr μσ)(spμ : ForkCtx (typeOf μσ C)) → ForkAlμ
    del : (C : Constr μσ)(spμ : ForkCtx (typeOf μσ C)) → ForkAlμ

  data ForkCtx where
    here  : ∀{π} → (spμ : List ForkAlμ)(atμs : All (λ α → ⟦ α ⟧A (Fix μσ)) π) → ForkCtx (I ∷ π)
    there : ∀{α π} → (atμ : ⟦ α ⟧A (Fix μσ))(alμs : ForkCtx π) → ForkCtx (α ∷ π)

  ForkAtμ = At (List ForkAlμ)


  --
  -- We use a generic height function
  --
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
 
  --
  -- And some utilities for comparing and mapping values
  --
  _<$>_ : {A B : Set} → (A → B) → List A → List B
  f <$> xs = List-map f xs

  data CMP : Set where
    LT EQ GT : CMP

  compare-PI : ℕ → ℕ → CMP
  compare-PI n m with compare n m
  ...| less    _ _ = LT
  ...| equal   _   = EQ
  ...| greater _ _ = GT

  S-map : {σ : Sum}
          {At₁ At₂ : Atom → Set}
          {Al₁ Al₂ : Rel Prod _}
        → (At₁ ⊆ At₂)
        → (∀{π₁ π₂} → Al₁ π₁ π₂ → Al₂ π₁ π₂)
        → S At₁ Al₁ σ → S At₂ Al₂ σ
  S-map f g Scp = Scp
  S-map f g (Scns C ps) = Scns C (All-map f ps)
  S-map f g (Schg C₁ C₂ {q} al) = Schg C₁ C₂ {q} (g al)


  -- 
  -- Finally, the enumeration produces a a list of options Forks,
  -- note how we eagerly consume constructors by recursing on diffForkAlμ
  -- whenever possible.
  -- 
  mutual
    diffForkAlμ : Fix μσ → Fix μσ → List ForkAlμ
    diffForkAlμ ⟨ x ⟩ ⟨ y ⟩ 
      with x ≟S y
    ...| yes _ = spn Scp ∷ []
    ...| no  _
      with sop x | sop y
    ...| tag cx dx | tag cy dy
      with cx ≟F cy
    ...| yes refl = spn (Scns cx (All-map (λ axy → diffForkAtμ axy) (zipd dx dy))) ∷ []
    ...| no  _    = diffForkAlμInsDel ⟨ x ⟩ ⟨ y ⟩

    diffForkAtμ : ∀{α} → ⟦ α ⟧A (Fix μσ) × ⟦ α ⟧A (Fix μσ) → ForkAtμ α
    diffForkAtμ {K κ} (x , y) = set (x , y)
    diffForkAtμ {I}   (x , y) = fix (diffForkAlμ x y)

    diffForkAlμInsDel : Fix μσ → Fix μσ → List ForkAlμ
    diffForkAlμInsDel ⟨ x ⟩ ⟨ y ⟩ 
      with compare-PI (heightS x) (heightS y) 
    ...| LT = diff-ins ⟨ x ⟩ y
    ...| EQ = diff-ins ⟨ x ⟩ y ++ diff-del x ⟨ y ⟩
    ...| GT = diff-del x ⟨ y ⟩

    diff-del : ⟦ μσ ⟧S (Fix μσ) → Fix μσ → List ForkAlμ
    diff-del s₁ x₂ with sop s₁ 
    ... | tag C₁ p₁ = del C₁ <$> diffCtx x₂ p₁

    diff-ins : Fix μσ → ⟦ μσ ⟧S (Fix μσ) → List ForkAlμ
    diff-ins x₁ s₂ with sop s₂
    ... | tag C₂ p₂ = ins C₂ <$> diffCtx x₁ p₂

    {-# TERMINATING #-}
    diffCtx : ∀ {π} → Fix μσ → ⟦ π ⟧P (Fix μσ) → List (ForkCtx π)
    diffCtx x₁ [] = []
    diffCtx {K _ ∷ _} x₁ (k₂ ∷ ats₂) 
      = there k₂ <$> diffCtx x₁ ats₂ 
    diffCtx {I ∷ _} x₁ (x₂ ∷ ats₂) 
      = here (diffForkAlμ x₁ x₂) ats₂
      ∷ there x₂ <$> diffCtx x₁ ats₂

  diffFork : Fix μσ → Fix μσ → List ForkAlμ
  diffFork x y
    = diffForkAlμ x y ++ diffForkAlμInsDel x y
  
  --
  -- Translating a ForkAlμ to a Alμ is easy,
  -- we just eliminate the Fork-points by choosing
  -- the one with the least cost.
  --

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
  crushForkAlμ : ForkAlμ → Alμ
  crush        : List ForkAlμ → Alμ
  crushForkCtx : ∀{π} → ForkCtx π → Ctx π

  crushForkAtμ : ∀{α} → ForkAtμ α → Atμ α
  crushForkAtμ (set x) = set x
  crushForkAtμ (fix x) = fix (crush x )

  crush x = minOn costAlμ (List-map crushForkAlμ x)

  crushForkAlμ (spn x) = spn (S-map crushForkAtμ (λ ()) x)
  crushForkAlμ (ins C spμ) = ins C (crushForkCtx spμ)
  crushForkAlμ (del C spμ) = del C (crushForkCtx spμ)

  crushForkCtx (here spμ atμs) = here (crush spμ) atμs
  crushForkCtx (there atμ ctx) = there atμ (crushForkCtx ctx)
