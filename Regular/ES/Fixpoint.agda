open import Prelude
open import Generic.Regular

module Regular.ES.Fixpoint (σμ : Sum) where

  open import Data.List using (_++_)
  open DecEq (Fix σμ) _≟Fix_
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  -- Encoding patches a-la Lempsink
  -- 
  -- We shall be diffing lists of atoms
 
  -- Constructors Of an atom are either the constructors
  -- of the fixpoint in question or opaque types
  --  
  cof : Atom → Set
  cof I     = Constr σμ
  cof (K κ) = ⟦ κ ⟧K

  -- The Type Of an atom is either the type of
  -- a constructor or empty.
  tyof : (α : Atom) → cof α → Prod
  tyof I     c = typeOf σμ c
  tyof (K κ) c = []

  -- we also provide a handy injection function
  -- to construct elements
  inj' : {α : Atom}(c : cof α) → ⟦ tyof α c ⟧P (Fix σμ) → ⟦ α ⟧A (Fix σμ)
  inj' {K κ} c xs = c
  inj' {I}   c xs = ⟨ inj c xs ⟩

  match' : {α : Atom}(c : cof α) → ⟦ α ⟧A (Fix σμ) 
         → Maybe (⟦ tyof α c ⟧P (Fix σμ))
  match' {K κ} c x 
    with c ≟K x
  ...| no  _ = nothing
  ...| yes _ = just []
  match' {I} c ⟨ x ⟩ with sop x
  ...| tag cx dx with c ≟F cx
  ...| yes refl = just dx
  ...| no  _    = nothing


  -- Edit-scripts a-la Lempsink are defined
  -- by:
  data ES : List Atom → List Atom → Set where
    nil : ES [] []
    ins : {i j : List Atom}{α : Atom}(c : cof α)
        → ES i (tyof α c ++ j)
        → ES i (α ∷ j)
    del : {i j : List Atom}{α : Atom}(c : cof α)
        → ES (tyof α c ++ i) j
        → ES (α ∷ i) j
    cpy : {i j : List Atom}{α : Atom}(c : cof α)
        → ES (tyof α c ++ i) (tyof α c ++ j)
        → ES (α ∷ i) (α ∷ j)

  -- The cost semantics, as in their paper, is given by: 
  cost : ∀{txs tys} → ES txs tys → ℕ
  cost nil        = 0
  cost (ins c es) = 1 + cost es
  cost (del c es) = 1 + cost es
  cost (cpy c es) = cost es

  _⊓_ : ∀{txs tys} → ES txs tys → ES txs tys → ES txs tys
  d₁ ⊓ d₂ with cost d₁ ≤? cost d₂
  ...| yes _ = d₁
  ...| no  _ = d₂

  -- Handy synonym;
  ⟦_⟧A* : List Atom → Set
  ⟦_⟧A* = All (λ α → ⟦ α ⟧A (Fix σμ))

  -- Some 'sop' functionality to ease our life:
  sop' : {α : Atom} → ⟦ α ⟧A (Fix σμ) → Σ (cof α) (⟦_⟧A* ∘ tyof α)
  sop' {K κ} k   = k , []
  sop' {I} ⟨ x ⟩ with sop x
  ...| tag cx dx = cx , dx

  split-all : ∀{a}{A : Set a}{P : A → Set}(l l' : List A)
            → All P (l ++ l') → All P l × All P l'
  split-all []       l' xs = [] , xs
  split-all (l ∷ ls) l' (x ∷ xs)
    = let xs₀ , xs₁ = split-all ls l' xs
       in (x ∷ xs₀) , xs₁

  ++-all : ∀{a}{A : Set a}{P : A → Set}(l l' : List A)
         → All P l → All P l' → All P (l ++ l')
  ++-all _ l' []       xs' = xs'
  ++-all _ l' (x ∷ xs) xs' = x ∷ ++-all _ l' xs xs'

  -- * We can apply these
  ins* : ∀{α αs}(c : cof α) → ⟦ tyof α c ++ αs ⟧A* → ⟦ α ∷ αs ⟧A*
  ins* {α} {αs} c xs 
    = let (xs₀ , xs₁) = split-all (tyof α c) αs xs
       in inj' {α} c xs₀ ∷ xs₁

  del* : ∀{α αs}(c : cof α) → ⟦ α ∷ αs ⟧A* → Maybe ⟦ tyof α c ++ αs ⟧A*
  del* {α} {αs} c (x ∷ xs) with match' {α} c x
  ...| nothing = nothing
  ...| just dx = just (++-all (tyof α c) αs dx xs)

  applyES : ∀{txs tys} → ES txs tys → ⟦ txs ⟧A* → Maybe ⟦ tys ⟧A*
  applyES nil        [] = just []
  applyES (ins c es) xs = ins* c <$> applyES es xs
  applyES (del c es) xs = del* c xs >>= applyES es
  applyES (cpy c es) xs = ins* c <$> (del* c xs >>= applyES es)

