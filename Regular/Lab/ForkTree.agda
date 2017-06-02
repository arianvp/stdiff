open import Prelude
open import Generic.Regular

module Regular.Lab.ForkTree where

  ForkTreeF : Sum
  ForkTreeF = (I ∷ I ∷ [])
            ∷ (K `ℕ ∷ [])
            ∷ []

  `fork `leaf : Constr ForkTreeF
  `fork = zero
  `leaf = suc zero

  ForkTree : Set
  ForkTree = Fix ForkTreeF

  leaf : ℕ → ForkTree
  leaf x = ⟨ inj `leaf (x ∷ []) ⟩

  fork : ForkTree → ForkTree → ForkTree
  fork l r = ⟨ inj `fork (l ∷ r ∷ []) ⟩

  forkXY : ℕ → ℕ → ForkTree
  forkXY x y = fork (leaf x) (leaf y)

  t₁ t₂ t₃ t₄ : ForkTree
  
  t₁ = fork (forkXY 1 2) (forkXY 3 4)

  t₂ = fork (forkXY 3 2) (forkXY 3 4)
  
  t₃ = fork (forkXY 1 2) (forkXY 5 4)

  t₄ = forkXY 1 2

  open import Regular.Functor ForkTree _≟Fix_ public
  open import Regular.Fixpoint ForkTreeF public
  
  p12 : Alμ
  p12 = spn
        (Scns zero
        (fix
          (spn
          (Scns zero
            (fix (spn (Scns (suc zero) (set (1 , 3) ∷ []))) ∷
            fix (spn Scp) ∷ [])))
          ∷ fix (spn Scp) ∷ []))

  p13 : Alμ 
  p13 = spn
        (Scns zero
        (fix (spn Scp) ∷
          fix
          (spn
          (Scns zero
            (fix (spn (Scns (suc zero) (set (3 , 5) ∷ []))) ∷
            fix (spn Scp) ∷ [])))
          ∷ []))

  p14 : Alμ 
  p14 = del zero
        (here (spn Scp)
        (⟨
          here (⟨ there (here (3 ∷ [])) ⟩ ∷ ⟨ there (here (4 ∷ [])) ⟩ ∷ []) ⟩
          ∷ []))

  open import Regular.Predicates.Disjoint.Fixpoint ForkTreeF public
  open import Regular.Predicates.Disjoint.Merge.Fixpoint ForkTreeF public

  lemma123 : disjAlμ p12 p13
  lemma123 = refl , (unit , (unit , unit))

  lemma124 : disjAlμ p12 p14
  lemma124 = refl , (unit , unit , unit)

  
