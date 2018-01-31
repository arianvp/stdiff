open import Prelude
open import Generic.Regular

module Regular.Lab.BinTree where

  treeF : Sum
  treeF =
    let leafT = [] in
    let nodeT = K `ℕ ∷ I ∷ I ∷ [] in
    leafT ∷ nodeT ∷ []

  `leaf `node : Constr treeF
  `leaf = zero
  `node = suc zero

  is-node? : ∀ {A} → ⟦ treeF ⟧S A → Bool
  is-node? x with sop x
  ... | tag (suc zero) ls = true
  ... | tag _ ls = false

  tree : Set
  tree = Fix treeF

  leaf : tree
  leaf = ⟨ here [] ⟩

  node : ℕ → tree → tree → tree
  node n l r = ⟨ there (here (n ∷ l ∷ r ∷ [])) ⟩

  mk-t₁ : tree → tree → tree
  mk-t₁ l r = node 10 l r

  mk-t₂ : tree → tree → tree → tree
  mk-t₂ l m r = node 50 (node 40 l m) r

  t₁ : tree
  t₁ = mk-t₁ leaf leaf

  t₂ : tree
  t₂ = mk-t₂ leaf leaf leaf

  postulate
    𝓣₁ 𝓣₂ 𝓣₃ : ⟦ treeF ⟧S tree
  
  open import Regular.Functor tree _≟Fix_ public
  open import Regular.Fixpoint treeF public
  open FixpointApplication

  p1 : Alμ
  p1 = ins `node (there 50 (here (spn (Scns `node (set (10 , 40) ∷ fix (spn Scp) ∷ fix (spn Scp) ∷ []))) (leaf ∷ []))) 

  p2 : Alμ
  p2 = spn (Scns `node (set (10 , 50) ∷ fix (ins `node (there 40 (here (spn Scp) (leaf ∷ [])))) ∷ fix (spn Scp) ∷ []))

  p3 : Alμ
  p3 = spn (Scns `node (set (10 , 50) ∷ fix (ins `node (there 40 (there leaf (here (spn Scp) [])))) ∷ fix (spn Scp) ∷ []))

  p12 : Alμ
  p12 = ins `node (there 50  (here (ins `node (there 40 (here (del `node (there 10 (here (spn Scp) (leaf ∷ [])))) (leaf ∷ [])))) (leaf ∷ [])))
  
  p23 : Alμ
  p23 = ins `node (there 50 (there (node 40 leaf leaf) (here (del `node (there 10 (there leaf (here (spn Scp) [])))) [])))

  all-correct : All (λ P → ⟪ P ⟫μ t₁ ≡ just t₂) (p1 ∷ p2 ∷ p3 ∷ p12 ∷ p23 ∷ [])
  all-correct = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

  open import Regular.Predicates.Domain.Fixpoint treeF public

  all-patches : List Alμ
  all-patches = diffAlμ t₁ t₂

  trees : List tree
  trees = t₁ ∷ mk-t₁ ⟨ 𝓣₁ ⟩ ⟨ 𝓣₂ ⟩ ∷ []

  test : ⟪ p1 ⟫μ (mk-t₁ ⟨ 𝓣₁ ⟩ ⟨ 𝓣₂ ⟩) ≡ just (mk-t₂ ⟨ 𝓣₁ ⟩ ⟨ 𝓣₂ ⟩ leaf)
  test = refl
  
{-
  p12 : Alμ
  p12 = spn
        (Scns (suc (suc zero))
         (set (1 , 1) ∷
          fix (spn Scp) ∷
          fix
          (spn
           (Scns (suc zero)
            (set (2 , 5) ∷ fix (spn Scp) ∷ fix (spn Scp) ∷ [])))
          ∷ fix (spn Scp) ∷ []))
  
  p13 : Alμ
  p13 = spn
        (Scns (suc (suc zero))
        (set (1 , 1) ∷
          fix (spn Scp) ∷
          fix (spn Scp) ∷
          fix
          (spn
          (Schg (suc zero) (suc (suc zero)) {λ ()}
            (AX (set (3 , 3))
            (AX (fix (spn Scp)) (AX (fix (spn Scp)) (Ains ⟨ here [] ⟩ A0))))))
          ∷ []))


  p23 : Alμ
  p23 = spn (Scns (suc (suc zero)) 
             ( (set ((1 , 1))) 
             ∷ fix (spn Scp) 
             ∷ fix (spn (Scns (suc zero) 
                        ( set ((5 , 2)) 
                        ∷ fix (spn Scp)
                        ∷ fix (spn Scp)
                        ∷ [])))
             ∷ fix (spn (Schg (suc zero) (suc (suc zero)) {λ ()}
                   (AX (set (1 , 1)) 
                   (Ains ⟨ here [] ⟩ 
                   (AX (fix (spn Scp)) 
                   (AX (fix (spn Scp)) 
                   A0)))))) 
             ∷ []))
       

  p14 : Alμ
  p14 = del (suc (suc zero))
        (there 1
        (there ⟨ here [] ⟩
          (there ⟨ there (here (2 ∷ ⟨ here [] ⟩ ∷ ⟨ here [] ⟩ ∷ [])) ⟩
          (here (spn Scp) []))))


  open import Regular.ES.Fixpoint treeF
  open import Regular.ES.MemoEnum treeF

  es23 : ES (I ∷ []) (I ∷ [])
  es23 = getDiff (diffT (t₂ ∷ []) (t₃ ∷ []))
-}  
