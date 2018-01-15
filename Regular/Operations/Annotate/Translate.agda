open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.Operations.Annotate.Translate (μσ : Sum) where

  open import Regular.Internal.Functor (Fix μσ) _≟Fix_
  open import Regular.Internal.Fixpoint μσ
  open DecEq (Fix μσ) _≟Fix_

  -- * Datatypes Adapted to receive the annotated fixpoint.

  TrivialAₐ : Atom → Set
  TrivialAₐ α = ⟦ α ⟧A (Fixₐ μσ) × ⟦ α ⟧A (Fixₐ μσ)

  TrivialPₐ : Rel Prod _
  TrivialPₐ π₁ π₂ = ⟦ π₁ ⟧P (Fixₐ μσ) × ⟦ π₂ ⟧P (Fixₐ μσ)

  -- * If a given subtree has no more copies, we can only resort
  --   to Schg to produce a patch; We call this the stiff patch.
  --   In the sense that it completely fixes one element in the
  --   domain and one in the image of the application function.
  --   This is the worst patch to transform an x into a y.
  --
  --   One option would be to fall back to the diff algorithm that enumerates
  --   all possibilities and choose the one with the least cost.
  
  {-# TERMINATING #-}
  stiff : Fix μσ → Fix μσ → Alμ 

  stiffAt : ∀{α}(x y : ⟦ α ⟧A (Fix μσ)) → Atμ α
  stiffAt {K _} x y = set (x , y)
  stiffAt {I}   x y = fix (stiff x y)

  stiffAl : ∀{π₁ π₂} → ⟦ π₁ ⟧P (Fix μσ) → ⟦ π₂ ⟧P (Fix μσ) → Al Atμ π₁ π₂
  stiffAl []       []       = A0
  stiffAl (p ∷ ps) []       = Adel p (stiffAl ps [])
  stiffAl []       (q ∷ qs) = Ains q (stiffAl [] qs)
  stiffAl {α₁ ∷ π₁} {α₂ ∷ π₂} (p ∷ ps) (q ∷ qs)
    with α₁ ≟Atom α₂
  ...| no _     = Ains q (Adel p (stiffAl ps qs))
  ...| yes refl = AX (stiffAt p q) (stiffAl ps qs)

  stiffS : ∀{σ}(x y : ⟦ σ ⟧S (Fix μσ)) → S Atμ (Al Atμ) σ
  stiffS x y with sop x | sop y
  ...| tag Cx Dx | tag Cy Dy with Cx ≟F Cy
  ...| yes refl = Scns Cx (All-map (uncurry stiffAt) (zipd Dx Dy)) 
  ...| no  prf  = Schg Cx Cy {prf} (stiffAl Dx Dy)

  stiff ⟨ x ⟩ ⟨ y ⟩ = spn (stiffS x y)

  -- * Converting two annotated fixpoints into a patch

  -- ** Spine is trivial.
 
  spine : ∀ {σ} → ⟦ σ ⟧S (Fixₐ μσ) → ⟦ σ ⟧S (Fixₐ μσ) 
        → S TrivialAₐ TrivialPₐ σ
  spine s₁ s₂ with fmapS 𝓤 s₁ ≟S fmapS 𝓤 s₂
  ...| yes _ = Scp
  ...| no ¬p  with sop s₁ | sop s₂
  ...| tag C₁ p₁ | tag C₂ p₂ with C₁ ≟F C₂
  ...| yes refl = Scns C₁ (zipd p₁ p₂)
  ...| no ¬q = Schg C₁ C₂ {¬q} (p₁ , p₂)
 
  -- ** Alignment merely follows the annotations on the 'I's

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

  -- * Fixpoints

  -- First we bring in the annotation counter;
  -- We will be favoring the trees that have the most copies
  -- when choosing a context.
  open AnnCounter


  -- When computing contexts, it makes a difference whether we are
  -- deleting or inserting only for choosing the order of arguments
  -- to 'diffAlμ'.
  data CtxInsDel : Set where
    CtxIns CtxDel : CtxInsDel


  -- Now, the diffCtx function will receive a proof that there is
  -- at least one copy annotation in the product we are looking for
  -- a context into. We will choose the tree that has the most copies
  -- to be the 'here' tree. 
  {-# TERMINATING #-}
  diffCtx : ∀ {π} → CtxInsDel → Fixₐ μσ → (z : ⟦ π ⟧P (Fixₐ μσ)) 
          → 1 ≤ count-C*-sum z → Ctx π
  diffAlμ : Fixₐ μσ → Fixₐ μσ → Alμ

  diffAtμ : ∀{α} → ⟦ α ⟧A (Fixₐ μσ) → ⟦ α ⟧A (Fixₐ μσ) → Atμ α
  diffAtμ {K κ} x y = set (x , y)
  diffAtμ {I}   x y = fix (diffAlμ x y)

  -- Some auxiliary lemmas follow; I somehow feel I'd like to change
  -- these (1 ≤) to a simpler NonZero predicate.
  ≤-monotone-r : ∀{m n o} → m ≤ n → m ≤ n + o
  ≤-monotone-r z≤n     = z≤n
  ≤-monotone-r (s≤s r) = s≤s (≤-monotone-r r)

  private
    aux-lemma-1 : ∀{m n o} → 1 ≤ m + (n + o) → ¬ (m ≤ n) → 1 ≤ m + o
    aux-lemma-1 {zero} hipa hipb = ⊥-elim (hipb z≤n)
    aux-lemma-1 {suc m} hipa hipb = s≤s z≤n

    aux-lemma-2 : ∀{m n} → 1 ≤ m + n → m ≤ n → 1 ≤ n
    aux-lemma-2 1≤m+n z≤n       = 1≤m+n
    aux-lemma-2 1≤m+n (s≤s m≤n) = s≤s z≤n

  Ctx-swap : ∀{α α' π} → Ctx (α' ∷ α ∷ π) → Ctx (α ∷ α' ∷ π)
  Ctx-swap (here spμ (a ∷ p))     = there a (here spμ p)
  Ctx-swap (there a (there a' δ)) = there a' (there a δ)
  Ctx-swap (there a (here spμ r)) = here spμ (a ∷ r)

  diffAlμDI : CtxInsDel → (x y : Fixₐ μσ) → Alμ
  diffAlμDI CtxDel x y = diffAlμ y x
  diffAlμDI CtxIns x y = diffAlμ x y

  -- Now, diffCtx is a hack. We were using a single definition
  -- to facilitate proofs. Turns out the proofs were still
  -- pretty complex (branch es-to-tree-proof-3-nonzero).
  --
  -- Nevertheless, an simpler spec for diffCtx is:
  --
  -- diffCtx cid x ats = let idx = max (map count-CA ats)
  --                      in diffCtxIdx cid idx x ats
  --
  -- diffCtxIdx cid n x (at₁ ∷ at₂ ∷ ⋯ ∷ atₙ ∷ ats)
  --   = there at₁ (⋯ (here (diffAlμDI cid x atₙ) ats))
  -- 
  -- In the implementation below, we force the
  -- product to be non-empty and use the first atom
  -- in the procut as an auxiliary value, where
  -- we store the local maximum under count-CA.
  diffCtx            cid x₁ [] ()
  diffCtx {K _ ∷ []} cid x₁ (at ∷ []) ()
  diffCtx {I   ∷ []} cid x₁ (at ∷ []) hip 
    = here (diffAlμDI cid x₁ at) []
  diffCtx {α ∷ α' ∷ π}  cid x₁ (at ∷ at' ∷ ats) hip 
    with count-CA {μσ} {α} at ≤? count-CA {μσ} {α'} at'
  ...| yes at≤at' 
     = there (fmapA {α} 𝓤 at) 
             (diffCtx cid x₁ (at' ∷ ats) 
                   (aux-lemma-2 
                       {count-CA {μσ} {α} at} 
                       {count-CA {μσ} {α'} at' + count-C*-sum ats}
                       hip (≤-monotone-r at≤at')))
  ...| no  at≰at' 
     = Ctx-swap (there 
             (fmapA {α'} 𝓤 at') 
             (diffCtx cid x₁ (at ∷ ats) 
                  (aux-lemma-1 
                     {m = count-CA {μσ} {α} at} 
                     {n = count-CA {μσ} {α'} at'} 
                     hip at≰at') ))

  diffS : ∀{σ}(s₁ s₂ : ⟦ σ ⟧S (Fixₐ μσ)) → Patch Alμ σ
  diffS s₁ s₂ = S-map (uncurry diffAtμ) (al-map (uncurry diffAtμ) ∘ uncurry align)
                      (spine s₁ s₂)

  diff-del : (z : ⟦ μσ ⟧S (Fixₐ μσ)) → Fixₐ μσ → 1 ≤ count-CS z → Alμ
  diff-ins : Fixₐ μσ → (z : ⟦ μσ ⟧S (Fixₐ μσ)) → 1 ≤ count-CS z → Alμ

  -- Runs a given computation if a tree has some copy annotations;
  -- keeps a proof of that handy.
  if-has-copies 
    : ∀{a}{A : Set a}(z : ⟦ μσ ⟧S (Fixₐ μσ))
    → (1 ≤ count-CS z → A)
    → (0 ≡ count-CS z → A)
    → A
  if-has-copies z th el with count-CS z | inspect count-CS z
  ...| zero   | [ CZ ] = el refl
  ...| suc cz | [ CZ ] = th (s≤s z≤n)

  diffAlμ ⟨ M , x ⟩ ⟨ M , y ⟩ 
    = if-has-copies x 
         (diff-del x ⟨ M , y ⟩) 
         (λ prf → stiff ⟨ fmapS 𝓤 x ⟩ ⟨ fmapS 𝓤 y ⟩)
  diffAlμ ⟨ M , x ⟩ ⟨ C , y ⟩ 
    = if-has-copies x 
         (diff-del x ⟨ C , y ⟩) 
         (λ prf → stiff ⟨ fmapS 𝓤 x ⟩ ⟨ fmapS 𝓤 y ⟩)
  diffAlμ ⟨ C , x ⟩ ⟨ M  , y ⟩ 
    = if-has-copies y 
         (diff-ins ⟨ C , x ⟩ y) 
         (λ prf → stiff ⟨ fmapS 𝓤 x ⟩ ⟨ fmapS 𝓤 y ⟩)
  diffAlμ ⟨ C , x ⟩ ⟨ C  , y ⟩ 
    = spn (diffS x y)

  diff-del s₁ x₂ hip with sop s₁
  ...| tag C₁ p₁ 
     = del C₁ (diffCtx CtxDel x₂ p₁ 
                (subst (λ P → 1 ≤ P) (count-CS≡C*-lemma {μσ} C₁ p₁) hip))

  diff-ins x₁ s₂ hip with sop s₂
  ...| tag C₂ p₂ 
     = ins C₂ (diffCtx CtxIns x₁ p₂ 
                (subst (λ P → 1 ≤ P) (count-CS≡C*-lemma {μσ} C₂ p₂) hip)) 
