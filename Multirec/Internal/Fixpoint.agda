open import Prelude
open import Generic.Multirec

module Multirec.Internal.Fixpoint {n : ℕ}(φ : Fam n) where

  open DecEq (Fix φ) _≟Fix_
  open import Multirec.Internal.Functor (Fix φ) _≟Fix_
  
  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)


  -- XXX: This looks like a derivative, and should be one.
  --
  -- OneOn P Qs [l₁ , ... , lₙ] ≡ [Qs l₁ , ... , Qs lᵢ₋₁ , P lᵢ , Qs lᵢ₊₁ , ... , Qs lₙ ]
{-

  oneon-fold : {A : Set}{P Qs : A → Set}{B : List A → Set}
             → (∀{x xs} → P x → B xs → B (x ∷ xs))
             → (∀{x xs} → Qs x → B xs → B (x ∷ xs))
             → B []
             → {l : List A} → OneOn P Qs l → B l
  oneon-fold {A} {P} {Qs} f g nil (here px qxs) 
    = f px (all-foldr {P = Qs} (λ {x} {xs} → g {x} {xs}) nil qxs)
  oneon-fold {A} {P} {Qs} f g nil (there qx pqxs) 
    = g qx (oneon-fold {A} {P} {Qs} f (λ {x} {xs} → g {x} {xs}) nil pqxs)

  oneon-map : {A : Set}{P₁ P₂ Qs₁ Qs₂ : A → Set}
            → (f : ∀{x} → P₁ x → P₂ x)(g : ∀{x} → Qs₁ x → Qs₂ x){l : List A}
            → OneOn P₁ Qs₁ l → OneOn P₂ Qs₂ l
  oneon-map fP fQs (here px qxs) = here (fP px) (mapᵢ fQs qxs)
  oneon-map fP fQs (there qx pqxs) = there (fQs qx) (oneon-map fP fQs pqxs)

  oneon-all : {A : Set}{P Qs : A → Set}{l : List A}
            → (∀{a} → P a → Maybe (Qs a))
            → OneOn P Qs l → Maybe (All Qs l)
  oneon-all f (here x xs) = Data.Maybe.map (_∷ xs) (f x)
  oneon-all f (there x xs) = Data.Maybe.map (x ∷_) (oneon-all f xs)

  fetch : {A : Set}{P Qs X : A → Set}{l : List A}
        → OneOn P Qs l → All X l → ∃ (λ lᵢ → P lᵢ × X lᵢ) 
  fetch (here {x} px _)  (xx ∷ _) = x , px , xx
  fetch (there _ xs) (_ ∷ xss) = fetch xs xss
-- ** Universe

  data Alμ : Fin n → Fin n → Set

  data Atμ+ (v₁ : Fin n) : Atom n → Set
  data Atμ- (v₂ : Fin n) : Atom n → Set

  data OneOn {X : Set}(P Qs : X → Set) : List X → Set where
    here  : ∀{x xs} → P x  → All Qs xs     → OneOn P Qs (x ∷ xs)
    there : ∀{x xs} → Qs x → OneOn P Qs xs → OneOn P Qs (x ∷ xs)

  Ctx : (Atom n → Set) → Prod n → Set 
  Ctx P l = OneOn P (λ α → ⟦ α ⟧A Rec) l 

  Alμₕ : Fin n → Set
  Alμₕ v = Alμ v v

  data Alμ where
    spn : ∀{v}(sp : S (At Alμₕ) (Al (At Alμₕ)) (Ty v)) → Alμ v v
    ins : ∀{v₁ v₂}(C : Constr (Ty v₂))
        → (∂ : Ctx (Atμ+ v₁) (typeOf (Ty v₂) C)) 
        → Alμ v₁ v₂
    del : ∀{v₁ v₂}(C : Constr (Ty v₁))
        → (∂ : Ctx (Atμ- v₂) (typeOf (Ty v₁) C)) 
        → Alμ v₁ v₂

  data Atμ+ (v₁ : Fin n) where
    fix : ∀ {v₂} → Alμ v₁ v₂  → Atμ+ v₁ (I v₂)

  data Atμ- (v₂ : Fin n) where
    fix : ∀ {v₁} → Alμ v₁ v₂  → Atμ- v₂ (I v₁)

-- ** Interpretation

  -- XXX: write in monadic style

  {-# TERMINATING #-}
  applyAlμ    : ∀{v₁ v₂} → Alμ v₁ v₂ → Rec v₁ → Maybe (Rec v₂)
  applyAtAlμₕ : ∀{α}     → At Alμₕ α → ⟦ α ⟧A (Fix φ) → Maybe (⟦ α ⟧A (Fix φ))
  applyAtμ+   : ∀{v α}   → Atμ+ v α  → ⟦ I v ⟧A Rec → Maybe (⟦ α ⟧A Rec)
  applyAtμ-   : ∀{v α}   → Atμ- v α → ⟦ α ⟧A Rec → Maybe (⟦ I v ⟧A Rec)

  applyAtAlμₕ = applyAt applyAlμ

  applyAlμ (spn s)   ⟨ x ⟩
    = Data.Maybe.map ⟨_⟩ (applyS applyAtAlμₕ (applyAl applyAtAlμₕ) s x)
  applyAlμ (ins C ∂) x 
    = Data.Maybe.map (⟨_⟩ ∘ inj C) (oneon-all (λ p → applyAtμ+ p x) ∂)
  applyAlμ (del C ∂) ⟨ x ⟩ with match C x
  ...| nothing = nothing
  ...| just dx with fetch ∂ dx
  ...| α , atμ- , a = applyAtμ- atμ- a

  applyAtμ+ (fix alμ) x = applyAlμ alμ x
  applyAtμ- (fix alμ) x = applyAlμ alμ x


-- ** Cost semantics

  {-# TERMINATING #-}
  costAlμ  : ∀{v₁ v₂} → Alμ v₁ v₂ → ℕ
  costAtμ+ : ∀{v α} → Atμ+ v α → ℕ
  costAtμ- : ∀{v α} → Atμ- v α → ℕ

  costAlμ (spn sp) = costS (costAt costAlμ) (costAl (costAt costAlμ)) sp
  costAlμ (ins C ∂) = oneon-fold (λ x → costAtμ+ x +_) (λ _ → suc) 0 ∂
  costAlμ (del C ∂) = oneon-fold (λ x → costAtμ- x +_) (λ _ → suc) 0 ∂

  costAtμ+ (fix alμ) = costAlμ alμ 
  costAtμ- (fix alμ) = costAlμ alμ

-- ** Aliasses

  Patch : Fin n → Set
  Patch = Alμₕ

  apply : ∀{v} → Patch v → Rec v → Maybe (Rec v)
  apply = applyAlμ

  cost : ∀{v} → Patch v → ℕ
  cost = costAlμ
-}


  data Alμ : Fin n → Fin n → Set

  Alμᵒ : Fin n → Fin n → Set
  Alμᵒ ν₂ ν₁ = Alμ ν₁ ν₂

  Alμ↓ : Fin n → Set
  Alμ↓ ν = Alμ ν ν

  data Ctx (P : Fin n → Set) : Prod n → Set where
    here  : ∀{ν π}(spμ : P ν)(atμs : All (λ α → ⟦ α ⟧A (Fix φ)) π) 
          → Ctx P (I ν ∷ π)
    there : ∀{α π}(atμ : ⟦ α ⟧A (Fix φ))(alμs : Ctx P π) 
          → Ctx P (α ∷ π)

  data Alμ where
    spn : ∀{ν}(sp : Patch Alμ↓ (⟦ φ ⟧F ν)) → Alμ ν ν
    ins : ∀{ν₁ ν₂}(C : Constr' φ ν₂)
                  (spμ : Ctx (Alμ ν₁) (typeOf' φ ν₂ C)) → Alμ ν₁ ν₂
    del : ∀{ν₁ ν₂}(C : Constr' φ ν₁)
                  (spμ : Ctx (Alμᵒ ν₂) (typeOf' φ ν₁ C)) → Alμ ν₁ ν₂

{-
  getCtx : ∀{π} → Ctx π → Alμ
  getCtx (there _ ctx) = getCtx ctx
  getCtx (here res _)  = res

  selectP : ∀{π} → ⟦ π ⟧P (Fix φ) → Ctx π → Fix φ
  selectP [] ()
  selectP (p ∷ ps) (here _ _)  = p
  selectP (p ∷ ps) (there _ c) = selectP ps c

  selectA : ∀{π}(atμs : All Atμ π)(ctx : Ctx π) → Alμ
  selectA [] ()
  selectA (fix x ∷ _) (here _ _) = x
  selectA (_ ∷ as) (there _ ctx) = selectA as ctx
-}

-- ** Interpretation

  {-# TERMINATING #-}
  applyAlμ : ∀{ν₁ ν₂} → Alμ ν₁ ν₂ → Fix φ ν₁ → Maybe (Fix φ ν₂)
{-
  inCtx : ∀ {π P}(applyP : ∀{ν} → P ν → Fix φ ν → Maybe (Fix φ ν))
        → Ctx P π → Fix φ  → Maybe (⟦ π ⟧P (Fix φ))
  matchCtx : ∀ {π} → Ctx π → ⟦ π ⟧P (Fix φ) → Maybe (Fix φ)
-}

  insCtx : ∀{π P}(f : ∀{ν} → P ν → Maybe (Fix φ ν))
         → Ctx P π → Maybe (⟦ π ⟧P (Fix φ))

  delCtx : ∀{π P ν₁ ν₂}(f : P ν₁ → Maybe (Fix φ ν₂))
         → Ctx P π → ⟦ π ⟧P (Fix φ) → Maybe (Fix φ ν₂)

  applyAlμ (spn sp) x = Maybe-map ⟨_⟩ (applyPatch applyAlμ sp (unfix x))
  applyAlμ (ins C alμ) x = Maybe-map (⟨_⟩ ∘ inj C) (insCtx (λ k → applyAlμ k x) alμ)
  applyAlμ (del C alμ) x = (delCtx {!!} alμ ∙ match C) (unfix x)
  
  insCtx f (here spμ atμs) = Maybe-map (_∷ atμs) (f spμ)
  insCtx f (there atμ ctx) = Maybe-map (atμ ∷_) (insCtx f ctx)

  delCtx f (here spμ atμs) (x ∷ xs) = {!!}
  delCtx f (there atμ ctx) (x ∷ xs) = {!!}
{-
  inCtx (here spμ atμs) x = Maybe-map (λ x → x ∷ atμs) (applyAlμ spμ x)
  inCtx (there atμ al) x = Maybe-map (λ ats → atμ ∷ ats) (inCtx al x)

  matchCtx (here spμ atμs) (x ∷ p) = applyAlμ spμ x 
  matchCtx (there {α} atμ al) (at ∷ p) = matchCtx al p
  
  applyAtμ = applyAt applyAlμ 
-}
-- ** Cost semantics
{-
  {-# TERMINATING #-}
  costAlμ : Alμ → ℕ
  costAtμ : ∀{α} → Atμ α → ℕ
  costCtx : ∀{π} → Ctx π → ℕ

  costAlμ (spn sp) = costS costAtμ (costAl costAtμ) sp
  costAlμ (ins C al) = costCtx al
  costAlμ (del C al) = costCtx al

  costCtx {π} (here spμ atμs) = costAlμ spμ + length π
  costCtx     (there atμ alμ) = 1 + costCtx alμ

  costAtμ = costAt costAlμ

-- ** Aliasses

  Patchμ : Set
  Patchμ = Alμ

  applyμ : Patchμ → Fix φ → Maybe (Fix φ)
  applyμ = applyAlμ

  costμ : Patchμ → ℕ
  costμ = costAlμ
-}

