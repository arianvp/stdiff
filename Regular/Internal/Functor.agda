open import Prelude
open import Generic.Regular

module Regular.Internal.Functor
           (Rec : Set)
           (_≟Rec_ : (⟨x⟩ ⟨y⟩ : Rec) → Dec (⟨x⟩ ≡ ⟨y⟩))
       where

  open DecEq Rec _≟Rec_

  TrivialA : Atom → Set
  TrivialA α = ⟦ α ⟧A Rec × ⟦ α ⟧A Rec

  TrivialP : Rel Prod _
  TrivialP π₁ π₂ = ⟦ π₁ ⟧P Rec × ⟦ π₂ ⟧P Rec

-- ** Spine

  data S (At : Atom → Set)(Al : Rel Prod _)(σ : Sum) : Set where
    Scp : S At Al σ
    Scns : (C : Constr σ)
           (ats : All At (typeOf σ C)) →
           S At Al σ
    Schg : (C₁ C₂ : Constr σ){q : C₁ ≢ C₂}
           (al : Al (typeOf σ C₁) (typeOf σ C₂)) →
           S At Al σ

-- *** Spine application

  applyS : {σ : Sum}{At : Atom → Set}{Al : Rel Prod _}
        → (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec))
        → (applyAl : ∀ {π₁ π₂} → Al π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)) 
        → S At Al σ → ⟦ σ ⟧S Rec → Maybe (⟦ σ ⟧S Rec)
  applyS applyAt applyAl Scp s = just s
  applyS applyAt applyAl (Schg C₁ C₂ p) s with sop s
  ... | tag C₃ p₃ with C₁ ≟F C₃
  ... | yes refl = Maybe-map (inj C₂) (applyAl p p₃)
  ... | no ¬p = nothing
  applyS {At = At} applyAt applyAl (Scns C₁ p₁) s with sop s
  ... | tag C₂ p₂ with C₁ ≟F C₂
  ... | no ¬p = nothing
  ... | yes refl = Maybe-map (inj C₁) (applySP p₁ p₂)
    where applySP : {π : Prod}
                  → All At π → ⟦ π ⟧P Rec → Maybe (⟦ π ⟧P Rec)
          applySP [] [] = just []
          applySP {α ∷ π} (at ∷ ats) (a₁ ∷ as₁) 
            with applyAt at a₁ | applySP ats as₁
          ...| just a₂ | just as₂ = just (a₂ ∷ as₂)
          ...| _       | _        = nothing

-- *** Spine cost

  costS : ∀ {σ At Al}
          (costAt : ∀{α} → At α → ℕ)
          (costAl : ∀ {π₁ π₂} → Al π₁ π₂ → ℕ) 
        → S At Al σ → ℕ
  costS costAt costAl Scp = 0
  costS {At = At} costAt costAl (Scns C p) = All-sum p
    where All-sum : ∀ {π} → All At π → ℕ
          All-sum {[]} [] = 0
          All-sum {α ∷ π} (a ∷ p) = costAt a + All-sum p
  costS costAt costAl (Schg C₁ C₂ p) = costAl p

-- ** Alignment

  data Al (At : Atom → Set) : Prod → Prod → Set where
    A0 : Al At [] []
    Adel : ∀ {α π₁ π₂} → ⟦ α ⟧A Rec → Al At π₁ π₂ → Al At (α ∷ π₁) π₂
    Ains : ∀ {α π₁ π₂} → ⟦ α ⟧A Rec → Al At π₁ π₂ → Al At π₁ (α ∷ π₂)
    AX : ∀{α π₁ π₂} → At α → Al At π₁ π₂ → Al At (α ∷ π₁) (α ∷ π₂)

-- *** Alignment application

  -- XXX: write in monadic style
  applyAl : ∀{π₁ π₂ At} → 
           (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)) →
           Al At π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)
  applyAl applyAt A0 [] = just []
  applyAl applyAt (AX at al) (a₁ ∷ as₁) with applyAt at a₁ | applyAl applyAt al as₁
  ... | just a₂ | just as₂ = just (a₂ ∷ as₂)
  ... | _ | _ = nothing
  applyAl applyAt (Ains a al) p₁ with applyAl applyAt al p₁
  ... | just p₂ = just (a ∷ p₂)
  ... | nothing = nothing
  applyAl applyAt (Adel {α} a₁ al) (a₂ ∷ p) with _≟A_ {α} a₁ a₂
  ... | yes refl = applyAl applyAt al p
  ... | no ¬p = nothing

-- *** Alignment cost

  costAl : ∀{π₁ π₂ At} 
          → (costAt : ∀ {α} → At α → ℕ) 
          → Al At π₁ π₂ → ℕ
  costAl costAt A0 = 0
  costAl costAt (Adel a al) = 1 + costAl costAt al
  costAl costAt (Ains a al) = 1 + costAl costAt al
  costAl costAt (AX at al) = costAt at + costAl costAt al

-- ** Atoms

  data At (PatchRec : Set) : Atom → Set where
    set : ∀ {κ} → TrivialK κ → At PatchRec (K κ)
    fix : PatchRec → At PatchRec I

  applyAt : ∀{α PatchRec} 
          → (applyR : PatchRec → Rec → Maybe Rec) 
          → At PatchRec α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)
  applyAt applyR (set k₁k₂) k = applyK k₁k₂ k
  applyAt applyR (fix spμ) x = applyR spμ x

  costAt : ∀{α PatchRec}
         → (costR : PatchRec → ℕ)
         → At PatchRec α → ℕ
  costAt costR (set k₁k₂) = costK k₁k₂
  costAt costR (fix spμ) = costR spμ

