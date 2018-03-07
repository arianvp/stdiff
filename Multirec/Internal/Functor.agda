open import Prelude
open import Generic.Multirec

module Multirec.Internal.Functor
           {n : ℕ}
           (Rec : Setⁿ n) 
           (_≟Rec_ : ∀{ν}(x y : Rec ν) → Dec (x ≡ y))
       where

  open DecEq Rec _≟Rec_

  TrivialA : Atom n → Set
  TrivialA α = ⟦ α ⟧A Rec × ⟦ α ⟧A Rec

  TrivialP : Rel (Prod n) _
  TrivialP π₁ π₂ = ⟦ π₁ ⟧P Rec × ⟦ π₂ ⟧P Rec

-- ** Spine

  data S (At : Atom n → Set)(Al : Rel (Prod n) _)(σ : Sum n) : Set where
    Scp : S At Al σ
    Scns : (C : Constr σ)
           (ats : All At (typeOf σ C)) →
           S At Al σ
    Schg : (C₁ C₂ : Constr σ){q : C₁ ≢ C₂}
           (al : Al (typeOf σ C₁) (typeOf σ C₂)) →
           S At Al σ

-- *** Spine application

  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  All-head-map : {A : Set}{l k : A}{ls ks : List A}{P Q : A → Set}
               → (f : P l → Maybe (Q k))(fs : All P ls → Maybe (All Q ks))
               → All P (l ∷ ls) → Maybe (All Q (k ∷ ks))
  All-head-map f fs (x ∷ xs) = _∷_ <$> f x ⊛ fs xs
               
  applySP : {π : Prod n}{At : Atom n → Set}
          → (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec))
          → All At π → ⟦ π ⟧P Rec → Maybe (⟦ π ⟧P Rec)
  applySP         applyAt [] [] = just []
  applySP {α ∷ π} applyAt (at ∷ ats) prod
    = All-head-map (applyAt at) (applySP applyAt ats) prod

  applyS : {σ : Sum n}{At : Atom n → Set}{Al : Rel (Prod n) _}
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
  ... | yes refl = Maybe-map (inj C₁) (applySP applyAt p₁ p₂)

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

  data Al (At : Atom n → Set) : Prod n → Prod n → Set where
    A0 : Al At [] []
    Adel : ∀ {α π₁ π₂} → ⟦ α ⟧A Rec → Al At π₁ π₂ → Al At (α ∷ π₁) π₂
    Ains : ∀ {α π₁ π₂} → ⟦ α ⟧A Rec → Al At π₁ π₂ → Al At π₁ (α ∷ π₂)
    AX : ∀{α π₁ π₂} → At α → Al At π₁ π₂ → Al At (α ∷ π₁) (α ∷ π₂)

-- *** Alignment application

  applyAl : ∀{π₁ π₂ At} → 
           (applyAt : ∀ {α} → At α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)) →
           Al At π₁ π₂ → ⟦ π₁ ⟧P Rec → Maybe (⟦ π₂ ⟧P Rec)
  applyAl applyAt A0 [] = just []
  applyAl applyAt (Ains a' al) p 
    = (a' ∷_) <$> applyAl applyAt al p
  applyAl applyAt (AX at al)   (a ∷ as) 
    = _∷_ <$> applyAt at a ⊛ applyAl applyAt al as
  -- XXX: should we check whether a' == a or ignore this?
  applyAl applyAt (Adel a' al) (a ∷ as) 
    = applyAl applyAt al as

  costAl : ∀{π₁ π₂ At} 
          → (costAt : ∀ {α} → At α → ℕ) 
          → Al At π₁ π₂ → ℕ
  costAl costAt A0 = 0
  costAl costAt (Adel a al) = 1 + costAl costAt al
  costAl costAt (Ains a al) = 1 + costAl costAt al
  costAl costAt (AX at al) = costAt at + costAl costAt al

-- ** Atoms

  data At (PatchRec : Setⁿ n) : Atom n → Set where
    set : ∀ {κ} → TrivialK κ → At PatchRec (K κ)
    fix : ∀ {ν} → PatchRec ν → At PatchRec (I ν)

  applyAt : ∀{α PatchRec} 
          → (applyR : ∀{ν} → PatchRec ν → Rec ν → Maybe (Rec ν)) 
          → At PatchRec α → ⟦ α ⟧A Rec → Maybe (⟦ α ⟧A Rec)
  applyAt applyR (set k₁k₂) k = applyK k₁k₂ k
  applyAt applyR (fix spμ) x = applyR spμ x

  costAt : ∀{α PatchRec}
         → (costR : ∀{ν} → PatchRec ν → ℕ)
         → At PatchRec α → ℕ
  costAt costR (set k₁k₂) = costK k₁k₂
  costAt costR (fix spμ) = costR spμ

-- * Mixing Everything

  applyPatch : ∀{PatchRec}{σ : Sum n}
             → (applyR : ∀{ν} → PatchRec ν → Rec ν → Maybe (Rec ν)) 
             → S (At PatchRec) (Al (At PatchRec)) σ
             → ⟦ σ ⟧S Rec
             → Maybe (⟦ σ ⟧S Rec)
  applyPatch applyR = applyS (applyAt applyR) (applyAl (applyAt applyR))

-- * Some renamings

  Patch : Setⁿ n → Sum n → Set
  Patch PatchRec = S (At PatchRec) (Al (At PatchRec))
