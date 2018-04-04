module Generic.Multirec where

open import Prelude
open import Generic.Opaque
  public

-- * We need monadic functionality for Maybe
open import Data.Maybe using (monadPlus)
open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

-- * Sum-of-product universe
-- ** Code

data Atom (n : ℕ) : Set where
  K : (κ : Konst) → Atom n 
  I : (ν : Fin n) → Atom n

Prod : ℕ → Set
Prod = List ∘ Atom

Sum : ℕ → Set
Sum = List ∘ Prod

-- ** Interpretation

open import Relation.Unary
Setⁿ : ℕ → Set₁
Setⁿ n = Pred (Fin n) _

⟦_⟧A : {n : ℕ} → Atom n → Setⁿ n → Set
⟦ K κ ⟧A X = ⟦ κ ⟧K
⟦ I ν ⟧A X = X ν 

⟦_⟧P : {n : ℕ} → Prod n → Setⁿ n → Set
⟦ π ⟧P X = All (λ α → ⟦ α ⟧A X) π

⟦_⟧S : {n : ℕ} → Sum n → Setⁿ n → Set
⟦ σ ⟧S X = Any (λ π → ⟦ π ⟧P X) σ

-- ** Decidable equality

module DecEq {n : ℕ}(Rec : Setⁿ n)(_≟Rec_ : ∀{v}(x y : Rec v) → Dec (x ≡ y)) where

  _≟Atom_ : (α₁ α₂ : Atom n) → Dec (α₁ ≡ α₂)
  I i    ≟Atom I j with i ≟F j
  ...| yes refl = yes refl
  ...| no  ¬p   = no λ { refl → ¬p refl }   
  (K κ₁) ≟Atom (K κ₂) with κ₁ ≟Konst κ₂
  ...| yes refl = yes refl
  ...| no  ¬p  = no λ { refl → ¬p refl }
  I _ ≟Atom (K _) = no λ ()
  (K _) ≟Atom I _ = no λ ()

  _≟A_ :  ∀ {α} → (a₁ a₂ : ⟦ α ⟧A Rec) → Dec (a₁ ≡ a₂)
  _≟A_ {K κ} k₁ k₂ = k₁ ≟K k₂
  _≟A_ {I i} x  y  = x ≟Rec y

  _≟P_ : ∀ {π} → (p₁ p₂ : ⟦ π ⟧P Rec) → Dec (p₁ ≡ p₂)
  _≟P_ {[]} [] [] = yes refl
  _≟P_ {α ∷ π} (a₁ ∷ p₁) (a₂ ∷ p₂) with _≟A_ {α} a₁ a₂
  ... | no ¬p = no (λ { refl → ¬p refl })
  ... | yes refl with p₁ ≟P p₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }

  _≟S_ : ∀ {σ} → (s₁ s₂ : ⟦ σ ⟧S Rec) → Dec (s₁ ≡ s₂)
  _≟S_ {[]} () _
  _≟S_ {π ∷ σ} (here p₁) (here p₂) with p₁ ≟P p₂
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }
  _≟S_ {π ∷ σ} (here p₁) (there s₂) = no λ ()
  _≟S_ {π ∷ σ} (there s₁) (here s₂) = no λ ()
  _≟S_ {π ∷ σ} (there s₁) (there s₂) with s₁ ≟S s₂
  ... | yes refl = yes refl
  ... | no ¬p = no (λ { refl → ¬p refl })

-- ** Sum-of-product view

Constr : {n : ℕ} → Sum n → Set
Constr σ = Fin (length σ)


typeOf : {n : ℕ}(σ : Sum n) → Constr σ → Prod n
typeOf [] ()
typeOf (π ∷ σ) zero = π
typeOf (π ∷ σ) (suc C) = typeOf σ C

inj : {n : ℕ}{σ : Sum n}{X : Setⁿ n} → (C : Constr σ) → ⟦ typeOf σ C ⟧P X → ⟦ σ ⟧S X
inj {σ = []} () _
inj {σ = π ∷ σ} zero p = here p
inj {σ = x ∷ σ} (suc C) p = there (inj C p)

data SOP {n : ℕ}{σ : Sum n}{X : Setⁿ n} : ⟦ σ ⟧S X → Set where
  tag : (C : Constr σ)(p : ⟦ typeOf σ C ⟧P X) → SOP (inj C p)

sop : {n : ℕ}{σ : Sum n}{X : Setⁿ n} → (s : ⟦ σ ⟧S X) → SOP s
sop (here p) = tag zero p
sop (there s) with sop s
... | tag C p = tag (suc C) p

match : {n : ℕ}{σ : Sum n}{X : Setⁿ n}(C : Constr σ)
      → ⟦ σ ⟧S X → Maybe (⟦ typeOf σ C ⟧P X)
match C x with sop x
... | tag C₂ p with C ≟F C₂
... | yes refl = just p
... | no  _    = nothing

-- * Fixpoint

Fam : ℕ → Set
Fam n = Vec (Sum n) n

⟦_⟧F : {n : ℕ} → Fam n → Fin n → Sum n
⟦ φ ⟧F ν = Vec-lookup ν φ 

-- * Easier to type Constr and typeOf

Constr' : {n : ℕ} → Fam n → Fin n → Set
Constr' φ ν = Constr (⟦ φ ⟧F ν)

typeOf' : {n : ℕ}(φ : Fam n)(ν : Fin n) → Constr' φ ν → Prod n
typeOf' φ ν C = typeOf (⟦ φ ⟧F ν) C

data Fix {n : ℕ}(φ : Fam n) : Fin n → Set where
  ⟨_⟩ : ∀{ν} → ⟦ ⟦ φ ⟧F ν ⟧S (Fix φ) → Fix φ ν

unfix : ∀{n ν}{φ : Fam n} → Fix φ ν → ⟦ ⟦ φ ⟧F ν ⟧S (Fix φ)
unfix ⟨ x ⟩ = x

{-# TERMINATING #-}
_≟Fix_ : ∀{n i}{φ : Fam n} → (x y : Fix φ i) → Dec (x ≡ y)
_≟Fix_ {φ = φ} ⟨ sx ⟩ ⟨ sy ⟩ with DecEq._≟S_ (Fix φ) _≟Fix_ sx sy
... | yes refl = yes refl
... | no ¬p = no (λ { refl → ¬p refl })

-- * Paths over a Mutually Recursive Value

module Paths where

  -- A value of (AllBut P prf), for (prf : x ∈ l) is
  -- isomorphic to All P (delete prf l)
  --
  data AllBut {A : Set}(P : A → Set) : {l : List A}{x : A} → x ∈ l → Set where
    here  : ∀{x xs}      → All P xs → AllBut P {x ∷ xs} (here refl)
    there : ∀{x x' xs p} → (hip : P x) → AllBut P {xs} {x'} p → AllBut P {x ∷ xs} (there p)

  fill : ∀{A l x}{P : A → Set} → (prf : x ∈ l) → P x → AllBut P prf → All P l
  fill .(here refl) hip (here rest)   = hip ∷ rest
  fill .(there _) hip   (there px ab) = px ∷ fill _ hip ab

  -- A value of type (∂ φ i j) indicates a path inside
  -- some values of type Fix φ i leading to a subtree of type Fix φ j.
  --
  data ∂ {n : ℕ}(φ : Fam n) : Fin n → Fin n → Set where
    here : ∀{i} → ∂ φ i i
    peel : ∀{i k j}{C : Constr' φ i} 
         → (prf : I k ∈ typeOf' φ i C)
         → AllBut (λ x → ⟦ x ⟧A (Fix φ)) prf  
         → ∂ φ k j 
         → ∂ φ i j 

  select : ∀{n k}{φ : Fam n}{π : Prod n} 
         → I k ∈ π → ⟦ π ⟧P (Fix φ) → Fix φ k
  select (here refl) (p ∷ ps) = p
  select (there prf) (p ∷ ps) = select prf ps

  match-∂ : ∀{n i j}{φ : Fam n} → ∂ φ i j → Fix φ i → Maybe (Fix φ j)
  match-∂ here                    el = just el
  match-∂ (peel {C = C} prf _ rest) ⟨ el ⟩ 
    = match C el >>= match-∂ rest ∘ select prf

  inject-∂ : ∀{n i j}{φ : Fam n} → ∂ φ i j → Fix φ j → Fix φ i
  inject-∂ here el = el
  inject-∂ (peel {C = C} prf els rest) el 
    = ⟨ inj C (fill prf (inject-∂ rest el) els) ⟩

  -- I can envision defining an Alμ with ∂ above.
  --   data Alμ : Fin n → Set where
  --     peel : (del : ∂ φ i j)(ins : ∂ φ j i) → Patch Alμ (⟦ j ⟧F φ) → Alμ i
