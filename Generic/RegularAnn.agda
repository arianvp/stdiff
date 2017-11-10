-- Annotated version of our regular types;
-- The annotations consists in a insert, delete or copy flag
-- on each constructor of a value.
module Generic.RegularAnn where

open import Prelude
open import Generic.Regular
open import Generic.Opaque

-- An annotation represents either a moving part,
-- or a copied part. A moving part in the source represents
-- a deletion whereas a moving part in the destinationa
-- represents a insertion
data Ann : Set where
  M C : Ann

⟦_⟧Sₐ : Sum → Set → Set
⟦ σ ⟧Sₐ X = Ann × ⟦ σ ⟧S X

fmapSₐ : ∀{σ X Y} → (X → Y) → ⟦ σ ⟧Sₐ X → ⟦ σ ⟧Sₐ Y
fmapSₐ f (ann , x) = ann , fmapS f x

data Fixₐ (σ : Sum) : Set where
  ⟨_⟩ : ⟦ σ ⟧Sₐ (Fixₐ σ) → Fixₐ σ 

{-# TERMINATING #-}
𝓤 : ∀{σ} → Fixₐ σ → Fix σ
𝓤 ⟨ _ , x ⟩ = ⟨ fmapS 𝓤 x ⟩

unfixₐ : {σ : Sum} → Fixₐ σ → ⟦ σ ⟧Sₐ (Fixₐ σ)
unfixₐ ⟨ ann , x ⟩ = ann , x

{-# TERMINATING #-}
cataₐ : ∀{σ A} → (⟦ σ ⟧Sₐ A → A) → Fixₐ σ → A
cataₐ f = f ∘ fmapSₐ (cataₐ f) ∘ unfixₐ

-- Handy projection
extractAnn : ∀{σ} → ⟦ I ⟧A (Fixₐ σ) → Ann
extractAnn ⟨ a , _ ⟩ = a

-- ** Annotation Counter
--
--    Ideally, we'd keep this data with the annotations themselves,
--    as we don't want to keep recalculating things.
--    For modelling, however, we have the burden of proof;
--    it's easier to recalculate these monsters and produce proofs
--    then to keep carrying proofs around.
--    
--    Moreover, here we can focus on the method.

{-
record AnnCounter : Set where
  constructor _,_
  field
    count-C : ℕ
    count-M : ℕ

open AnnCounter

0ₐ : AnnCounter
0ₐ = 0 , 0

count1 : Ann → AnnCounter
count1 C = 1 , 0
count1 M = 0 , 1

infixr 6 _+ₐ_
_+ₐ_ : AnnCounter → AnnCounter → AnnCounter 
(c₁ , m₁) +ₐ (c₂ , m₂) = (c₁ + c₂ , m₁ + m₂)

-- * Monoidal structure

postulate
  theMagic : ∀{a}{A : Set a} → A

+ₐ-isSemigroup : IsSemigroup _≡_ _+ₐ_
+ₐ-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = theMagic
  ; ∙-cong        = cong₂ _+ₐ_
  }

+ₐ-semigroup : Semigroup _ _
+ₐ-semigroup = record { isSemigroup = +ₐ-isSemigroup }

+ₐ-0ₐ-isCommutativeMonoid : IsCommutativeMonoid _≡_ _+ₐ_ 0ₐ
+ₐ-0ₐ-isCommutativeMonoid = record
  { isSemigroup = +ₐ-isSemigroup
  ; identityˡ   = theMagic
  ; comm        = theMagic
  }

+ₐ-0ₐ-monoid : Monoid _ _
+ₐ-0ₐ-monoid = record { isMonoid = IsCommutativeMonoid.isMonoid +ₐ-0ₐ-isCommutativeMonoid }

+ₐ-0ₐ-commutativeMonoid : CommutativeMonoid _ _
+ₐ-0ₐ-commutativeMonoid = record { isCommutativeMonoid = +ₐ-0ₐ-isCommutativeMonoid }

-- * Computing Annotation Counters from generic trees.

open RegularConsume +ₐ-0ₐ-monoid

-- We can count all the M's and C's in a tree
count : ∀{σ} → Fixₐ σ → AnnCounter
count = cataₐ gene
  where
    gene : ∀{σ} → ⟦ σ ⟧Sₐ AnnCounter → AnnCounter
    gene (ann , s) = count1 ann +ₐ consumeS s

-- Or we can count all the M's and C's in the underlying trees.
count* : ∀{σ} → ⟦ σ ⟧S (Fixₐ σ) → List AnnCounter
count* {σ} x with sop x
...| tag Cx Dx = all-foldr (λ {α} a xs → gene {σ} {α} a ∷ xs) [] Dx
  where
    gene : ∀{σ α} → ⟦ α ⟧A (Fixₐ σ) → AnnCounter
    gene {_} {K _} a = 0ₐ
    gene {_} {I}   x = count x

-- The relation between both is obvious;

sumₐ : List AnnCounter → AnnCounter
sumₐ []       = 0ₐ
sumₐ (x ∷ xs) = x +ₐ sumₐ xs

count*-lemma : ∀{σ}(ann : Ann)(x : ⟦ σ ⟧S (Fixₐ σ))
             → count ⟨ ann , x ⟩ ≡ count1 ann +ₐ sumₐ (count* x)
count*-lemma ann x = theMagic
-}
