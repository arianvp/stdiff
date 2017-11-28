open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Functor 
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
    where

  open import Regular.Internal.Functor Rec _≟Rec_

  All-zip3-set
    : {A : Set}{l : List A}{P Q R : A → Set}
    → (∀ {x} → P x → Q x → R x → Set)
    → All P l → All Q l → All R l
    → Set
  All-zip3-set f [] [] [] = Unit
  All-zip3-set f (x ∷ xs) (y ∷ ys) (z ∷ zs)
    = f x y z × All-zip3-set f xs ys zs

  data AppAt : {α : Atom} 
             → ⟦ α ⟧A Rec → ⟦ α ⟧A Rec
             → At PatchRec α 
             → Set 
      where
    AppSet : ∀{κ}(k₁ k₂ : ⟦ κ ⟧K) → AppAt k₁ k₂ (set (k₁ , k₂))

    AppFix : (r₁ r₂ : Rec)(p : PatchRec)
           → AppRec r₁ r₂ p
           → AppAt r₁ r₂ (fix p)

  data AppAl : {π₁ π₂ : Prod} 
             → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec
             → Al (At PatchRec) π₁ π₂
             → Set
      where
    AppA0 : AppAl [] [] A0

    AppAX : ∀{α π₁ π₂}(x y : ⟦ α ⟧A Rec)
          → (xs : ⟦ π₁ ⟧P Rec)(ys : ⟦ π₂ ⟧P Rec)
          → (px  : At PatchRec α)
          → (pxs : Al (At PatchRec) π₁ π₂)
          → AppAt x y px
          → AppAl xs ys pxs
          → AppAl (x ∷ xs) (y ∷ ys) (AX px pxs)

    AppAins : ∀{α π₁ π₂}(y : ⟦ α ⟧A Rec)
            → (xs : ⟦ π₁ ⟧P Rec)(ys : ⟦ π₂ ⟧P Rec)
            → (al : Al (At PatchRec) π₁ π₂)
            → AppAl xs ys al
            → AppAl xs (y ∷ ys) (Ains {α = α} y al)

    AppAdel : ∀{α π₁ π₂}(x : ⟦ α ⟧A Rec)
            → (xs : ⟦ π₁ ⟧P Rec)(ys : ⟦ π₂ ⟧P Rec)
            → (al : Al (At PatchRec) π₁ π₂)
            → AppAl xs ys al
            → AppAl (x ∷ xs) ys (Adel {α = α} x al)

  data AppS : {σ : Sum} 
            → ⟦ σ ⟧S Rec → ⟦ σ ⟧S Rec 
            → Patch PatchRec σ 
            → Set 
      where
    AppScp  : ∀{σ}(x : ⟦ σ ⟧S Rec) → AppS x x Scp

    AppScns : ∀{σ}(C : Constr σ)(Pxs Pys : ⟦ typeOf σ C ⟧P Rec)
            → (pxy : All (At PatchRec) (typeOf σ C))
            → All-zip3-set AppAt Pxs Pys pxy
            → AppS {σ} (inj C Pxs) (inj C Pys) (Scns C pxy)

    AppSchg : ∀{σ}(C₁ C₂ : Constr σ)(q : C₁ ≢ C₂)
            → (Pxs : ⟦ typeOf σ C₁ ⟧P Rec)
            → (Pys : ⟦ typeOf σ C₂ ⟧P Rec)
            → (al  : Al (At PatchRec) (typeOf σ C₁) (typeOf σ C₂))
            → AppAl Pxs Pys al
            → AppS {σ} (inj C₁ Pxs) (inj C₂ Pys) (Schg C₁ C₂ {q} al)
