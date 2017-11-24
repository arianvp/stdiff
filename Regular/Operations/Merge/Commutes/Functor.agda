open import Prelude
open import Generic.Regular

module Regular.Operations.Merge.Commutes.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (makeidR   : Rec → PatchRec)
       (identityR : PatchRec → Set)
       (disjRec   : PatchRec → PatchRec → Set)
       (disjRecSym    : (r₁ r₂ : PatchRec) → disjRec r₁ r₂ → disjRec r₂ r₁) 
       (disjRecSymInv : (r₁ r₂ : PatchRec)(h : disjRec r₁ r₂)
                      → disjRecSym r₂ r₁ (disjRecSym r₁ r₂ h) ≡ h) 
       (mergeRec  : (p₁ p₂ : PatchRec)(hip : disjRec p₁ p₂) → PatchRec)
       (applyRec  : PatchRec → Rec → Maybe Rec)
    where

  -- * Basic patches-over-functors functionality and predicates.
  open import Regular.Internal.Functor Rec _≟Rec_
  open import Regular.Predicates.Identity.Functor 
                Rec _≟Rec_ PatchRec makeidR identityR
  open import Regular.Predicates.Disjoint.Functor 
                Rec _≟Rec_ PatchRec makeidR identityR disjRec
  open import Regular.Operations.Merge.Functor
                Rec _≟Rec_ PatchRec makeidR identityR disjRec mergeRec

  open DecEq Rec _≟Rec_

  -- * Disjointness is symmetric
  open DisjSymmetry disjRecSym disjRecSymInv

  -- * Characterization of identity patches is correct
  open IdentityPropertiesF applyRec

  -- * We need monadic functionality for Maybe
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus renaming (_<=<_ to _∙_)

  -- * Renames the application functions to ⟪_⟫ ; makes life easier.
  open import Regular.Functor Rec _≟Rec_ using (module FunctorApplication)
  open FunctorApplication PatchRec applyRec

  -- * XXX: To be refactored:
  --   Auxiliary lemmas about application
  
  ⟪⟫Scns-comp : {σ : Sum}{C : Constr σ}{a₁ a₂ : All (At PatchRec) (typeOf σ C)}
              → ∀ x → (⟪ Scns {σ = σ} C a₁ ⟫S ∙ ⟪ Scns C a₂ ⟫S) x
                    ≡ ((just ∘ inj {σ} C) ∙ ⟪ a₁ ⟫SP ∙ ⟪ a₂ ⟫SP ∙ match C) x
  ⟪⟫Scns-comp {σ} {C} {a₁} {a₂} x with sop x
  ...| tag Cx Px with C ≟F Cx 
  ...| no _     = refl
  ...| yes refl 
    with ⟪ a₂ ⟫SP Px 
  ...| nothing  = refl
  ...| just Px' 
    rewrite sop-inj-lemma {σ} Cx Px' 
    with Cx ≟F Cx
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl

  ⟪⟫Schg-inj-natural : {σ : Sum}{C D : Constr σ}{q : C ≢ D}
                       (al : Al (At PatchRec) (typeOf σ C) (typeOf σ D))
                       (at : All (At PatchRec) (typeOf σ C))
                     → ∀ x → (Maybe-map (inj {σ} C) (⟪ at ⟫SP x) 
                             >>= ⟪ Schg {σ = σ} C D {q} al ⟫S )
                           ≡ ((just ∘ inj {σ} D) ∙ ⟪ al ⟫P ∙ ⟪ at ⟫SP) x
  ⟪⟫Schg-inj-natural {σ} {C} {D} {q} al at x 
    with ⟪ at ⟫SP x
  ...| nothing = refl
  ...| just x' 
    rewrite sop-inj-lemma {σ} C x'
    with C ≟F C
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl

  ⟪_⟫Rec : PatchRec → Rec → Maybe Rec
  ⟪_⟫Rec = applyRec

  module MergeCommutesHip 
         (mergeRec-commute : (r₁ r₂ : PatchRec)(hip : disjRec r₁ r₂)
                           → ∀ x → ( ⟪ mergeRec r₁ r₂ hip ⟫Rec                    ∙ ⟪ r₁ ⟫Rec) x
                                 ≡ ( ⟪ mergeRec r₂ r₁ (disjRecSym r₁ r₂ hip) ⟫Rec ∙ ⟪ r₂ ⟫Rec) x)
      where
    -- * We need a bunch of commutation proofs; one for each "level" of the universe.
    --   Nevertheless, they all go more or less the same.
    --
    --
    -- * Whenever s₁ and s₂ are disjoint, merging applies both changes.
    {-# TERMINATING #-}
    mergeS-commute : {σ : Sum}(s₁ s₂ : Patch PatchRec σ)(hip : disjS s₁ s₂)
                    → ∀ x → (⟪ mergeS s₁ s₂ hip ⟫S ∙ ⟪ s₁ ⟫S) x
                          ≡ (⟪ mergeS s₂ s₁ (disjS-sym s₁ s₂ hip) ⟫S ∙ ⟪ s₂ ⟫S) x

    merge-At-Al-commute : ∀{π₁ π₂}(ats : All (At PatchRec) π₁)(al : Al (At PatchRec) π₁ π₂)
                        → (hip : disj-At-Al ats al)
                        → ∀ x → (⟪ merge-At-Al ats al hip ⟫P ∙ ⟪ ats ⟫SP) x
                              ≡ (⟪ merge-Al-At al ats (disj-At-Al-sym ats al hip) ⟫SP ∙ ⟪ al ⟫P) x

    merge-Al-At-commute : ∀{π₁ π₂}(al : Al (At PatchRec) π₁ π₂)(ats : All (At PatchRec) π₁)
                        → (hip : disj-Al-At al ats)
                        → ∀ x → (⟪ merge-Al-At al ats hip ⟫SP ∙ ⟪ al ⟫P) x
                              ≡ (⟪ merge-At-Al ats al (disj-Al-At-sym al ats hip) ⟫P ∙ ⟪ ats ⟫SP) x

    mergeAt-commute : {α : Atom}(a₁ a₂ : At PatchRec α)(hip : disjAt a₁ a₂)
                    → ∀ x → (⟪ mergeAt a₁ a₂ hip ⟫A ∙ ⟪ a₁ ⟫A) x
                          ≡ (⟪ mergeAt a₂ a₁ (disjAt-sym a₁ a₂ hip) ⟫A ∙ ⟪ a₂ ⟫A) x
    mergeAt-commute (set (k₁ , _))  (set (k₂ , k₃)) (inj₁ refl) x 
      rewrite dec-refl _≟K_ k₁ 
      with k₂ ≟K k₃
    ...| yes refl = refl
    ...| no _     
      with k₂ ≟K x
    ...| no _     = refl
    ...| yes refl = refl
    mergeAt-commute (set (k₁ , k₂)) (set (k₃ , _))  (inj₂ refl) x 
      rewrite dec-refl _≟K_ k₃ 
      with k₁ ≟K k₂
    ...| yes refl = refl
    ...| no _     
      with k₁ ≟K x
    ...| no _     = refl
    ...| yes refl = refl
    mergeAt-commute (fix rec₁) (fix rec₂) hip x 
      = mergeRec-commute rec₁ rec₂ hip x

    private
      distr : {A : Set}{P Q R : A → Set}{l k m : A}{ls ks ms : List A}
            → (f : P l → Maybe (Q k))(fs : All P ls → Maybe (All Q ks))
            → (g : Q k → Maybe (R m))(gs : All Q ks → Maybe (All R ms))
            → (x : P l)(xs : All P ls)
            → ((All-head-map g gs) ∙ (All-head-map f fs)) (x ∷ xs)
            ≡ All-head-map (g ∙ f) (gs ∙ fs) (x ∷ xs)
      distr f fs g gs x xs 
        with f x
      ...| nothing = refl
      ...| just y   
        with fs xs
      ...| nothing
        with g y 
      ...| nothing = refl
      ...| just _  = refl 
      distr f fs g gs x xs | just y | just ys = refl

    
      All-head-map-prepend : {A : Set}{l : A}{ls ks : List A}{P Q O : A → Set}
                          → (f : P l → Maybe (Q l))(fs : All P ls → Maybe (All Q ls))
                          → (g : All O ks → Maybe (All P ls))
                          → (k : P l)(xs : All O ks)
                          → ((((k ∷_) <$> g xs) >>= All-head-map f fs) )
                          ≡ (_∷_ <$> f k ⊛ (fs ∙ g) xs)
      All-head-map-prepend f fs g k xs
        with g xs
      ...| nothing
        with f k
      ...| nothing = refl
      ...| just k' = refl
      All-head-map-prepend f fs g k xs | just xs' 
        with f k
      ...| nothing = refl
      ...| just k' = refl

    mergeSP-commute : {π : Prod}(p₁ p₂ : All (At PatchRec) π)(hip : disjAts p₁ p₂)
                    → ∀ x → (⟪ mergeAts p₁ p₂ hip ⟫SP ∙ ⟪ p₁ ⟫SP) x
                          ≡ (⟪ mergeAts p₂ p₁ (disjAts-sym p₁ p₂ hip) ⟫SP ∙ ⟪ p₂ ⟫SP) x

    mergeSP-commute []         []         hip x = refl
    mergeSP-commute {α ∷ π} (a₁ ∷ as₁) (a₂ ∷ as₂) (h0 , h1) (x ∷ xs)
       rewrite distr {l = α} {α} {α} {π} {π} {π} 
                     ⟪ a₁ ⟫A ⟪ as₁ ⟫SP ⟪ mergeAt a₁ a₂ h0 ⟫A ⟪ mergeAts as₁ as₂ h1 ⟫SP x xs
             | distr {l = α} {α} {α} {π} {π} {π} 
                     ⟪ a₂ ⟫A ⟪ as₂ ⟫SP ⟪ mergeAt a₂ a₁ (disjAt-sym a₁ a₂ h0) ⟫A
                     ⟪ mergeAts as₂ as₁ (disjAts-sym as₁ as₂ h1) ⟫SP x xs
             | mergeAt-commute a₁ a₂ h0 x
             | mergeSP-commute as₁ as₂ h1 xs
             = refl
 
    mergeS-commute Scp Scp hip x = refl
    mergeS-commute Scp (Scns C₂ at₂) hip x 
      with ⟪ Scns C₂ at₂ ⟫S x 
    ...| nothing = refl
    ...| just x' = refl
    mergeS-commute Scp (Schg C₂ C₃ {q} al₂) hip x 
      with ⟪ Schg C₂ C₃ {q} al₂ ⟫S x
    ...| nothing = refl
    ...| just x' = refl
    mergeS-commute (Scns C₁ at₁) Scp hip x 
      with ⟪ Scns C₁ at₁ ⟫S x 
    ...| nothing = refl
    ...| just x' = refl
    mergeS-commute (Schg C₁ C₂ {q} al) Scp hip x 
      with ⟪ Schg C₁ C₂ {q} al ⟫S x
    ...| nothing = refl
    ...| just x' = refl
    mergeS-commute (Schg _ _ _) (Schg _ _ _) () _
    mergeS-commute {σ} (Scns C₁ at₁) (Scns _ at₂) (refl , hip) x 
      rewrite ⟪⟫Scns-comp {σ} {C₁} {mergeAts at₁ at₂ hip} {at₁} x
            | ⟪⟫Scns-comp {σ} {C₁} {at₂} {mergeAts at₂ at₁ (disjAts-sym at₁ at₂ hip)} x 
      with sop x
    ...| tag Cx Px with C₁ ≟F Cx
    ...| no _     = refl
    ...| yes refl 
      rewrite mergeSP-commute at₁ at₂ hip Px
      with ⟪ at₂ ⟫SP Px
    ...| nothing  = refl
    ...| just Px' 
      rewrite sop-inj-lemma {σ} Cx Px'
            | dec-refl _≟F_ Cx 
            = refl
    mergeS-commute {σ} (Scns C₁ at₁) (Schg C₂ C₃ {q} al₂) (refl , hip) x 
      with sop x
    ...| tag Cx Px 
      with C₁ ≟F Cx
    ...| no C₁≢Cx 
      with C₃ ≟F Cx
    ...| no C₃≢Cx = refl
    ...| yes refl with ⟪ merge-Al-At al₂ at₁ (disj-At-Al-sym at₁ al₂ hip) ⟫SP Px
    ...| nothing  = refl
    ...| just Px' 
      rewrite sop-inj-lemma {σ} Cx Px'
      with C₁ ≟F Cx
    ...| no _    = refl
    ...| yes abs = ⊥-elim (C₁≢Cx abs)
    mergeS-commute {σ} (Scns C₁ at₁) (Schg C₂ C₃ {q} al₂) (refl , hip) x
      | tag Cx Px 
      | yes refl
      rewrite ⟪⟫Schg-inj-natural {σ} {Cx} {C₃} {q} (merge-At-Al at₁ al₂ hip) at₁ Px
            | merge-At-Al-commute at₁ al₂ hip Px
        with ⟪ al₂ ⟫P Px
    ...| nothing  = refl
    ...| just Px' 
      rewrite sop-inj-lemma {σ} C₃ Px'
      with C₃ ≟F C₃
    ...| no abs   = ⊥-elim (abs refl)
    ...| yes refl = refl
    mergeS-commute {σ} (Schg C₁ C₂ {q} al₁) (Scns _ at₂) (refl , hip) x
      with sop x
    ...| tag Cx Px with C₁ ≟F Cx
    ...| no C₁≢Cx with C₂ ≟F Cx
    ...| no C₂≢Cx = refl
    ...| yes refl with ⟪ merge-Al-At al₁ at₂ hip ⟫SP Px
    ...| nothing  = refl
    ...| just Px'
      rewrite sop-inj-lemma {σ} Cx Px'
      with C₁ ≟F Cx
    ...| no _    = refl
    ...| yes abs = ⊥-elim (C₁≢Cx abs)
    mergeS-commute {σ} (Schg C₁ C₂ {q} al₁) (Scns _ at₂) (refl , hip) x
      | tag Cx Px | yes refl 
      rewrite ⟪⟫Schg-inj-natural {σ} {Cx} {C₂} {q} 
                                (merge-At-Al at₂ al₁ (disj-Al-At-sym al₁ at₂ hip)) 
                                at₂ Px
            | merge-At-Al-commute at₂ al₁ (disj-Al-At-sym al₁ at₂ hip) Px
            | disj-Al-At-sym-inv al₁ at₂ hip
        with ⟪ al₁ ⟫P Px
    ...| nothing  = refl
    ...| just Px' 
      rewrite sop-inj-lemma {σ} C₂ Px'
            | dec-refl _≟F_ C₂
            = refl

    merge-Al-At-[]-id : ∀{π₂}(al : Al (At PatchRec) [] π₂)
                      → ∀ xs → ⟪ merge-Al-At al [] unit ⟫SP xs ≡ just xs
    merge-Al-At-[]-id A0 []           = refl
    merge-Al-At-[]-id (Ains {α} at al) (x ∷ xs) 
      rewrite identityAt-correct {α} (makeidAt at) (makeidAt-correct {α} at) x
            | merge-Al-At-[]-id al xs
            = refl


    merge-Al-At-commute A0 [] hip [] = refl
    merge-Al-At-commute (Ains {α} at al) [] unit []
      rewrite identityAt-correct {α} (makeidAt at) (makeidAt-correct {α} at) at
            | merge-At-Al-commute [] al unit [] 
         with ⟪ al ⟫P []
    ...| nothing = refl
    ...| just xs 
      rewrite merge-Al-At-[]-id al xs
            | identityAt-correct {α} (makeidAt at) (makeidAt-correct {α} at) at
            = refl
    merge-Al-At-commute (Ains {α} at al) (a ∷ as) hip (x ∷ xs)
      rewrite All-head-map-prepend {Atom} {α} 
                                   ⟪ makeidAt {α} at ⟫A 
                                   ⟪ merge-Al-At al (a ∷ as) hip ⟫SP
                                   ⟪ al ⟫P at (x ∷ xs)
            | merge-Al-At-commute al (a ∷ as) hip (x ∷ xs)
            | identityAt-correct {α} (makeidAt at) (makeidAt-correct {α} at) at 
      with ⟪ a ⟫A x
    ...| nothing = refl 
    ...| just x' 
      with ⟪ as ⟫SP xs
    ...| nothing  = refl
    ...| just xs' = refl 
    merge-Al-At-commute (Adel {α} at al) (a ∷ as) (h0 , h1) (x ∷ xs)
      with _≟A_ {α} at x | inspect (_≟A_ {α} at) x
    ...| no  _ | [ AT≢X ]
      rewrite identityAt-correct a h0 x
            | merge-Al-At-commute al as h1 xs
      with ⟪ as ⟫SP xs
    ...| nothing  = refl
    ...| just xs' rewrite AT≢X = refl
    merge-Al-At-commute (Adel {α} at al) (a ∷ as) (h0 , h1) (x ∷ xs)
       | yes _ | [ AT≡X ] 
      rewrite identityAt-correct a h0 x
            | merge-Al-At-commute al as h1 xs
      with ⟪ as ⟫SP xs
    ...| nothing  = refl
    ...| just xs' rewrite AT≡X = refl

    merge-Al-At-commute {α ∷ π₁} {π₂} (AX {α = α'} {π₂ = π₂'} at al) (a ∷ as) (h0 , h1) (x ∷ xs) 
      rewrite distr {l = α} {α'} {α'}
                    ⟪ at ⟫A ⟪ al ⟫P
                    ⟪ mergeAt at a h0 ⟫A ⟪ merge-Al-At al as h1 ⟫SP
                    x xs
            | merge-Al-At-commute al as h1 xs
            | mergeAt-commute at a h0 x
      with ⟪ a ⟫A x
    ...| nothing = refl    
    ...| just x' 
      with ⟪ as ⟫SP xs
    ...| just xs' = refl
    ...| nothing  
      with ⟪ mergeAt a at (disjAt-sym at a h0) ⟫A x'
    ...| nothing = refl 
    ...| just _  = refl 

    merge-At-Al-commute ats al hip xs 
      rewrite merge-Al-At-commute al ats (disj-At-Al-sym ats al hip) xs
            | disj-At-Al-sym-inv ats al hip
            = refl
