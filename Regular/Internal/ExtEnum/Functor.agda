open import Prelude
open import Generic.Regular

module Regular.Internal.ExtEnum.Functor
         (Rec : Set)(_≟Rec_ : ∀ (⟨x⟩ ⟨y⟩ : Rec) → Dec (⟨x⟩ ≡ ⟨y⟩))
         (M : Set → Set)(m : RawMonadPlus M)
       where

  open import Regular.Internal.Functor Rec _≟Rec_
  open DecEq Rec _≟Rec_

  open RawMonadPlus m

  All-mapM : ∀ {A}{P : A → Set} {Q : A → Set} →
           (∀{a} → P a → M (Q a)) → ∀{xs} → All P xs → M (All Q xs)
  All-mapM g []         = return []
  All-mapM g (px ∷ pxs) = _∷_ <$> g px ⊛ All-mapM g pxs


-- ** Spine identification

  spine : ∀ {σ} → ⟦ σ ⟧S Rec → ⟦ σ ⟧S Rec → S TrivialA TrivialP σ
  spine s₁ s₂ with s₁ ≟S s₂
  ... | yes refl = Scp
  ... | no ¬p  with sop s₁ | sop s₂
  ... | tag C₁ p₁ | tag C₂ p₂ with C₁ ≟F C₂
  ... | yes refl = Scns C₁ (zipd p₁ p₂)
  ... | no ¬q = Schg C₁ C₂ {¬q} (p₁ , p₂)
  
  _⊆M_ : (At₁ At₂ : Atom → Set) → Set
  At₁ ⊆M At₂ = At₁ ⊆ M ∘ At₂

  _⇒M_ : (Al₁ Al₂ : Rel Prod _) → Set
  Al₁ ⇒M Al₂ = ∀{π₁ π₂} → Al₁ π₁ π₂ → M (Al₂ π₁ π₂)

  S-mapM : {σ : Sum}
           {At₁ At₂ : Atom → Set}
           {Al₁ Al₂ : Rel Prod _}
        → (At₁ ⊆M At₂)
        → (Al₁ ⇒M Al₂)
        → S At₁ Al₁ σ → M (S At₂ Al₂ σ)
  S-mapM f g Scp = return Scp
  S-mapM f g (Scns C ps) = Scns C <$> All-mapM f ps
  S-mapM f g (Schg C₁ C₂ {q} al) = Schg C₁ C₂ {q} <$> g al

-- ** Enumerating alignments

  align : ∀{π₁ π₂} → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec → M (Al TrivialA π₁ π₂)
  align  [] [] = return A0
  align  [] (at₂ ∷ ats₂) = Ains at₂ <$> align [] ats₂
  align (at₁ ∷ ats₁) [] = Adel at₁ <$> align ats₁ []
  align {α₁ ∷ π₁} {α₂ ∷ π₂} (at₁ ∷ ats₁) (at₂ ∷ ats₂) with α₁ ≟Atom α₂
  ... | yes refl = AX (at₁ , at₂) <$> align ats₁ ats₂
                 ∣ Adel at₁ <$> align ats₁ (at₂ ∷ ats₂)
                 ∣ Ains at₂ <$> align (at₁ ∷ ats₁) ats₂
  ... | no ¬p = Adel at₁ <$> align ats₁ (at₂ ∷ ats₂)
              ∣ Ains at₂ <$> align (at₁ ∷ ats₁) ats₂

  al-mapM : ∀{π₁ π₂}
            {At₁ At₂ : Atom → Set}
          → (At₁ ⊆M At₂) 
          → Al At₁ π₁ π₂ → M (Al At₂ π₁ π₂)
  al-mapM f A0 = return A0
  al-mapM f (Adel at al) = Adel at <$> al-mapM f al
  al-mapM f (Ains at al) = Ains at <$> al-mapM f al
  al-mapM f (AX at al) = AX <$> f at ⊛ al-mapM f al

  diffAt : ∀ {α PatchRec} → (Rec → Rec → M PatchRec) → ⟦ α ⟧A Rec → ⟦ α ⟧A Rec → M (At PatchRec α)
  diffAt {K κ} diffR k₁ k₂ = return (set (k₁ , k₂))
  diffAt {I} diffR x y = fix <$> diffR x y

  diffS : ∀{PatchRec σ} → (Rec → Rec → M PatchRec)
         → ⟦ σ ⟧S Rec → ⟦ σ ⟧S Rec → M (S (At PatchRec) (Al (At PatchRec)) σ)
  diffS {PatchRec} diffR s₁ s₂ = S-mapM (uncurry (diffAt diffR)) (uncurry alignP) (spine s₁ s₂)
         where alignP : ∀ {π₁ π₂} → ⟦ π₁ ⟧P Rec → ⟦ π₂ ⟧P Rec → M (Al (At PatchRec) π₁ π₂)
               alignP p₁ p₂ = align p₁ p₂ >>= al-mapM (uncurry (diffAt diffR))
