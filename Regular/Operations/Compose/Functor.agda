open import Prelude
open import Generic.Regular

module Regular.Operations.Compose.Functor
       (Rec       : Set)
       (_≟Rec_    : (x y : Rec) → Dec (x ≡ y))
       (PatchRec  : Set)
       (AppRec    : Rec → Rec → PatchRec → Set)
       (applyRec  : PatchRec → Rec → Maybe Rec)
       (AppRec-ok : {x y : Rec}{p : PatchRec}
                  → AppRec x y p
                  → applyRec p x ≡ just y)
       (Rec-∘     : {x y z : Rec}{p q : PatchRec}
                  → AppRec x y p → AppRec y z q
                  → ∃ (AppRec x z))
    where

  open import Regular.Functor Rec _≟Rec_
  open DecEq Rec _≟Rec_
  open FunctorApplication PatchRec applyRec
  open import Regular.Predicates.Applies.Functor 
    Rec _≟Rec_ PatchRec AppRec
  open import Regular.Predicates.Applies.Correctness.Functor
    Rec _≟Rec_ PatchRec AppRec applyRec AppRec-ok

  appAt-∘ : ∀{α}{x y z : ⟦ α ⟧A Rec}{p q : At PatchRec α}
          → AppAt x y p → AppAt y z q 
          → ∃ (AppAt {α} x z)
  appAt-∘ (AppSet k₁ k₂ p) (AppSet k₃ k₄ q) 
    with k₁ ≟K k₄
  ...| yes k₁≡k₄ rewrite k₁≡k₄ = set (k₁ , k₁) , AppSetId k₁ k₄
  ...| no  k₁≢k₄ = set (k₁ , k₄) , AppSet k₁ k₄ k₁≢k₄
  appAt-∘ (AppSet k₁ k₂ p) (AppSetId k q)   
    = set (k₁ , k₂) , AppSet k₁ k₂ p
  appAt-∘ {q = q} (AppSetId k a) hq = q , hq
  appAt-∘ (AppFix r₁ r₂ p hp) (AppFix s₁ s₂ q hq) 
    with Rec-∘ hp hq
  ...| r , hr = fix r , AppFix r₁ s₂ r hr

  appAl-∘ : ∀{π₁ π₂ π₃}{x : ⟦ π₁ ⟧P Rec}{y : ⟦ π₂ ⟧P Rec}{z : ⟦ π₃ ⟧P Rec}
          → {p : Al (At PatchRec) π₁ π₂}{q : Al (At PatchRec) π₂ π₃}
          → AppAl x y p → AppAl y z q
          → ∃ (AppAl x z)
  appAl-∘ {q = q} AppA0 hq = q , hq
  appAl-∘ (AppAX x y xs ys px pxs x₁ hp) (AppAX .y z .ys zs py pys y₁ hq) 
    with appAt-∘ x₁ y₁ | appAl-∘ hp hq
  ...| a , ha | as , has = AX a as , AppAX x z xs zs a as ha has
  appAl-∘ (AppAX x y xs ys px pxs x₁ hp) (AppAins z .(y ∷ ys) zs al hq) 
    with appAl-∘ (AppAX x y xs ys px pxs x₁ hp) hq
  ...| as , has
    = Ains z as , AppAins z (x ∷ xs) zs as has
  appAl-∘ (AppAX x y xs ys px pxs x₁ hp) (AppAdel .y y' .ys zs q hq) 
    with appAl-∘ hp hq
  ...| as , has = Adel x as , AppAdel x x xs zs as has
  appAl-∘ (AppAins y xs ys p hp) (AppAins z .(y ∷ ys) zs q hq) 
    with appAl-∘ (AppAins y xs ys p hp) hq
  ...| as , has = Ains z as , AppAins z xs zs as has
  appAl-∘ (AppAins y xs ys p hp) (AppAdel .y y' .ys zs q hq) 
    = appAl-∘ hp hq
  appAl-∘ (AppAins y xs ys p hp) (AppAX .y z .ys zs py pys q hq) 
    with appAl-∘ hp hq
  ...| as , has = Ains z as , AppAins z xs zs as has
  appAl-∘ (AppAdel x x' xs ys p hp) AppA0 
    = Adel x p , AppAdel x x xs [] p hp
  appAl-∘ (AppAdel x x' xs .(y ∷ ys) p hp) (AppAdel y y' ys zs q hq) 
    with appAl-∘ hp (AppAdel y y' ys zs q hq)
  ...| as , has = Adel x as , AppAdel x x xs zs as has
  appAl-∘ (AppAdel x x' xs ys p hp) (AppAins z .ys zs q hq)
   with appAl-∘ hp hq
  -- TODO: put some thought here... we could transform x into z!!
  ...| as , has = Adel x (Ains z as) 
                , AppAdel x x xs (z ∷ zs) (Ains z as) (AppAins z xs zs as has) 
  appAl-∘ (AppAdel x x' xs .(y ∷ ys) p hp) (AppAX y z ys zs py pys q hq)
    with appAl-∘ hp (AppAX y z ys zs py pys q hq)
  ...| as , has = Adel x as , AppAdel x x xs (z ∷ zs) as has

  appS'-∘ : ∀{σ}{C₁ C₂ C₃ : Constr σ}
          → {P₁ : ⟦ typeOf σ C₁ ⟧P Rec}
          → {P₂ : ⟦ typeOf σ C₂ ⟧P Rec}
          → {P₃ : ⟦ typeOf σ C₃ ⟧P Rec}
          → {p q : Patch PatchRec σ}
          → AppS (inj C₁ P₁) (inj C₂ P₂) p
          → AppS (inj C₂ P₂) (inj C₃ P₃) q
          → ∃ (AppS (inj {σ} C₁ P₁) (inj {σ} C₃ P₃))
  appS'-∘ {_} {C₁} {C₂} {C₃} {P₁} {P₂} {P₃} hp hq
    with C₁ ≟F C₂
  ...| yes refl with P₁ ≟P P₂
  appS'-∘ {_} {C₁} {.C₁} {C₃} {P₁} {.P₁} {P₃} {p} {q} hp hq
     | yes refl | yes refl  = q , hq
  appS'-∘ {_} {C₁} {.C₁} {C₃} {P₁} {P₂} {P₃} hp hq
     | yes refl | no  P₁≢P₂ = {!!}
  appS'-∘ {_} {C₁} {C₂} {C₃} {P₁} {P₂} {P₃} hp hq
     | no  C₁≢C₂ with C₂ ≟F C₃
  appS'-∘ {_} {C₁} {C₂} {.C₂} {P₁} {P₂} {P₃} hp hq
     | no C₁≢C₂ | yes refl with P₂ ≟P P₃
  appS'-∘ {_} {C₁} {C₂} {.C₂} {P₁} {P₂} {.P₂} {p} hp hq
     | no C₁≢C₂ | yes refl | yes refl = p , hp
  appS'-∘ {_} {C₁} {C₂} {.C₂} {P₁} {P₂} {P₃} hp hq
     | no C₁≢C₂ | yes refl | no P₂≢P₃ = {!!}
  appS'-∘ {_} {C₁} {C₂} {C₃} {P₁} {P₂} {P₃} hp hq
     | no C₁≢C₂ | no C₂≢C₃ = {!!}

  inj-Maybe-⊥
    : ∀{σ}{C₁ C₂ : Constr σ}(h : C₁ ≢ C₂)
    → {ps : Maybe (⟦ typeOf σ C₁ ⟧P Rec)}{qs : ⟦ typeOf σ C₂ ⟧P Rec}
    → Maybe-map (inj {σ} C₁) ps ≡ just (inj C₂ qs)
    → ⊥
  inj-Maybe-⊥ = {!!}

  inj-extract
    : ∀{σ}(C₁ C₂ : Constr σ)
    → (ps : Maybe (⟦ typeOf σ C₁ ⟧P Rec))(qs : ⟦ typeOf σ C₂ ⟧P Rec)
    → Maybe-map (inj {σ} C₁) ps ≡ just (inj C₂ qs)
    → Σ (C₁ ≡ C₂) (λ { refl → ps ≡ just qs })
  inj-extract C₁ C₂ nothing qs hip = Maybe-⊥-elim hip
  inj-extract C₁ C₂ (just ps) qs hip 
    with inj-inj (just-inj hip)
  ...| refl , h = refl , cong just h

  ∷-extract 
    : ∀{α π}{x y : ⟦ α ⟧A Rec}{xs ys : ⟦ π ⟧P Rec}
    → (p : At PatchRec α)(ps : All (At PatchRec) π)
    → ⟪ p ∷ ps ⟫SP (x ∷ xs) ≡ just (y ∷ ys)
    → (⟪ p ⟫A x ≡ just y) × (⟪ ps ⟫SP xs ≡ just ys)
  ∷-extract {α} {π} {x} {y} p ps hip 
    with ⟪ p ⟫A x 
  ...| nothing = Maybe-⊥-elim hip
  ...| just x' 
    with _≟A_ {α} x' y
  ...| no abs   = {!!}
  ...| yes refl = {!!}

  appAll-∘-ext
    : ∀{π}{xs ys zs : ⟦ π ⟧P Rec}(p q : All (At PatchRec) π)
    → (hipP : ⟪ p ⟫SP xs ≡ just ys)
    → (hipQ : ⟪ q ⟫SP ys ≡ just zs)
    → ∃ (λ r → ⟪ r ⟫SP xs ≡ just zs)
  appAll-∘-ext {[]} {[]} {[]} {[]} [] [] _ _ = [] , refl
  appAll-∘-ext {α ∷ π} {x ∷ xs} {y ∷ ys} {z ∷ zs} (p ∷ ps) (q ∷ qs) hp hq 
    with ∷-extract p ps hp
  ...| r0 , r1 
    with ∷-extract q qs hq
  ...| s0 , s1 
     = let appP = AppAt-sound x y p r0
           appQ = AppAt-sound y z q s0
        in {!!}

  appS-∘-ext
    : ∀{σ}{x y z : ⟦ σ ⟧S Rec}(p q : Patch PatchRec σ)
    → (hipP : ⟪ p ⟫S x ≡ just y)
    → (hipQ : ⟪ q ⟫S y ≡ just z)
    → ∃ (λ qp → ⟪ qp ⟫S x ≡ just z)
  appS-∘-ext Scp q refl hq = q , hq
  appS-∘-ext p Scp hp refl = p , hp
  appS-∘-ext {x = x} {y} {z} (Scns C₁ pxy) (Scns C₂ pyz) hp hq
    with sop x | sop y | sop z
  ...| tag Cx Px | tag Cy Py | tag Cz Pz
    with C₂ ≟F Cy 
  ...| no abs = Maybe-⊥-elim hq
  ...| yes refl
    with C₁ ≟F Cx
  ...| no abs = Maybe-⊥-elim hp
  ...| yes refl 
    with inj-extract Cx Cy (⟪ pxy ⟫SP Px) Py hp
  ...| refl , r0 
    with inj-extract Cy Cz (⟪ pyz ⟫SP Py) Pz hq
  ...| refl , r1 = Scns Cx (All-map {!!} (zipd pxy pyz)) , {!!}
{- 
    with Cx ≟F Cy
  ...| no abs = ⊥-elim (inj-Maybe-⊥ abs {⟪ pxy ⟫SP Px} {Py} hp)
  ...| yes refl = {!!}
-}
  appS-∘-ext (Scns C₁ pxy) (Schg C₂ C₃ al) hp hq = {!!}
  appS-∘-ext = {!!}

  appS-∘ : ∀{σ}{x y z : ⟦ σ ⟧S Rec}{p q : Patch PatchRec σ}
         → AppS x y p → AppS y z q
         → ∃ (AppS x z)
{-
  appS-∘ {_} {x} {y} {z} hp hq
    with sop x | sop y | sop z
  ...| tag Cx Px | tag Cy Py | tag Cz Pz 
    = appS'-∘ hp hq
-}
  appS-∘-Scns-proj
    : ∀{σ}{C : Constr σ}{Pxs Pys : ⟦ typeOf σ C ⟧P Rec}
    → {p : Patch PatchRec σ}
    → AppS (inj C Pxs) (inj C Pys) p
    → ∃ (All-zip3-set (λ {α} → AppAt {α}) Pxs Pys)
  appS-∘-Scns-proj hp = {!!}

  appS-∘ {q = q} (AppScp x) hq = q , hq
  appS-∘ {q = Scp} (AppScns C Pxs Pys pxy x) (AppScp .(inj C Pys)) 
    = Scns C pxy , AppScns C Pxs Pys pxy x
  appS-∘ {σ} {z = z} {q = Scns C₁ ats} (AppScns C Pxs Pys pxy x) hq 
    with AppS-correct hq
  ...| prf rewrite sop-inj-lemma {σ} C Pys 
    with C₁ ≟F C
  ...| no abs = Maybe-⊥-elim prf
  ...| yes refl with sop z
  ...| tag Cz Pzs with C ≟F Cz 
  ...| no abs = ⊥-elim (inj-Maybe-⊥ {σ} {C} {Cz} abs {⟪ ats ⟫SP Pys} prf) 
  appS-∘ {σ} {z = z} {q = Scns .Cz ats} 
         (AppScns .Cz Pxs Pys pxy x) hq
     | prf | yes refl | tag Cz Pzs | yes refl = {!!}
  appS-∘ {q = Schg C₁ C₂ al} (AppScns C Pxs Pys pxy x) hq = {!!}
  appS-∘ (AppSchg C₁ C₂ q Pxs Pys al x) hq = {!!}

