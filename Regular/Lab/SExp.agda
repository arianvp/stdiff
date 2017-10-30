open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.Lab.SExp where

  SExpF : Sum
  SExpF =
    let NameT   = K `String ∷ [] in
    let DefT    = K `String ∷ I ∷ I ∷ [] in
    let ConsT   = I ∷ I ∷ [] in
    let NilT    = [] in
    let LitT    = K `String ∷ [] in
      NameT ∷ DefT ∷ ConsT ∷ NilT ∷ LitT ∷ []

  SExp : Set
  SExp = Fix SExpF

  %name %def %cons %nil %lit : Constr SExpF
  %name = zero
  %def  = suc zero
  %cons = suc (suc zero)
  %nil  = suc (suc (suc zero))
  %lit  = suc (suc (suc (suc zero)))

  N : String → SExp
  N x = ⟨ inj %name (x ∷ []) ⟩

  Lit : String → SExp
  Lit x = ⟨ inj %lit (x ∷ []) ⟩
  
  Def : String → SExp → SExp → SExp
  Def nm parms body = ⟨ inj %def (nm ∷ parms ∷ body ∷ []) ⟩

  infixr 20 _▹_
  _▹_ : SExp → SExp → SExp
  s₁ ▹ s₂ = ⟨ inj %cons (s₁ ∷ s₂ ∷ []) ⟩ 

  # : SExp
  # = ⟨ inj %nil [] ⟩

  open import Regular.Functor SExp _≟Fix_
  open import Regular.Fixpoint SExpF

  k1 k2 k3 k4 : SExp

  k1 = Def "head" (N "s" ▹ #)
                  (N "if" ▹ (N "null" ▹ N "s" ▹ #)
                             ▹ (N "error" ▹ Lit "!?" ▹ #)
                             ▹ (N "car" ▹ N "s" ▹ #)
                             ▹ #)

  k2 = Def "head" (N "s" ▹ #)
                  (N "if" ▹ (N "null" ▹ N "s" ▹ #)
                             ▹ (N "failWith" ▹ Lit "!?" ▹ #)
                             ▹ (N "car" ▹ N "s" ▹ #)
                             ▹ #)

  k3 = Def "head" (N "s" ▹ #)
                  (N "if" ▹ (N "null" ▹ N "s" ▹ #)
                             ▹ (N "error" ▹ Lit "empty list" ▹ #)
                             ▹ (N "car" ▹ N "s" ▹ #)
                             ▹ #)

  k4 = Def "head" (N "s" ▹ #)
                  (N "if" ▹ (N "null" ▹ N "s" ▹ #)
                             ▹ (N "failWith" ▹ Lit "empty list" ▹ #)
                             ▹ (N "car" ▹ N "s" ▹ #)
                             ▹ #)

  p12 : Alμ
  p12 = spn (Scns %cons ((fix (spn 
            (Scns %name (set ("error" , "failWith") ∷ [])))) 
                  ∷ (fix (spn Scp) ∷ [])))

  p13 : Alμ
  p13 = spn (Scns %cons (fix (spn Scp) 
            ∷ fix (spn (Scns %cons (fix ((spn (Scns %lit (set ("!?" , "empty list") ∷ [])))) 
            ∷ fix (spn Scp) ∷ []))) ∷ []))

  p-tmp : Alμ → Alμ
  p-tmp x = spn (Scns %def 
                ( set ("head" , "head") 
                ∷ fix (spn Scp)
                ∷ fix (spn (Scns %cons 
                      ( fix (spn Scp) 
                      ∷ fix (spn (Scns %cons 
                        ( fix (spn Scp) 
                        ∷ fix (spn (Scns %cons 
                          ( fix x
                          ∷ fix (spn Scp) 
                          ∷ [])))
                        ∷ []))) 
                      ∷ []))) 
                ∷ []))

  apply-d12-ok : applyAlμ (p-tmp p12) k1 ≡ just k2
  apply-d12-ok = refl

  apply-d13-ok : applyAlμ (p-tmp p13) k1 ≡ just k3
  apply-d13-ok = refl

  apply-commute-1 : applyAlμ (p-tmp p12) k3 ≡ just k4
  apply-commute-1 = refl

  apply-commute-2 : applyAlμ (p-tmp p13) k2 ≡ just k4
  apply-commute-2 = refl

  open import Regular.ES.Fixpoint SExpF
  open import Regular.ES.MemoEnum SExpF
    as MemoEnum
    using ()
  open import Regular.ES.AnnEnum SExpF
    as AnnEnum
    using ()

  
  j1 j2 : SExp
  
  j1 = N "keep" ▹ (N "old" ▹ N "keep")

  j2 = (N "keep" ▹ (N "new" ▹ N "keep")) 
     ▹ (N "new" ▹ N "new")

  es12 : ES (I ∷ []) (I ∷ [])
  es12 = ins %cons 
         (cpy %cons (cpy %name (cpy "keep" 
         (cpy %cons (cpy %name (del "old" (ins "new" 
         (cpy %name (cpy "keep" 
         (ins %cons (ins %name (ins "new" 
                    (ins %name (ins "new" nil))))))))))))))

  j12-prf : applyES es12 (j1 ∷ []) ≡ just (j2 ∷ [])
  j12-prf = refl 

  j1ₐ j2ₐ : ⟦ I ∷ [] ⟧Aₐ*
  j1ₐ = ann-source (j1 ∷ []) es12 (indeed (j2 ∷ []))
  j2ₐ = ann-dest (j2 ∷ []) es12 (indeed (j1 ∷ []))

  extr : ⟦ I ∷ [] ⟧Aₐ* → Fixₐ SExpF
  extr (x ∷ []) = x

  j12-patch : Alμ
  j12-patch = AnnEnum.diffAlμ (extr j1ₐ) (extr j2ₐ)

  j3 j4 : SExp
  j3 = Def "lala" # (N "foo"
     ▹  Def "lele" # (N "bar" ▹ N "baz"))

  j4 = Def "lala" # (N "foo" ▹ (N "bar" ▹ N "baz"))

  es34 : ES (I ∷ []) (I ∷ [])
  es34 = cpy %def (cpy "lala" (cpy %nil 
        (cpy %cons (cpy %name (cpy "foo" 
        (del %def (del "lele" (del %nil 
        (cpy %cons (cpy %name (cpy "bar" 
        (cpy %name (cpy "baz" nil))))))))))))) 

  j3ₐ j4ₐ : ⟦ I ∷ [] ⟧Aₐ*
  j3ₐ = ann-source (j3 ∷ []) es34 (indeed (j4 ∷ []))
  j4ₐ = ann-dest (j4 ∷ []) es34 (indeed (j3 ∷ []))

  j34-patch : Alμ
  j34-patch = AnnEnum.diffAlμ (extr j3ₐ) (extr j4ₐ)

  test : applyAlμ j34-patch j3 ≡ just j4
  test = refl
