open import Prelude
open import Generic.Regular

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

  open import Regular.Internal.ForkEnum.FunctorFix SExpF as BE
    using ()

  p13* : Alμ
  p13* = BE.crush (BE.diffForkAlμ k1 k3)

  q1 q2 : SExp

  q1 = Def "func" #
      (N "import" ▹ (N "flag1" ▹ N "trash1" ▹ N "trash2" ▹ #)
                  ▹ (N "flag2" ▹ N "keep1" ▹ #)
                  ▹ (N "flag3" ▹ N "trash3" ▹ #)
                  ▹ (N "flag4" ▹ N "keep4" ▹ #)
                  ▹ (N "flag5" ▹ N "keep5" ▹ #)
                  ▹ #)

  q2 = Def "func" #
      (N "import" ▹ (N "flag2" ▹ N "keep1" ▹ N "new" ▹ #)
                  ▹ (N "flag4" ▹ N "keep4" ▹ #)
                  ▹ (N "flag5" ▹ N "keep5" ▹ #)
                  ▹ #)

  q12-exp : Alμ
  q12-exp = spn (Scns %def 
                (set ("func" , "func") 
                ∷ fix (spn Scp) 
                ∷ fix (spn (Scns %cons 
                      (fix (spn (Scns %name (set ("import" , "import") ∷ []))) 
                      ∷ fix (del %cons (there (N "flag1" ▹ N "trash1" ▹ N "trash2" ▹ #)
                                       (here (spn (Scns %cons 
                        (fix (spn (Scns %cons 
                          (fix (spn Scp) 
                          ∷ fix (spn (Scns %cons 
                              (fix (spn Scp) 
                              ∷ fix (ins %cons (there (N "new") (here (spn Scp) []))) 
                              ∷ []))) 
                          ∷ []))) 
                        ∷ fix (del %cons (there (N "flag3" ▹ N "trash3" ▹ #) 
                                         (here (spn Scp) []))) 
                        ∷ []))) []))) 
                      ∷ []))) 
                ∷ []))

  q12-exp-correct : applyAlμ q12-exp q1 ≡ just q2
  q12-exp-correct = refl
  
  q12-exp-cost : ℕ
  q12-exp-cost = costAlμ q12-exp
  
  q12* : Alμ
  q12* = BE.crush (BE.diffForkAlμ q1 q2)

  q12*-cost : ℕ
  q12*-cost = costAlμ q12*

  s1 s2 : SExp

  s1 = Def "func" #
      (N "import" ▹ (N "trash1" ▹ #)
                  ▹ (N "keep" ▹ #)
                  ▹ (N "trash2" ▹ #)
                  ▹ N "keep"
                  ▹ #)

  s2 = Def "func" #
       (N "import" ▹ (N "keep" ▹ N "new" ▹ #)
                  ▹ N "keep"
                  ▹ #)

  s12-exp : Alμ
  s12-exp = spn (Scns %def 
                (set ("func" , "func") 
                ∷ fix (spn Scp) 
                ∷ fix (spn (Scns %cons 
                  (fix (spn Scp) 
                  ∷ fix (del %cons (there (N "trash1" ▹ #) 
                                   (here 
                    (spn (Scns %cons 
                         (fix (spn (Scns %cons 
                              (fix (spn Scp) 
                               ∷ fix (ins %cons (there (N "new") (here (spn Scp) []))) 
                               ∷ []))) 
                         ∷ fix (del %cons (there (N "trash2" ▹ #) 
                                          (here (spn Scp) []))) 
                         ∷ []))) []))) 
                  ∷ [])))
                ∷ []))

  s12-exp-correct : applyAlμ s12-exp s1 ≡ just s2
  s12-exp-correct = refl
  
  s12-exp-cost : ℕ
  s12-exp-cost = costAlμ s12-exp
  
  s12* : List BE.ForkAlμ 
  s12* =  (BE.diffForkAlμ s1 s2)

  s12*-cost : ℕ
  s12*-cost = costAlμ (BE.crush s12*)
