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
