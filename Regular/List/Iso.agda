open import Prelude
open import Generic.Regular

module Regular.List.Iso where

  -- * First we define lists of naturals in our Universe
  --   and prove they are isomorphic to List ℕ
  listF : Sum
  listF = [] ∷ ( K `ℕ ∷ I ∷ []) ∷ []

  list : Set
  list = Fix listF

  nil : list
  nil = ⟨ inj zero [] ⟩
 
  cons : ℕ → list → list
  cons n ns = ⟨ inj (suc zero) (n ∷ ns ∷ []) ⟩  

  gene : ⟦ listF ⟧S (List ℕ) → List ℕ
  gene (here px)                    = []
  gene (there (here (n ∷ ns ∷ []))) = n ∷ ns
  gene (there (there ()))

  iso-list₁ : list → List ℕ
  iso-list₁ = cata gene

  iso-list₂ : List ℕ → list
  iso-list₂ [] = nil
  iso-list₂ (x ∷ xs) = cons x (iso-list₂ xs)

  iso-list-ok₁ : ∀ l → iso-list₁ (iso-list₂ l) ≡ l
  iso-list-ok₁ [] = refl
  iso-list-ok₁ (x ∷ l) = cong₂ _∷_ refl (iso-list-ok₁ l)
 
  iso-list-ok₂ : ∀ l → iso-list₂ (iso-list₁ l) ≡ l
  iso-list-ok₂ ⟨ here [] ⟩                    = refl
  iso-list-ok₂ ⟨ there (here (n ∷ ns ∷ [])) ⟩ 
    = cong ⟨_⟩ (cong (there ∘ here) (cong (λ P → n ∷ P ∷ []) (iso-list-ok₂ ns)))
  iso-list-ok₂ ⟨ there (there ()) ⟩ 

  -- * Now, we are ready to define a diff between lists a-la unix
  --   and prove it isomorphic to our representation when
  --   instantiated to lists.
  
  data ListDiff : Set where
    dnil : ListDiff 
    dins : (n : ℕ) → ListDiff → ListDiff 
    ddel : (n : ℕ) → ListDiff → ListDiff 
    dcpy : (n : ℕ) → ListDiff → ListDiff 

  
  open import Regular.Functor (Fix listF) _≟Fix_
  open import Regular.Fixpoint listF
  
  go : ListDiff → Alμ
  go dnil       = {!!}
  go (dins n d) = {!!}
  go (ddel n d) = {!!}
  go (dcpy n d) = {!!}

  og : Alμ → ListDiff
  og (spn Scp)                           = dnil
  og (spn (Scns C r))                    = {!!}
  og (spn (Schg C₁ C₂ {q} {r₁} {r₂} al)) = {!!}
  og (ins C spμ)                         = {!!}
  og (del C spμ)                         = {!!}
