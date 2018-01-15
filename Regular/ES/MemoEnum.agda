open import Prelude
open import Generic.Regular

module Regular.ES.MemoEnum (σμ : Sum) where

  open import Data.List using (_++_)
  open DecEq (Fix σμ) _≟Fix_
  open import Data.Maybe using (monadPlus)
  open RawMonadPlus {lz} monadPlus

  open import Regular.ES.Fixpoint σμ

  -- * Here we write the the efficient memoized
  --   enumeration function
  --   Adapted from Lempsink's paper
  --   

  data EST : List Atom → List Atom → Set where
    nn : ES [] [] → EST [] []
    nc : {tys : List Atom}{y : Atom}(c : cof y)
       → ES  [] (y ∷ tys)
       → EST [] (tyof y c ++ tys)
       → EST [] (y ∷ tys)
    cn : {txs : List Atom}{x : Atom}(c : cof x)
       → ES  (x ∷ txs)         []
       → EST (tyof x c ++ txs) []
       → EST (x ∷ txs)         []
    cc : {txs tys : List Atom}{x y : Atom}
       → (cx : cof x)(cy : cof y)
       → ES  (x ∷ txs)          (y ∷ tys)
       → EST (x ∷ txs)          (tyof y cy ++ tys)
       → EST (tyof x cx ++ txs) (y ∷ tys)
       → EST (tyof x cx ++ txs) (tyof y cy ++ tys)
       → EST (x ∷ txs)          (y ∷ tys)

  getDiff : ∀ {txs tys} → EST txs tys → ES txs tys
  getDiff (nn x)             = x
  getDiff (nc c x _)         = x
  getDiff (cn c x _)         = x
  getDiff (cc cx cy x _ _ _) = x

  best : ∀{txs tys tx ty}(cx : cof tx)(cy : cof ty)
       → EST (tx ∷ txs) (tyof ty cy ++ tys)
       → EST (tyof tx cx ++ txs) (ty ∷ tys)
       → EST (tyof tx cx ++ txs) (tyof ty cy ++ tys)
       → ES (tx ∷ txs) (ty ∷ tys)
  best {_} {_} {I}    {K κ₂} cx cy i d c 
    = ins cy (getDiff i) ⊓ del cx (getDiff d)
  best {_} {_} {K κ₁} {I}    cx cy i d c 
    = ins cy (getDiff i) ⊓ del cx (getDiff d)
  best {_} {_} {I}    {I}    cx cy i d c 
    with cx ≟F cy
  ...| no  _    = ins cy (getDiff i) ⊓ del cx (getDiff d)
  ...| yes refl = ins cy (getDiff i) ⊓ (del cx (getDiff d) ⊓ cpy cx (getDiff c))
  best {_} {_} {K κ₁} {K κ₂} cx cy i d c
    with κ₁ ≟Konst κ₂ 
  ...| no _ = ins cy (getDiff i) ⊓ del cx (getDiff d)
  ...| yes refl 
    with cx ≟K cy
  ...| no  _    = ins cy (getDiff i) ⊓ del cx (getDiff d)
  ...| yes refl = ins cy (getDiff i) ⊓ (del cx (getDiff d) ⊓ cpy cx (getDiff c))

  extracti : ∀{txs tys ty}{R : Set}
           → EST txs (ty ∷ tys)
           → ((cy : cof ty) → EST txs (tyof ty cy ++ tys) → R) → R
  extracti (nc cy _ i)       k = k cy i
  extracti (cc _ cy _ i _ _) k = k cy i

  extractd : ∀{txs tys tx}{R : Set}
           → EST (tx ∷ txs) tys
           → ((cx : cof tx) → EST (tyof tx cx ++ txs) tys → R) → R
  extractd (cn cx _ d)       k = k cx d
  extractd (cc cx _ _ _ d _) k = k cx d

  {-# TERMINATING #-}
  diffT : ∀{txs tys} → ⟦ txs ⟧A* → ⟦ tys ⟧A* → EST txs tys

  extendi : ∀{txs tys tx}(cx : cof tx)
          → EST (tyof tx cx ++ txs) tys → EST (tx ∷ txs) tys
  extendi {_} {[]}       cx d 
    = cn cx (del cx (getDiff d)) d
  extendi {_} {ty ∷ tys} cx d 
    = extracti d (λ cy c 
    → let i = extendi cx c 
       in cc cx cy (best cx cy i d c) i d c)

  extendd : ∀{txs tys ty}(cx : cof ty)
          → EST txs (tyof ty cx ++ tys) → EST txs (ty ∷ tys) 
  extendd {[]}       cy i
    = nc cy (ins cy (getDiff i)) i
  extendd {tx ∷ txs} cy i
    = extractd i (λ cx c
    → let d = extendd cy c
       in cc cx cy (best cx cy i d c) i d c)

  diffT []       []       = nn nil
  diffT {α ∷ αs} (x ∷ xs) []       
    = let (cx , dx) = sop' {α} x
          d = diffT (++-all (tyof α cx) αs dx xs) []
       in cn cx (del cx (getDiff d)) d
  diffT {_} {β ∷ βs} []       (y ∷ ys) 
    = let (cy , dy) = sop' {β} y
          i = diffT [] (++-all (tyof β cy) βs dy ys)
       in nc cy (ins cy (getDiff i)) i
  diffT {α ∷ αs} {β ∷ βs} (x ∷ xs) (y ∷ ys) 
    = let (cx , dx) = sop' {α} x
          (cy , dy) = sop' {β} y
          c = diffT (++-all (tyof α cx) αs dx xs)
                    (++-all (tyof β cy) βs dy ys)
          i = extendi {tx = α} cx c
          d = extendd {ty = β} cy c
       in cc cx cy (best cx cy i d c) i d c
