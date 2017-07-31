open import Prelude
open import Generic.Regular

module Regular.ES.Fixpoint (σμ : Sum) where

  open import Data.List using (_++_)
  open DecEq (Fix σμ) _≟Fix_
  
  -- Encoding patches a-la Lempsink
  -- 
  -- We shall be diffing lists of atoms
 
  -- Constructors Of an atom are either the constructors
  -- of the fixpoint in question or opaque types
  --  
  cof : Atom → Set
  cof I     = Constr σμ
  cof (K κ) = ⟦ κ ⟧K

  -- The Type Of an atom is either the type of
  -- a constructor or empty.
  tyof : (α : Atom) → cof α → Prod
  tyof I     c = typeOf σμ c
  tyof (K κ) c = []


  -- Edit-scripts a-la Lempsink are defined
  -- by:
  data ES : List Atom → List Atom → Set where
    nil : ES [] []
    ins : {i j : List Atom}{α : Atom}(c : cof α)
        → ES i (tyof α c ++ j)
        → ES i (α ∷ j)
    del : {i j : List Atom}{α : Atom}(c : cof α)
        → ES (tyof α c ++ i) j
        → ES (α ∷ i) j
    cpy : {i j : List Atom}{α : Atom}(c : cof α)
        → ES (tyof α c ++ i) (tyof α c ++ j)
        → ES (α ∷ i) (α ∷ j)

   -- * Claim
   --
   --   We can translate ES a-la Lemsink to our
   --   patch datatype
