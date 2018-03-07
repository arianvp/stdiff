open import Prelude
open import Generic.Multirec

module Multirec.Lab.RoseTree where


data Rose (a : Set) : Set where
  _▹_ : Rose a → List (Rose a) → Rose a

listPos : Fin 2
listPos = zero

rosePos : Fin 2
rosePos = suc zero

ListF : Sum 2
ListF = ([]) ∷ (I rosePos ∷ I listPos ∷ []) ∷ []

RoseF : Sum 2
RoseF = ((K `String ∷ I listPos ∷ [])) ∷ []

MyFam : Fam 2
MyFam = ListF ∷ RoseF ∷ []


Rose' : Set
Rose' =  Fix MyFam rosePos

List' : Set
List' =  Fix MyFam listPos


nil : List'
nil = ⟨ (here []) ⟩


leaf : String → Rose'
leaf s = ⟨ here (s ∷ nil ∷ []) ⟩

open import Multirec.Functor (Fix MyFam) _≟Fix_ public
open import Multirec.Fixpoint MyFam


