open import Prelude
open import Generic.Multirec

module Multirec.Lab.RoseTree where


data Rose (a : Set) : Set where
  _▹_ : Rose a → List (Rose a) → Rose a

listPos : Fin 2
listPos = zero

rosePos : Fin 2
rosePos = suc zero

ListF : Sum _
ListF = ([]) ∷ (I rosePos ∷ I listPos ∷ []) ∷ []

`nil : Constr ListF
`nil = zero

`cons : Constr ListF
`cons = suc zero

RoseF : Sum _
RoseF = ((K `String ∷ I listPos ∷ [])) ∷ []

`rose : Constr RoseF
`rose = zero

MyFam : Fam _
MyFam = ListF ∷ RoseF ∷ []

Rose' : Set
Rose' =  Fix MyFam rosePos

List' : Set
List' =  Fix MyFam listPos

nil : List'
nil = ⟨ inj `nil [] ⟩

cons : Rose' → List' → List'
cons x xs = ⟨ inj `cons (x ∷ xs ∷ []) ⟩

rose : String → List' → Rose'
rose s xs = ⟨ inj `rose (s ∷ xs ∷ []) ⟩

leaf : String → Rose'
leaf s = rose s nil

open import Multirec.Functor (Fix MyFam) _≟Fix_ public
open import Multirec.Fixpoint MyFam
open FixpointApplication



-- * Unit tests
--- * Simply do nothing
patch : Alμ↓ rosePos
patch = spn Scp

x : (y : List') → ⟪ spn Scp ⟫μ y ≡ just y
x ⟨ here px ⟩ = refl
x ⟨ there x₁ ⟩ = refl


t₁ : Rose'
t₁ = rose "1" (cons (rose "2" nil) nil)

t₂ : List'
t₂ = cons (rose "1" nil) nil

t₃ : Rose'
t₃ = rose "2" (cons (rose "2" nil) nil)

p12 : Alμ rosePos listPos
p12 = del `rose (there "1" (here (spn Scp) []))

p23 : Alμ listPos rosePos
p23 = ins `rose (there "2" (here (spn Scp) []))


p13 : Alμ↓ rosePos
p13 = del `rose (there "1" (here (ins `rose (there "2" (here (spn Scp) []))) []))

y : ⟪ p13 ⟫μ t₁ ≡ just t₃
y = refl

