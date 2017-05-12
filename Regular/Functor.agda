open import Prelude
open import Generic.Regular

module Regular.Functor
           (Rec : Set)
           (_≟Rec_ : (x y : Rec) → Dec (x ≡ y))
       where
 
  open import Data.List using (monadPlus)

  open import Regular.Internal.Functor Rec _≟Rec_
    public
  open import Regular.Internal.EnumFunctor Rec _≟Rec_ List Data.List.monadPlus
    public
    
  
