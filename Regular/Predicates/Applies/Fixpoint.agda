open import Prelude
open import Generic.Regular

module Regular.Predicates.Applies.Fixpoint (μσ : Sum) where

  open import Regular.Internal.Fixpoint μσ
  open import Regular.Internal.Functor (Fix μσ) _≟Fix_

  data AppAlμ : Fix μσ → Fix μσ → Alμ → Set

  open import Regular.Predicates.Applies.Functor
    (Fix μσ) _≟Fix_ Alμ AppAlμ
    public

  data AppCtxDel : ∀{π} 
                 → ⟦ π ⟧P (Fix μσ)
                 → Fix μσ  
                 → Ctx π
                 → Set
      where
    AppDelHere : ∀{π}(x y : Fix μσ)(spμ : Alμ)
               → (pxs pxs' : ⟦ π ⟧P (Fix μσ))
               → AppAlμ x y spμ
               → AppCtxDel (x ∷ pxs) y (here spμ pxs')

    AppDelThere : ∀{α π}(x x' : ⟦ α ⟧A (Fix μσ))(y : Fix μσ)
                → (pxs : ⟦ π ⟧P (Fix μσ))
                → (δ : Ctx π)
                → AppCtxDel pxs y δ
                → AppCtxDel (x ∷ pxs) y (there {α} x' δ)

  data AppCtxIns : ∀{π} 
                 → Fix μσ  
                 → ⟦ π ⟧P (Fix μσ)
                 → Ctx π
                 → Set
      where
    AppInsHere : ∀{π}(x y : Fix μσ)(spμ : Alμ)
               → (pys : ⟦ π ⟧P (Fix μσ))
               → AppAlμ x y spμ
               → AppCtxIns x (y ∷ pys) (here spμ pys)

    AppInsThere : ∀{α π}(x : Fix μσ)(y : ⟦ α ⟧A (Fix μσ))
                → (pys : ⟦ π ⟧P (Fix μσ))
                → (δ : Ctx π)
                → AppCtxIns x pys δ
                → AppCtxIns x (y ∷ pys) (there {α} y δ)

  data AppAlμ where
    AppSpn : (x y : ⟦ μσ ⟧S (Fix μσ))(s : Patch Alμ μσ)
           → AppS x y s
           → AppAlμ ⟨ x ⟩ ⟨ y ⟩ (spn s)

    AppIns : (x : Fix μσ)(C : Constr μσ)
           → (Pys : ⟦ typeOf μσ C ⟧P (Fix μσ))
           → (δ : Ctx (typeOf μσ C))
           → AppCtxIns x Pys δ
           → AppAlμ x ⟨ inj C Pys ⟩ (ins C δ)
 
    AppDel : (C : Constr μσ)
           → (Pxs : ⟦ typeOf μσ C ⟧P (Fix μσ))
           → (y : Fix μσ)
           → (δ : Ctx (typeOf μσ C))
           → AppCtxDel Pxs y δ
           → AppAlμ ⟨ inj C Pxs ⟩ y (del C δ)
                     
