open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.Annotate.Soundness (μσ : Sum) where

  open import Regular.Functor (Fix μσ) _≟Fix_
  open import Regular.Fixpoint μσ
    hiding (diffAlμ)
  open import Regular.Predicates.Applies.Fixpoint μσ

  open import Regular.ES.Annotate.FromPatch μσ
  open import Regular.ES.Annotate.Enum μσ

  open DecEq (Fix μσ) _≟Fix_
  open FixpointApplication

  sound : {x y : Fix μσ}{p : Alμ}
        → (hip : AppAlμ x y p)
        → diffAlμ (annAlμ-src hip) (annAlμ-dst hip) ≡ p

  

  sound (AppSpn x y s hip) = cong spn {!!}

  -- Here, we'll need to look at the patch;
  -- if it has no copies, it really is the 'stiff-diff' of
  -- x and y, if it has a copy, the proof goes by induction.
  --
  -- Now, obviously, everything happen modulo 'normal' patch.
  -- We could use some insight on that.
  sound (AppIns x C₁ Pys δ hip) 
    with AppCtxIns⇒AppAlμ hip
  ...| ⟨ z ⟩ , k = cong id {!!}
  sound (AppDel C₁ Pxs y δ hip) = {!!}
