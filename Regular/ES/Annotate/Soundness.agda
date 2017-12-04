open import Prelude
open import Generic.Regular
open import Generic.RegularAnn

module Regular.ES.Annotate.Soundness (μσ : Sum) where

  open import Regular.Functor (Fix μσ) _≟Fix_
  open import Regular.Fixpoint μσ
    hiding (diffAlμ)
  open import Regular.Predicates.Applies.Fixpoint μσ
  open import Regular.Predicates.Normal.Fixpoint μσ

  open import Regular.ES.Annotate.FromPatch μσ
  open import Regular.ES.Annotate.Enum μσ

  open DecEq (Fix μσ) _≟Fix_
  open FixpointApplication

  sound-D : {x y : Fix μσ}{p : Alμ}
          → (np  : normAlμ-D p)
          → (hip : AppAlμ x y p)
          → diffAlμ (annAlμ-src hip) (annAlμ-dst hip) ≡ p

  sound-I : {x y : Fix μσ}{p : Alμ}
          → (np  : normAlμ-I p)
          → (hip : AppAlμ x y p)
          → diffAlμ (annAlμ-src hip) (annAlμ-dst hip) ≡ p

  sound-M : {x y : Fix μσ}{p : Alμ}
          → (np  : normAlμ-M p)
          → (hip : AppAlμ x y p)
          → diffAlμ (annAlμ-src hip) (annAlμ-dst hip) ≡ p


  sound-D p (AppDel C₁ Pxs y δ hip) = {!!}
  sound-D p (AppIns x C₁ Pys δ hip) = {!!}
  sound-D () (AppSpn x y s hip)

  sound-I p (AppIns x C₁ Pys δ hip) = {!!}
  sound-I p (AppSpn x y s hip)     = {!!}
  sound-I () (AppDel C₁ Pxs y δ hip) 

  sound-M p (AppSpn x y s hip) = cong spn {!!}
  sound-M () (AppIns x C₁ Pys δ hip) 
  sound-M () (AppDel C₁ Pxs y δ hip) 




  -- Here, we'll need to look at the patch;
  -- if it has no copies, it really is the 'stiff-diff' of
  -- x and y, if it has a copy, the proof goes by induction.
  --
  -- Now, obviously, everything happen modulo 'normal' patch.
  -- We could use some insight on that.
