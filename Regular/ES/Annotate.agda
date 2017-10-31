open import Prelude
open import Generic.Regular
open import Generic.RegularAnn
-- * Claim
--
--   We can translate ES a-la Lemsink to our
--   patch datatype
--
--   The way to do so is to traverse the source and
--   destination trees together with their edit-script.
-- 
--   We start by defining the cost semantics and 
--   the '⊓' operation
--
module Regular.ES.Annotate (σμ : Sum) where

  open import Data.List using (_++_)
  open import Regular.ES.Fixpoint σμ
 
  -- Handy synonym;
  ⟦_⟧Aₐ* : List Atom → Set
  ⟦_⟧Aₐ* = All (λ α → ⟦ α ⟧A (Fixₐ σμ))

  -- It is handy to be able to invert patches; make some hypothesis
  -- simpler
  inv-es : ∀{txs tys} → ES txs tys → ES tys txs
  inv-es nil = nil
  inv-es (cpy c es) = cpy c (inv-es es)
  inv-es (ins c es) = del c (inv-es es)
  inv-es (del c es) = ins c (inv-es es)

  injₐ' : {α : Atom}(c : cof α) → Ann → ⟦ tyof α c ⟧P (Fixₐ σμ) → ⟦ α ⟧A (Fixₐ σμ)
  injₐ' {K κ} c ann xs = c
  injₐ' {I}   c ann xs = ⟨ ann , inj c xs ⟩

  insₐ* : ∀{α αs}(c : cof α) → Ann → ⟦ tyof α c ++ αs ⟧Aₐ* → ⟦ α ∷ αs ⟧Aₐ*
  insₐ* {α} {αs} c ann xs 
    = let (xs₀ , xs₁) = split-all (tyof α c) αs xs
       in injₐ' {α} c ann xs₀ ∷ xs₁

  ann-source : ∀{txs tys}(xs : ⟦ txs ⟧A*)(p : ES txs tys)
             → (hip : IsJust (applyES p xs))
             → ⟦ txs ⟧Aₐ*
  ann-source xs       nil hip      = []
  ann-source xs       (ins c p) hip = ann-source xs p (IsJust-unmap hip)
  ann-source {tx ∷ txs} (x ∷ xs) (del c p) hip 
    with match' {tx} c x
  ...| nothing = ⊥-elim (IsJust-magic hip)
  ...| just dx = insₐ* c M (ann-source (++-all (tyof tx c) txs dx xs) p hip)
  ann-source {tx ∷ txs} (x ∷ xs) (cpy c p) hip 
    with match' {tx} c x
  ...| nothing = ⊥-elim (IsJust-magic hip)
  ...| just dx = insₐ* c C (ann-source (++-all (tyof tx c) txs dx xs) p (IsJust-unmap hip))

  ann-dest : ∀{txs tys}(ys : ⟦ tys ⟧A*)(p : ES txs tys)
           → (hip : IsJust (applyES (inv-es p) ys))
           → ⟦ tys ⟧Aₐ*
  ann-dest ys       nil       hip = []
  ann-dest ys       (del c p) hip = ann-dest ys p (IsJust-unmap hip)
  ann-dest {_} {ty ∷ tys} (y ∷ ys) (ins c p) hip 
    with match' {ty} c y 
  ...| nothing = ⊥-elim (IsJust-magic hip)
  ...| just dy = insₐ* c M (ann-dest (++-all (tyof ty c) tys dy ys) p hip)
  ann-dest {_} {ty ∷ tys} (y ∷ ys) (cpy c p) hip 
    with match' {ty} c y 
  ...| nothing = ⊥-elim (IsJust-magic hip)
  ...| just dy = insₐ* c C (ann-dest (++-all (tyof ty c) tys dy ys) p (IsJust-unmap hip))

