module Everything where

-- * Our Prelude
open import Prelude

-- * Generic Programming
open import Generic.Opaque
open import Generic.Regular
open import Generic.Multirec

-- * Regular patches

-- ** Internals (Data Type definitions and enumeration functions)
open import Regular.Internal.Functor
open import Regular.Internal.EnumFunctor
open import Regular.Internal.Fixpoint
open import Regular.Internal.EnumFix

-- ** Renamings
open import Regular.Fixpoint
open import Regular.Functor

-- ** Predicates over Patches
--
-- *** Identity Patches; correctness is inside
open import Regular.Predicates.Identity.Functor
open import Regular.Predicates.Identity.Fixpoint

-- *** Domain of a patch;
open import Regular.Predicates.Domain.Functor
open import Regular.Predicates.Domain.Fixpoint

-- **** And its correctness proof.
open import Regular.Predicates.Domain.Correctness.Functor
open import Regular.Predicates.Domain.Correctness.Fixpoint

-- *** Disjoint Patches
open import Regular.Predicates.Disjoint.Functor
open import Regular.Predicates.Disjoint.Fixpoint

-- ** Merging Patches
open import Regular.Operations.Merge.Functor
open import Regular.Operations.Merge.Fixpoint

-- *** And the commuation proof
open import Regular.Operations.Merge.Commutes.Functor
open import Regular.Operations.Merge.Commutes.Fixpoint

-- ** Laboratories
open import Regular.Lab.2-3-Tree
open import Regular.Lab.SExp
open import Regular.Lab.ForkTree

-- ** Experimental
open import Regular.ES.Fixpoint
