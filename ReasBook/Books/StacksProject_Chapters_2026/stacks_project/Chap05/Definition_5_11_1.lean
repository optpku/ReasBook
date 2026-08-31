module

import Mathlib.Order.KrullDimension
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.11.1: for an irreducible closed subset `Y` of `X`, the codimension `codim(Y, X)`
is the canonical order-theoretic notion `Order.coheight Y` in the poset `IrreducibleCloseds X`. -/
recall Order.coheight

/- Companion recall: for `Y : IrreducibleCloseds X`, the codimension of `Y` in `X` is also the
Krull dimension of the upper interval of irreducible closed subsets of `X` containing `Y`, via the
canonical theorem `Order.coheight_eq_krullDim_Ici`. -/
recall Order.coheight_eq_krullDim_Ici
