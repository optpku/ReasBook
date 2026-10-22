/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Order.ConditionallyCompleteLattice.Indexed

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Theorem 1.10.1 lies in the order-theoretic weak-duality domain.

Relevant owner declarations sampled before refining:
* `iSup_iInf_le_iInf_iSup`, the complete-lattice maximin `≤` minimax owner theorem
* `ciSup_le`, the conditionally complete introduction rule for indexed suprema
* `le_ciInf`, the conditionally complete introduction rule for indexed infima
* `ciInf_le` and `le_ciSup`, the slice-evaluation rules supplying the pointwise comparison

Best owner abstraction:
* the indexed `⨅`/`⨆` API of `ConditionallyCompleteLattice`

Primitive data:
* the payoff `F : Q₁ → Q₂ → α`
* nonempty index types `Q₁`, `Q₂`
* lower bounded `x`-slices and upper bounded `u`-slices

Derived API:
* the source-facing weak-duality inequality
  `⨆ u, ⨅ x, F x u ≤ ⨅ x, ⨆ u, F x u`

Source/core/bridge triage:
* source-facing: the textbook weak-duality inequality
* core/canonical: the indexed `⨅`/`⨆` operators in a `ConditionallyCompleteLattice`
* bridge/view: `iSup_iInf_le_iInf_iSup`, the complete-lattice analogue that identifies the same
  owner pattern at a stronger ambient level

Accordingly this file keeps only the source-facing theorem and reuses the canonical indexed
`iInf`/`iSup` API directly, rather than introducing any local maximin/minimax wrapper layer.
-/

/-- Theorem 1.10.1: for a payoff on nonempty index sets valued in a conditionally complete
lattice, if each lower slice `{F(x, u) | x ∈ Q₁}` is bounded below and each upper slice
`{F(x, u) | u ∈ Q₂}` is bounded above, then the maximin value is bounded above by the minimax
value. Specializing to `α = ℝ` recovers the textbook real-valued weak-duality inequality. -/
theorem maximin_le_minimax
    {Q₁ : Type u} {Q₂ : Type v} {α : Type w} [ConditionallyCompleteLattice α]
    [Nonempty Q₁] [Nonempty Q₂] (F : Q₁ → Q₂ → α)
    (hbelow : ∀ u, BddBelow (Set.range fun x ↦ F x u))
    (habove : ∀ x, BddAbove (Set.range (F x))) :
    (⨆ u, ⨅ x, F x u) ≤ ⨅ x, ⨆ u, F x u := by
  -- Fix a column index and reduce the target to the corresponding inequality for that slice.
  refine ciSup_le fun u ↦ ?_
  -- For this fixed column, prove it is below every row supremum and then introduce the infimum.
  refine le_ciInf fun x ↦ ?_
  -- Compare the column infimum to the entry `F x u`, then compare that entry to the row supremum.
  exact (ciInf_le (hbelow u) x).trans (le_ciSup (habove x) u)
