/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Topology.Order.MonotoneConvergence

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

/- Proposition 1.4.2 lies in the order-theoretic monotone-convergence domain.

Relevant owner declarations sampled before refining:
* `Antitone`, the owner predicate for a decreasing sequence
* `antitone_nat_of_succ_le`, the canonical bridge from the textbook one-step decrease
  condition to the owner predicate on `ℕ`
* `tendsto_atTop_ciInf`, the owner monotone-convergence theorem for antitone nets
* `sInf_range`, the bridge from the indexed infimum `⨅ n, a n` to the textbook
  `sInf (Set.range a)`

Best owner abstraction:
* `tendsto_atTop_ciInf`

Primitive data:
* the source-facing one-step decrease condition `∀ n, a (n + 1) ≤ a n`
* `BddBelow (Set.range a)`

Derived API:
* `Antitone a`, via `antitone_nat_of_succ_le`
* convergence of `a` to `sInf (Set.range a)`

Source/core/bridge triage:
* source-facing: the proposition that a bounded-below relaxation sequence converges to the
  infimum of its range from the textbook one-step decrease hypothesis
* core/canonical: `tendsto_atTop_ciInf`
* bridge/view: `antitone_nat_of_succ_le` and `sInf_range`

This file therefore keeps only the source-facing theorem and targets the canonical proof route via
`antitone_nat_of_succ_le`, `tendsto_atTop_ciInf`, and `sInf_range` without introducing any local
wrapper around monotonicity or infimum convergence.
-/

/-- Proposition 1.4.2: A bounded-below relaxation sequence converges to the infimum of its
range. -/
-- Proof sketch: convert the successor-step decrease hypothesis to `Antitone a` via
-- `antitone_nat_of_succ_le`, then apply `tendsto_atTop_ciInf` and rewrite `⨅ n, a n` as
-- `sInf (Set.range a)` using `sInf_range`.
theorem relaxationSequence_tendsto_inf {α : Type u} [TopologicalSpace α]
    [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {a : ℕ → α}
    (ha : ∀ n : ℕ, a (n + 1) ≤ a n) (hbdd : BddBelow (Set.range a)) :
    Tendsto a atTop (nhds (sInf (Set.range a))) := by
  simpa [sInf_range] using tendsto_atTop_ciInf (antitone_nat_of_succ_le ha) hbdd
