/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

/- Definition 5.4.7.13 lies in the lifted finite-family log-sum-exp barrier domain.

Sampled owner declarations:
* `exponentialConeBarrier` from `Definition_5_4_7_10`, the scalar barrier summed coordinatewise
  upstream;
* `liftedConeLogSumExp` from `Definition_5_4_7_12`, the lifted finite-family cone owner;
* `liftedConeLogSumExpBarrier` from `Theorem_5_4_7_7`, the Chapter 5 owner for the ambient lifted
  barrier;
* `liftedConeLogSumExpBarrier_apply` from `Theorem_5_4_7_7`, the canonical coordinate-sum bridge.

Best owner abstraction:
* source-facing: the lifted finite-family barrier `Ψ_L`;
* core/canonical: the upstream owner `liftedConeLogSumExpBarrier`;
* bridge/view: specialization to `ι = Fin n` for the textbook `n`-coordinate presentation.

Primitive data:
* none in this file; the owner and its bridges are already defined upstream.

Derived API:
* the recalled owner `liftedConeLogSumExpBarrier`;
* the recalled coordinate-sum bridge `liftedConeLogSumExpBarrier_apply`;
* the recalled positive-branch formula `liftedConeLogSumExpBarrier_apply_formula`.

This item is recall-only. The public surface stays at the same arbitrary finite index type as
Definitions 5.4.7.11 and 5.4.7.12; `Fin n` is only the standard specialization bridge. -/

/- The textbook `n`-coordinate barrier is the `ι = Fin n` specialization of the finite-family
owner. -/
example (n : ℕ+) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ × ℝ → ℝ :=
  liftedConeLogSumExpBarrier

/- Definition 5.4.7.13 recalls the Chapter 5 owner for the lifted finite-family log-sum-exp
barrier. -/
recall liftedConeLogSumExpBarrier {ι : Type v} [Fintype ι] :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι × ℝ × ℝ → ℝ

/- The ambient owner is recalled through its canonical coordinate-sum bridge. -/
recall liftedConeLogSumExpBarrier_apply
    {ι : Type v} [Fintype ι] (x y : EuclideanSpace ℝ ι) (t τ : ℝ) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      ∑ i : ι, exponentialConeBarrier ((x i - t, y i), τ)

/- On the positive branch, the coordinate-sum owner reduces to the textbook logarithmic formula.
-/
recall liftedConeLogSumExpBarrier_apply_formula
    {ι : Type v} [Fintype ι] (x y : EuclideanSpace ℝ ι) (t τ : ℝ)
    (hτ : 0 < τ) (hy : ∀ i : ι, 0 < y i) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      -∑ i : ι,
        (Real.log (t + τ * Real.log (y i) - x i - τ * Real.log τ) +
          Real.log (y i) + Real.log τ)

end
