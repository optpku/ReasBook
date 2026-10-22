/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Asymptotics Filter

/-
Primary domain: scalar asymptotic convergence rates for real optimization error sequences.

Source/core/bridge triage for Definition 1.6.9:
* source-facing: `HasConvergenceRateOfOrder r φ`
* core/canonical: the eventual comparison bound
  `∃ C > 0, ∀ᶠ N in atTop, r N ≤ C * φ N`, packaged with
  `IsOptimizationErrorSequence r`
* bridge/view: the asymptotic consequence `HasConvergenceRateOfOrder.isBigO`, and direct
  downstream use of the square-root specialization
  `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`

Relevant declarations sampled before refining:
* `Asymptotics.isBigO_iff'`
* `Asymptotics.IsBigO.of_bound`
* `HasGeometricRateOfConvergence.isBigO` in `Definition_1_2_6.lean`
* `HasEventuallySuperlinearErrorBound r 0 c 0` in `Definition_1_2_7.lean`, a neighboring
  chapter example where a specialized owner is reused directly instead of wrapped by a duplicate
  local predicate

Owner abstraction:
* the source-facing eventual comparison bound from Definition 1.6.9, packaged with the
  optimization-error-sequence hypothesis; bare `r =O[atTop] φ` is only a companion bridge
  because it inserts absolute values

Primitive data:
* the sequence `r`
* the comparison rate `φ`
* the nonnegativity and convergence-to-zero hypothesis `IsOptimizationErrorSequence r`
* a witness `C > 0` and the eventual bound `r N ≤ C * φ N` along `atTop`

Derived API:
* the projection lemmas `error` and `bound`
* the asymptotic bridge `isBigO`
-/

/-- An optimization error sequence is a nonnegative real sequence converging to `0`. -/
def IsOptimizationErrorSequence (r : ℕ → ℝ) : Prop :=
  (∀ N, 0 ≤ r N) ∧ Tendsto r atTop (nhds 0)

namespace IsOptimizationErrorSequence

variable {r : ℕ → ℝ}

theorem nonneg (h : IsOptimizationErrorSequence r) (N : ℕ) : 0 ≤ r N :=
  h.1 N

theorem tendsto_zero (h : IsOptimizationErrorSequence r) : Tendsto r atTop (nhds 0) :=
  h.2

end IsOptimizationErrorSequence

/-- Definition 1.6.9: a minimization process has convergence rate of order `φ` when its
optimization error sequence is nonnegative, converges to `0`, and is eventually bounded above
by a positive multiple of `φ`. -/
def HasConvergenceRateOfOrder (r φ : ℕ → ℝ) : Prop :=
  IsOptimizationErrorSequence r ∧ ∃ C > 0, ∀ᶠ N in atTop, r N ≤ C * φ N

namespace HasConvergenceRateOfOrder

variable {r φ : ℕ → ℝ}

theorem error (h : HasConvergenceRateOfOrder r φ) : IsOptimizationErrorSequence r :=
  h.1

theorem bound (h : HasConvergenceRateOfOrder r φ) :
    ∃ C > 0, ∀ᶠ N in atTop, r N ≤ C * φ N :=
  h.2

/-- A convergence rate of order `φ` yields the canonical asymptotic estimate `r =O[atTop] φ`. -/
-- Proof sketch: the source-facing eventual bound already forces `φ` to be eventually nonnegative,
-- because `r` is nonnegative and the comparison constant is positive. Convert the resulting
-- norm bound directly with `IsBigO.of_bound`.
theorem isBigO
    (h : HasConvergenceRateOfOrder r φ) :
    r =O[atTop] φ := by
  obtain ⟨C, hC, hbound⟩ := h.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hbound] with N hN
  have hrN : 0 ≤ r N := h.error.nonneg N
  have hφN : 0 ≤ φ N := nonneg_of_mul_nonneg_right (hrN.trans hN) hC
  simpa [Real.norm_eq_abs, abs_of_nonneg hrN, abs_of_nonneg hφN] using hN

end HasConvergenceRateOfOrder
