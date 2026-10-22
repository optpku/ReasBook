/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_54

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WeightSequenceNotation

universe u

section

variable {X : Type u}

/- Theorem 6.13 lies in Chapter 6's accumulated-weight / oracle-error normalization domain.

Sampled owner-style declarations:
- `accumulatedWeights` with notation `A[a](t)` in `Definition_6_53`, the chapter owner for the
  accumulated weights `A_t`;
- `linearOptimizationOracleErrorBound` in `Definition_6_54`, the chapter owner for the error term
  `B_{ν,t}`;
- `weighted_objective_upper_bound_of_linear_oracle_composite_method` in `Theorem_6_12`, the
  upstream weighted estimate that Theorem 6.13 normalizes;
- `le_div_iff₀`, the arithmetic theorem used internally to divide by a positive scalar.

Best owner abstraction:
- source-facing owners `A[a](t)` and `linearOptimizationOracleErrorBound V₀ a G_ν D ν t`.

Primitive data:
- the positivity hypothesis `hAt : 0 < A[a](t)`;
- the weighted inequality
  `A[a](t) * (fbar xt - fbar xs) ≤ linearOptimizationOracleErrorBound V₀ a G_ν D ν t`.

Derived API:
- the normalized objective-gap bound obtained by dividing by `A[a](t)`.

Source/core/bridge triage:
- source-facing: the Chapter 6 step from the weighted bound to the normalized gap estimate;
- core/canonical: the chapter owners `accumulatedWeights` and
  `linearOptimizationOracleErrorBound`;
- bridge/view: this theorem, whose proof internally reuses `le_div_iff₀`.

The interval condition `ν ∈ (0, 1]` belongs to the upstream construction of
`linearOptimizationOracleErrorBound`; it is not primitive data for this normalization step.
-/
-- Proof sketch: apply `le_div_iff₀` to divide the Chapter 6 weighted objective-gap inequality by
-- the positive scalar `A[a](t)`.
/-- Theorem 6.13: if `A_t > 0` and the weighted objective gap satisfies
`A_t (\bar f(x_t) - \bar f(x_s)) ≤ B_{ν,t}` with
`B_{ν,t} = linearOptimizationOracleErrorBound V₀ a G_ν D ν t`, then
`\bar f(x_t) - \bar f(x_s) ≤ B_{ν,t} / A_t`. Here `t : ℕ` encodes the hypothesis `t ≥ 0`. -/
theorem objective_gap_le_error_bound_div_accumulated_weight
    (fbar : X → ℝ) (xt xs : X) (a : ℕ → ℝ) (V0 Gν D : ℝ)
    {ν : ℝ} {t : ℕ}
    (hAt : 0 < A[a](t))
    (hweighted :
      A[a](t) * (fbar xt - fbar xs) ≤
        linearOptimizationOracleErrorBound V0 a Gν D ν t) :
    fbar xt - fbar xs ≤
      linearOptimizationOracleErrorBound V0 a Gν D ν t / A[a](t) := by
  exact (le_div_iff₀ hAt).2 (by simpa [mul_comm] using hweighted)

end
