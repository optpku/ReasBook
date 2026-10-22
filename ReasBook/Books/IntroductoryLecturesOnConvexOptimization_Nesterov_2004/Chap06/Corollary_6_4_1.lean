/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WeightSequenceNotation

universe u

section

variable {E : Type u}

/- Corollary 6.4.1 lies in Chapter 6's accumulated-weight / oracle-error normalization domain.

Sampled owner-style declarations:
- `A[a](t)` from `Definition_6_53`, the chapter owner for the accumulated weights `A_t`;
- `linearOptimizationOracleErrorBound` from `Definition_6_54`, the chapter owner for the error
  term `B_{ν,t}`;
- `objective_gap_le_error_bound_div_accumulated_weight` from `Theorem_6_13`, the canonical
  normalization theorem upstream in the same chapter.

Best owner abstraction:
- source-facing: the iterate-specialized corollary at the textbook point `x_t` relative to
  `x_*`;
- core/canonical: `objective_gap_le_error_bound_div_accumulated_weight`;
- bridge/view: the specialization `xt = x t`, `xs = xStar`.

Primitive data:
- the iterate family `x`, reference point `xStar`, weights `a`, and error-term parameters;
- the positivity hypothesis `0 < A[a](t)`;
- the weighted inequality at the specific iterate `x t`.

Derived API:
- the normalized composite-objective gap bound at time `t`.

This item therefore keeps no parallel arithmetic wrapper. It remains theorem-shaped because the
textbook corollary is a genuine source-facing specialization of the chapter owner theorem, not an
exact-interface duplicate suitable for pure `recall`. -/
-- Proof sketch: specialize Theorem 6.13 to `xt = x t` and `xs = xStar`.
/-- Corollary 6.4.1: for any iterate index `t`, if `A_t > 0` and the weighted
composite-objective gap at `x_t` relative to `x_*` is bounded by `B_{ν,t}`, then equation
`(6.4.17)` holds:
`\bar f(x_t) - \bar f(x_*) ≤ B_{ν,t} / A_t`, where
`B_{ν,t} = linearOptimizationOracleErrorBound V₀ a G_ν D ν t`. The subsequent standard-weight
rates `(6.4.18)`--`(6.4.20)` are referenced but not restated here. -/
theorem composite_objective_gap_le_error_bound_div_accumulated_weight
    (fbar : E → ℝ) (x : ℕ → E) (xStar : E) (a : ℕ → ℝ) (V0 Gν D : ℝ)
    {ν : ℝ} {t : ℕ}
    (hAt : 0 < A[a](t))
    (hweighted :
      A[a](t) * (fbar (x t) - fbar xStar) ≤
        linearOptimizationOracleErrorBound V0 a Gν D ν t) :
    fbar (x t) - fbar xStar ≤
      linearOptimizationOracleErrorBound V0 a Gν D ν t / A[a](t) := by
  simpa using
    objective_gap_le_error_bound_div_accumulated_weight
      fbar (x t) xStar a V0 Gν D hAt hweighted

end
