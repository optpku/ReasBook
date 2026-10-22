/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_53

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators WeightSequenceNotation

/- Definition 6.66 lies in the Chapter 6 strong-convex conditional-gradient error-term domain.

Mandatory domain-style sampling:
- `accumulatedWeights` with notation `A[a](t)` in `Definition_6_53`, the chapter owner for the
  accumulated weights `A_t`;
- `linearOptimizationOracleErrorBound` in `Definition_6_54`, the nearby Chapter 6 owner for the
  non-strongly-convex analogue `B_{ν,t}`;
- `weighted_objective_upper_bound_of_strongly_convex_linear_oracle_composite_method` in
  `Theorem_6_15`, the direct downstream theorem that consumes this owner;
- `Ψ ∈ 𝒮^0_σΨ(Q)` in `Definition_6_65`, the surrounding strong-convexity owner used with this
  error term downstream.

Best owner abstraction:
- source-facing: the textbook quantity `\hat B_{v,t}`;
- core/canonical: the chapter weight owners `a 0` and `A[a](t)`, which determine the initial
  weight and accumulated weights from the primitive sequence `a`;
- bridge/view: the displayed finite-sum expansion theorem below.

Primitive data:
- the initial gap term `V₀`;
- the weight sequence `a`;
- the parameters `v`, `G_v`, `D`, `σ_Ψ`, and the index `t`.

Derived API:
- `stronglyConvexCompositeErrorBound V₀ a v G_v D σ_Ψ t`;
- its defining closed-form expansion.

The previous version kept `a₀` and `A` as extra primitive inputs. In this chapter those are not
independent data: the canonical initial weight is `a 0`, and the canonical accumulated weights are
already owned by `A[a](t)`. This refinement deletes the redundant parameters and aligns the public
surface with the chapter weight API already used downstream.
-/

/-- Definition 6.66: the quantity `\hat{B}_{v,t}` is the initial term `a₀ V₀` plus the weighted
strong-convexity contribution
`(∑_{k=1}^t a_k^(1 + 2 v) / A_k^(2 v)) G_v^2 D^(2 v) / (2 σ_Ψ)`. -/
def stronglyConvexCompositeErrorBound
    (V0 : ℝ) (a : ℕ → ℝ) (v Gv D sigmaPsi : ℝ) (t : ℕ) : ℝ :=
  a 0 * V0 +
    Finset.sum (Finset.Icc 1 t)
        (fun k ↦ Real.rpow (a k) (1 + 2 * v) / Real.rpow (A[a](k)) (2 * v)) *
      (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * sigmaPsi))

-- Proof sketch: unfold `stronglyConvexCompositeErrorBound`.
/-- Expanding `stronglyConvexCompositeErrorBound V₀ a v G_v D σ_Ψ t` gives the defining
formula for the quantity `\hat{B}_{v,t}`. -/
theorem stronglyConvexCompositeErrorBound_def
    (V0 : ℝ) (a : ℕ → ℝ) (v Gv D sigmaPsi : ℝ) (t : ℕ) :
    stronglyConvexCompositeErrorBound V0 a v Gv D sigmaPsi t =
      a 0 * V0 +
        Finset.sum (Finset.Icc 1 t)
            (fun k ↦ Real.rpow (a k) (1 + 2 * v) / Real.rpow (A[a](k)) (2 * v)) *
          (Gv ^ (2 : ℕ) * Real.rpow D (2 * v) / (2 * sigmaPsi)) := rfl

end
