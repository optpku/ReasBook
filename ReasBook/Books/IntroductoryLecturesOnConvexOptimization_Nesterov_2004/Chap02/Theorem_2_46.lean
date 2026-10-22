/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: accelerated first-order dynamics for strongly convex smooth unconstrained
minimization on real Hilbert spaces.

Owner declarations sampled for this refinement:
* `IsStrongConvexSmoothObjective` in `Definition_2_17` owns the objective-side `C¹`,
  strong-convexity, and gradient-Lipschitz data;
* `IsMinOn` on `Set.univ` gives the canonical minimizer predicate for the ambient unconstrained
problem;
* `ConstantStepSchemeIII` in `Proposition_2_12` owns the constant-step scheme III trajectory data;
* `constantStepSchemeIII_objective_gap_le_geometric_initial_energy` in `Proposition_2_12` owns
  the scheme-III Lyapunov estimate with the canonical initial energy;
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Theorem_2_30` owns the canonical quadratic-growth
  consequence of strong convexity at a global minimizer.

Primitive data here are therefore only the objective `f`, its owner hypothesis
`hf : IsStrongConvexSmoothObjective μ L f`, one minimizing point `xStar` with
`hxStar : IsMinOn f Set.univ xStar`, the initial point `x₀`, and the owner scheme with parameter
`q_f = q[μ, L]`. Since that owner scheme already stores `q_f ∈ (0, 1]`, the textbook side
assumption `μ ≤ L` is derived rather than kept as a parallel public binder. No problem-level
wrapper or duplicate local optimal-value API is introduced.

Source/core/bridge triage:
* source-facing: the textbook geometric objective-gap estimate for scheme III;
* core/canonical: `ConstantStepSchemeIII`, `IsStrongConvexSmoothObjective`, and `IsMinOn`;
* bridge/view: this file, which combines the owner Lyapunov estimate with the owner
  quadratic-growth theorem to remove the initial quadratic term from the right-hand side. -/

section

variable {μ L : ℝ} {f : E → ℝ}
local notation "qf" => q[μ, L]

/-- Theorem 2.46: every constant-step scheme III trajectory for a smooth `μ`-strongly convex
objective satisfies the geometric objective-gap bound
`f(x_k) - f(x*) ≤ 2 (1 - √q[μ, L])^k (f(x₀) - f(x*))` for all `k ≥ 0`. The admissible range
`q[μ, L] ∈ (0, 1]` is carried by the owner scheme hypothesis
`scheme : ConstantStepSchemeIII f L q[μ, L] x₀`, so no separate public `μ ≤ L` binder is kept.
The textbook recursion
`y_k = x_k + β (x_k - x_{k-1})`, `x_{k+1} = y_k - (1 / L) ∇ f(y_k)` with `x_{-1} = x₀` is
encoded by `ConstantStepSchemeIII` via the shifted auxiliary sequence `y_{k+1}`. -/
-- Proof sketch: apply the owner geometric Lyapunov estimate
-- `constantStepSchemeIII_objective_gap_le_geometric_initial_energy` from `Proposition_2_12`,
-- then bound the initial quadratic term by the canonical quadratic-growth theorem
-- `hf.strongConvexOn.quadratic_growth_of_isMinOn hxStar`.
theorem constantStepSchemeIII_objective_gap_le_geometric_rate
    (hf : IsStrongConvexSmoothObjective μ L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    (scheme : ConstantStepSchemeIII f L qf x0)
    (k : ℕ) :
    f (scheme k) - f xStar ≤
      2 * (1 - Real.sqrt qf) ^ k * (f x0 - f xStar) := by
  -- First remove the initial quadratic Lyapunov term by quadratic growth at the minimizer.
  have hqg :
      (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ f x0 - f xStar := by
    linarith [hf.strongConvexOn.quadratic_growth_of_isMinOn hxStar x0]
  -- The scheme stores `qf ∈ (0, 1]`, so the geometric factor has a nonnegative base.
  have hqf_nonneg : 0 ≤ qf := le_of_lt scheme.qf_mem_Ioc.1
  have hsqrt_le_one : Real.sqrt qf ≤ 1 := by
    nlinarith [scheme.qf_mem_Ioc.2, Real.sq_sqrt hqf_nonneg, Real.sqrt_nonneg qf]
  let weight : ℝ := (1 - Real.sqrt qf) ^ k
  have hweight_nonneg : 0 ≤ weight := by
    exact pow_nonneg (sub_nonneg.mpr hsqrt_le_one) k
  -- Multiply the quadratic-growth bound by the nonnegative weight and absorb the energy term.
  have hinitial_energy :
      weight * (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) ≤
        2 * weight * (f x0 - f xStar) := by
    nlinarith
  -- Chain the owner Lyapunov estimate with the scalar absorption step.
  calc
    f (scheme k) - f xStar ≤
        weight *
          (f x0 - f xStar + (μ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) :=
      constantStepSchemeIII_objective_gap_le_geometric_initial_energy
        (hf := hf) (hxStar := hxStar) (scheme := scheme) k
    _ ≤ 2 * weight * (f x0 - f xStar) := hinitial_energy
    _ = 2 * (1 - Real.sqrt qf) ^ k * (f x0 - f xStar) := by
      rfl

end
