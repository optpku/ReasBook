/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_40

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DeltaN

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 3.41 lies in the chapter's projected normalized subgradient / constant-stepsize domain.

Sampled owner-style declarations:
- `SimpleSetSubgradientMethod.
    bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method`
  in `Theorem_3_40`, the method-level owner gap estimate;
- `deltaNConstantChoice` in `Proposition_3_35`, the canonical constant stepsize prefix;
- `deltaN_constantChoice` in `Proposition_3_35`, the owner evaluation theorem at that prefix.

Best owner abstraction:
- `source-facing`: the constant-stepsize specialization of the best sampled-value bound for a run
  `method : SimpleSetSubgradientMethod problem`;
- `core/canonical`: the method-level bound from `Theorem_3_40`;
- `bridge/view`: the identification of the method's finite stepsize prefix with
  `deltaNConstantChoice N R`.

Primitive data:
- the owner first-order convex minimization problem `problem`;
- the owner simple-set subgradient run `method`;
- the minimizer `xStar`, radius `R`, Lipschitz constant `M`, and horizon `N`;
- the source-facing constant-stepsize hypothesis on the prefix `0, ..., N`.

Derived API:
- the sampled best value `bestFunctionValueUpTo (fun i ↦ problem (method i)) N`;
- the canonical constant prefix `deltaNConstantChoice N R`;
- the closed form `Δ[N; R] (deltaNConstantChoice N R) = R / √(N + 1)`.

The previous version erased the subgradient-method owner and kept only a generic scalar inequality.
This refinement restores the source-facing semantics by specializing the actual method theorem
`Theorem_3_40` to the constant stepsize prefix.
-/

namespace SimpleSetSubgradientMethod

variable {problem : FirstOrderConvexMinimizationProblem E}

/-- Theorem 3.41: if the first `N + 1` stepsizes of a simple-set subgradient method are chosen
constantly as `h_i = R / √(N + 1)`, then the best sampled objective gap among the first `N + 1`
iterates is bounded by `M R / √(N + 1)`. -/
-- Proof sketch: apply the method-level owner estimate from `Theorem_3_40`, identify the finite
-- stepsize prefix with `deltaNConstantChoice N R`, and simplify with `deltaN_constantChoice`.
theorem bestFunctionValueUpTo_sub_le_of_constant_stepsizes
    (method : SimpleSetSubgradientMethod problem) (xStar : E) (R M : NNReal)
    (hxStar_min : IsMinOn problem problem.feasibleSet xStar)
    (hf_lipschitz : LipschitzOnWith M problem (Metric.closedBall xStar R))
    (hx0_ball : method.x0 ∈ Metric.closedBall xStar R)
    (N : ℕ)
    (h_stepsize :
      ∀ i : Fin (N + 1), method.stepsize i = (R : ℝ) / Real.sqrt (N + 1 : ℝ)) :
    bestFunctionValueUpTo (fun i ↦ problem (method i)) N - problem xStar ≤
      (M : ℝ) * ((R : ℝ) / Real.sqrt (N + 1 : ℝ)) := by
  have hbound :=
    bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method
      method xStar R M hxStar_min hf_lipschitz hx0_ball N
  have hprefix :
      method.stepsizePrefix N = deltaNConstantChoice N R := by
    ext i
    simpa using h_stepsize i
  calc
    bestFunctionValueUpTo (fun i ↦ problem (method i)) N - problem xStar ≤
        (M : ℝ) * Δ[N; (R : ℝ)] (method.stepsizePrefix N) :=
      hbound
    _ = (M : ℝ) * Δ[N; (R : ℝ)] (deltaNConstantChoice N R) := by rw [hprefix]
    _ = (M : ℝ) * ((R : ℝ) / Real.sqrt (N + 1 : ℝ)) := by
      rw [deltaN_constantChoice]

end SimpleSetSubgradientMethod

end
