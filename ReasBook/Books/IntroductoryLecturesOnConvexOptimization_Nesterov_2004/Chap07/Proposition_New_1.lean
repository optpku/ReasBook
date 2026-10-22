/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_40

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n N : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open ProjectedNormalizedSubgradientMethod SimpleSetSubgradientMethod

/- Proposition New 1 lies in the chapter's projected normalized subgradient / sampled best-value
domain.

Sampled owner-style declarations:
- `ProjectedNormalizedSubgradientMethod.outputPoint` and
  `objective_outputPoint_eq_bestFunctionValueUpTo` in `Algorithm_7_1`, the source-facing output
  index bridge for Algorithm 7.1;
- `SimpleSetSubgradientMethod.
    bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method`
  in `Chap03/Theorem_3_40`, the core method-level sampled-gap estimate;
- `deltaN` and `deltaN_apply` in `Chap03/Definition_3_41`, the owner scalar for the finite
  stepsize prefix.

Best owner abstraction:
- source-facing: the output-point bound for Algorithm 7.1;
- core/canonical: the Chapter 3 sampled-value theorem for `method.run`;
- bridge/view: the output-point minimum identity and the constant-prefix evaluation induced by
  `method.constant_stepsize`.

Primitive data:
- the owner first-order minimization problem and simple-set subgradient run already stored in
  `method`;
- the minimizer `xStar`, the Lipschitz constant `γ₁`, and the source-facing radius parameter
  `method.radius`.

Derived API:
- the initial closed-ball membership of `method.run.x0`;
- the sampled best-value bound for `method.run`;
- the identification of the finite stepsize prefix with the constant value
  `method.radius / √(N + 1)`.

This refinement keeps Proposition New 1 source-facing, but deletes the duplicate wheel proof
route: the theorem is now a thin bridge from the Chapter 3 owner estimate to the Chapter 7
output-point surface. -/

/-- Proposition New 1: for Algorithm 7.1 on a closed convex feasible set, if `xStar` attains the
optimal value `f^* = f(xStar)` on the feasible set and `f` is `γ₁`-Lipschitz on the closed ball
centered at `xStar` with radius `‖x₀ - xStar‖`, then the output `G_N(R)` satisfies
`f(G_N(R)) - f^* ≤ (γ₁ / √(N + 1)) * ((‖x₀ - xStar‖² + R²) / (2R))`. -/
-- Proof sketch: apply the projected normalized subgradient bound to the iterate sequence of
-- `method`, using the constant stepsize `R / √(N + 1)` built into Algorithm 7.1 and the fact that
-- `method.outputPoint` realizes the minimum sampled objective value. Then evaluate the stepsize
-- sums `∑ h_i = R * √(N + 1)` and `∑ h_i² = R²`, and substitute these identities into the
-- resulting estimate.
theorem projectedNormalizedSubgradientMethod_output_sub_minimizer_le_lipschitz_distance_radius_ratio
    (method : ProjectedNormalizedSubgradientMethod n N)
    (h_radius : 0 < method.radius)
    {xStar : E} {γ₁ : NNReal}
    (hxStar_min : IsMinOn method.problem method.problem.feasibleSet xStar)
    (h_lipschitz :
      LipschitzOnWith γ₁ method.problem
        (Metric.closedBall xStar ‖method.run.x0 - xStar‖)) :
    method.problem method.outputPoint - method.problem xStar ≤
      ((γ₁ : ℝ) / Real.sqrt (N + 1 : ℝ)) *
        ((‖method.run.x0 - xStar‖ ^ (2 : ℕ) + method.radius ^ (2 : ℕ)) /
          (2 * method.radius)) := by
  set R0 : NNReal := ⟨‖method.run.x0 - xStar‖, norm_nonneg _⟩
  have hx0_ball : method.run.x0 ∈ Metric.closedBall xStar R0 := by
    simpa [R0, Metric.mem_closedBall, dist_eq_norm] using le_rfl
  have hbound :=
    bestFunctionValueUpTo_sub_le_of_projected_normalized_subgradient_method
      method.run xStar R0 γ₁ hxStar_min h_lipschitz hx0_ball N
  have hbound' :
      bestFunctionValueUpTo (fun i ↦ method.problem (method i)) N - method.problem xStar ≤
        (γ₁ : ℝ) * deltaN N R0 (method.run.stepsizePrefix N) := by
    simpa using hbound
  have hprefix :
      method.run.stepsizePrefix N = deltaNConstantChoice N method.radius := by
    ext i
    simpa [stepSize] using method.stepsize_eq i
  have hdelta :
      deltaN N R0 (method.run.stepsizePrefix N) =
        (1 / Real.sqrt (N + 1 : ℝ)) *
          ((‖method.run.x0 - xStar‖ ^ (2 : ℕ) + method.radius ^ (2 : ℕ)) /
            (2 * method.radius)) := by
    change
      deltaN N (⟨‖method.run.x0 - xStar‖, norm_nonneg _⟩ : NNReal) (method.run.stepsizePrefix N) =
        (1 / Real.sqrt (N + 1 : ℝ)) *
          ((‖method.run.x0 - xStar‖ ^ (2 : ℕ) + method.radius ^ (2 : ℕ)) /
            (2 * method.radius))
    rw [hprefix, deltaN_apply]
    have hsqrt : Real.sqrt (N + 1 : ℝ) ≠ 0 := by
      positivity
    simp
    field_simp [hsqrt, h_radius.ne']
    ring_nf
    rw [Real.sq_sqrt]
    · ring_nf
    · positivity
  have hsqrt : Real.sqrt (N + 1 : ℝ) ≠ 0 := by
    positivity
  calc
    method.problem method.outputPoint - method.problem xStar
        = bestFunctionValueUpTo (fun i ↦ method.problem (method i)) N - method.problem xStar := by
            rw [method.objective_outputPoint_eq_bestFunctionValueUpTo]
    _ ≤ (γ₁ : ℝ) * deltaN N R0 (method.run.stepsizePrefix N) := hbound'
    _ = (γ₁ : ℝ) *
          ((1 / Real.sqrt (N + 1 : ℝ)) *
            ((‖method.run.x0 - xStar‖ ^ (2 : ℕ) + method.radius ^ (2 : ℕ)) /
              (2 * method.radius))) := by rw [hdelta]
    _ = ((γ₁ : ℝ) / Real.sqrt (N + 1 : ℝ)) *
          ((‖method.run.x0 - xStar‖ ^ (2 : ℕ) + method.radius ^ (2 : ℕ)) /
            (2 * method.radius)) := by field_simp [hsqrt]

end
