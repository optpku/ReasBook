/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n N : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Algorithm 7.1 lies in the projected normalized subgradient / finite-horizon Euclidean domain.

Sampled owner-style declarations:
- `FirstOrderConvexMinimizationProblem` in `Chap03/Definition_3_40`, the chapter owner for the
  feasible set, objective, canonical projection, and first-order oracle;
- `FirstOrderConvexMinimizationProblem.normalizedSubgradientStep` in `Chap03/Algorithm_3_2`, the
  owner one-step projected normalized subgradient update;
- `SimpleSetSubgradientMethod` in `Chap03/Algorithm_3_2`, the recursive owner iterate sequence;
- `bestFunctionValueUpTo` in `Chap03/Theorem_3_2_10`, the chapter owner for sampled prefix
  minima.

Best owner abstraction:
- source-facing: Algorithm 7.1 as a finite-horizon constant-stepsize run with a chosen output
  index;
- core/canonical: `FirstOrderConvexMinimizationProblem n` together with
  `SimpleSetSubgradientMethod problem`;
- bridge/view: the certificate that the first `N + 1` stepsizes are constant and the chosen index
  attaining the sampled minimum.

Primitive data:
- the owner first-order convex minimization problem;
- the owner simple-set subgradient run;
- the radius parameter `R`;
- the finite-horizon constant-stepsize certificate;
- the chosen minimizing output index.

Derived API:
- the feasible set, objective, projection, and iterates through the owner graph;
- the source-facing constant-step recursion on `0, ..., N`;
- the sampled output point and its best-value characterization.

This refinement removes the duplicate local feasible-set/objective/projection/subgradient package
and keeps Algorithm 7.1 only as the source-facing finite-horizon specialization of the Chapter 3
owner graph. The textbook positivity condition `R > 0` is moved to theorem-level hypotheses
instead of remaining primitive run data. -/

/-- Algorithm 7.1: a projected normalized subgradient run over an owner first-order convex
minimization problem, together with a radius parameter `R`, a certificate that the owner
simple-set method uses the constant stepsize `R / √(N + 1)` on the finite horizon
`0, ..., N`, and a chosen output index attaining the minimum sampled objective value among
`x₀, ..., x_N`. The feasible set, objective, canonical projection, and oracle-selected
subgradients are inherited from the owner problem/method rather than stored again as primitive
data. Positivity of `R` is kept as theorem-level data, not as a field of the run. -/
structure ProjectedNormalizedSubgradientMethod (n N : ℕ) where
  /-- The owner first-order convex minimization problem. -/
  problem : FirstOrderConvexMinimizationProblem (EuclideanSpace ℝ (Fin n))
  /-- The owner simple-set subgradient run. -/
  run : SimpleSetSubgradientMethod problem
  /-- The radius parameter `R`. -/
  radius : ℝ
  /-- On the finite horizon `0, ..., N`, the owner stepsizes are constantly
  `R / √(N + 1)`. -/
  constant_stepsize :
    ∀ i : Fin (N + 1), run.stepsize i = radius / Real.sqrt (N + 1 : ℝ)
  /-- A chosen sampled minimizer index among `x₀, ..., x_N`. -/
  bestIndex : Fin (N + 1)
  /-- The chosen index attains the minimum sampled objective value. -/
  bestIndex_is_argmin :
    ∀ i : Fin (N + 1), problem.objective (run bestIndex) ≤ problem.objective (run i)

namespace ProjectedNormalizedSubgradientMethod

/-- A projected normalized subgradient method can be used as its iterate sequence
`x₀, x₁, x₂, ...`. -/
instance : CoeFun (ProjectedNormalizedSubgradientMethod n N) (fun _ ↦ ℕ → E) where
  coe method := method.run

/-- The constant stepsize `R / √(N + 1)` used in Algorithm 7.1. -/
def stepSize (method : ProjectedNormalizedSubgradientMethod n N) : ℝ :=
  method.radius / Real.sqrt (N + 1 : ℝ)

/-- On the horizon `0, ..., N`, the run uses the constant stepsize of Algorithm 7.1. -/
theorem stepsize_eq
    (method : ProjectedNormalizedSubgradientMethod n N) (i : Fin (N + 1)) :
    method.run.stepsize i = method.stepSize := by
  simpa [stepSize] using method.constant_stepsize i

/-- The zeroth iterate is the prescribed starting point `x₀` of the owner simple-set method. -/
theorem iterates_zero
    (method : ProjectedNormalizedSubgradientMethod n N) :
    method 0 = method.run.x0 := by
  simpa using SimpleSetSubgradientMethod.iterates_zero method.run

/-- On the finite horizon `0, ..., N`, each successor iterate is the owner projected normalized
subgradient step with the constant Algorithm 7.1 stepsize. -/
theorem iterates_succ
    (method : ProjectedNormalizedSubgradientMethod n N) {k : ℕ} (hk : k ≤ N) :
    method (k + 1) = method.problem.normalizedSubgradientStep method.stepSize (method k) := by
  simpa [stepSize, method.constant_stepsize ⟨k, Nat.lt_succ_of_le hk⟩] using
    (SimpleSetSubgradientMethod.iterates_succ method.run k)

/-- The output point `x̄`, obtained by evaluating the iterates at the chosen minimizing index. -/
def outputPoint (method : ProjectedNormalizedSubgradientMethod n N) : E :=
  method method.bestIndex

/-- The output point achieves the minimum objective value among the sampled iterates
`x₀, ..., x_N`. -/
theorem outputPoint_is_argmin
    (method : ProjectedNormalizedSubgradientMethod n N) (i : Fin (N + 1)) :
    method.problem.objective method.outputPoint ≤ method.problem.objective (method i) := by
  simpa [outputPoint] using method.bestIndex_is_argmin i

/-- The output value equals the sampled best objective value among the first `N + 1` iterates. -/
theorem objective_outputPoint_eq_bestFunctionValueUpTo
    (method : ProjectedNormalizedSubgradientMethod n N) :
    method.problem.objective method.outputPoint =
      bestFunctionValueUpTo (fun i ↦ method.problem.objective (method i)) N := by
  refine le_antisymm ?_ ?_
  · rw [bestFunctionValueUpTo]
    refine le_ciInf ?_
    intro i
    simpa [outputPoint] using method.bestIndex_is_argmin i
  · simpa [outputPoint] using
      (show
        bestFunctionValueUpTo (fun i ↦ method.problem.objective (method i)) N ≤
          (fun i ↦ method.problem.objective (method i)) method.bestIndex from
        bestFunctionValueUpTo_le method.bestIndex)

/-- Every iterate produced by Algorithm 7.1 remains in the feasible set `Q₁`. -/
theorem iterate_mem_feasibleSet
    (method : ProjectedNormalizedSubgradientMethod n N) (k : ℕ) :
    method k ∈ method.problem.feasibleSet := by
  simpa using SimpleSetSubgradientMethod.iterates_mem method.run k

/-- The output point `x̄` belongs to the feasible set `Q₁`. -/
theorem outputPoint_mem_feasibleSet
    (method : ProjectedNormalizedSubgradientMethod n N) :
    method.outputPoint ∈ method.problem.feasibleSet := by
  simpa [outputPoint] using SimpleSetSubgradientMethod.iterates_mem method.run method.bestIndex

end ProjectedNormalizedSubgradientMethod

end
