/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin CubicRegularizationModelNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 4.1.5 is the source-facing cubic-regularization method owner in the chapter.

Sampled owner-style declarations:
* `RelaxedRegularizedNewtonIteration` in `Definition_4_1_5`, the chapter's weaker owner for the
  iterate sequence, regularization schedule, and update law;
* `RegularizedNewton.acceptedParameters` in `Definition_4_1_16`, the canonical acceptance-set
  owner at a fixed base point;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the owner of a cubic step `T_M` together
  with its global cubic-model minimization property;
* `cubicRegularizationProblem`, `Φ[f; M](x)`, and `f̄[f; M](x)` in `Definition_4_1_3`, the cubic
  subproblem owner and its canonical model-value layers.

Best owner abstraction:
* source-facing: `CubicRegularizationMethod`;
* core/canonical: `CubicRegularizationMapping f M` for the chosen cubic step at each iteration,
  `f̄[f; M](x)` for the model value, and `RelaxedRegularizedNewtonIteration` for the weaker
  trajectory dynamics;
* bridge/view: the compatibility relation between the chosen step owner `step k` and the ambient
  family `stepMap (M_k)`.

Primitive data:
* the iterate sequence `x`,
* the regularization sequence `M_k`,
* the chosen cubic-step owner `step k : CubicRegularizationMapping f M_k`,
* the standing parameter datum `L₀ ∈ (0, L]`,
* the initial condition `x₀ = x0`,
* the parameter bounds `M_k ∈ [L₀, 2L]`,
* the acceptance inequality `f (T_{M_k}(x_k)) ≤ f̄[f; M_k](x_k)`,
* the update rule `x_{k+1} = T_{M_k}(x_k)` together with the bridge to the ambient family
  `stepMap`.

Derived API:
* the weaker relaxed-iteration view forgetting only the stronger lower bound `L₀ ≤ M_k`,
* the minimizing-step statement at the current iterate, obtained from the owner `step k`,
* accepted-parameter membership
  `M_k ∈ acceptedParameters f stepMap (fun M x ↦ f̄[f; M](x)) L₀ L x_k`,
* the accepted trial point at iteration `k` and its identification with the next iterate.

This file therefore keeps the source-facing cubic owner, but now organizes it around the canonical
cubic-step and model-value owners instead of an arbitrary free `modelValue` layer. The only extra
bridge data kept is the identification of the chosen owner `step k` with the ambient family
`stepMap (M_k)`, needed to connect the source-facing method to the chapter's generic
regularization/backtracking infrastructure. -/

/-- Algorithm 4.1.5: a cubic-regularization method for an objective `f`, a family of cubic trial
maps `T_M`, constants `L₀ ∈ (0, L]` and `L`, and an initial point `x₀` consists of an iterate
sequence `x_k`, a regularization-parameter sequence `M_k`, and a chosen cubic-step owner
`step k : CubicRegularizationMapping f M_k` such that `step k` agrees with `T_{M_k}`, `x₀ = x0`,
each `M_k` lies in `[L₀, 2L]`, the acceptance inequality
`f (T_{M_k}(x_k)) ≤ f̄[f; M_k](x_k)` holds, and the next iterate is
`x_{k+1} = T_{M_k}(x_k)`. -/
structure CubicRegularizationMethod
    (f : E → ℝ)
    (stepMap : ℝ → E → E)
    (L0 L : ℝ) (x0 : E) where
  /-- The iterate sequence `x₀, x₁, x₂, ...`. -/
  x : ℕ → E
  /-- The chosen regularization parameters `M₀, M₁, M₂, ...`. -/
  regularization : ℕ → ℝ
  /-- For each iteration `k`, `step k` is the chosen cubic-step owner with parameter `M_k`. -/
  step (k : ℕ) : CubicRegularizationMapping f (regularization k)
  /-- The chosen owner `step k` agrees with the ambient family `T_{M_k}` used elsewhere in the
  chapter. -/
  step_eq_stepMap (k : ℕ) (x : E) : step k x = stepMap (regularization k) x
  /-- The standing regularization lower bound satisfies `L₀ ∈ (0, L]`. -/
  L0_mem_Ioc : L0 ∈ Set.Ioc (0 : ℝ) L
  /-- The zeroth iterate is the prescribed initial point `x₀`. -/
  x_zero : x 0 = x0
  /-- Every chosen parameter `M_k` belongs to the admissible interval `[L₀, 2L]`. -/
  regularization_mem_Icc (k : ℕ) : regularization k ∈ Set.Icc L0 (2 * L)
  /-- The accepted trial point satisfies the model comparison
  `f (T_{M_k}(x_k)) ≤ f̄[f; M_k](x_k)` at every iteration. -/
  objective_step_le_value (k : ℕ) :
    f ((step k) (x k)) ≤
      EReal.toReal
        (SetConstrainedMinimizationProblem.optimalValue
          (cubicRegularizationProblem f (regularization k) (x k)))
  /-- The next iterate is obtained by applying `T_{M_k}` to the current iterate `x_k`. -/
  x_succ (k : ℕ) : x (k + 1) = (step k) (x k)

namespace CubicRegularizationMethod

variable {f : E → ℝ} {stepMap : ℝ → E → E}
variable {L0 L : ℝ} {x0 : E}

/-- A cubic-regularization method can be used as its underlying iterate sequence `x_k`. -/
instance :
    CoeFun (CubicRegularizationMethod f stepMap L0 L x0) (fun _ ↦ ℕ → E) where
  coe method := method.x

/-- The standing parameter `L₀` is positive. -/
theorem L0_pos
    (method : CubicRegularizationMethod f stepMap L0 L x0) :
    0 < L0 :=
  method.L0_mem_Ioc.1

/-- The standing parameter `L₀` is bounded above by `L`. -/
theorem L0_le_L
    (method : CubicRegularizationMethod f stepMap L0 L x0) :
    L0 ≤ L :=
  method.L0_mem_Ioc.2

/-- The chosen cubic-step owner at iteration `k` agrees pointwise with the ambient family
`T_{M_k}`. -/
theorem step_apply_eq_stepMap
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) (x : E) :
    (method.step k) x = stepMap (method.regularization k) x := by
  simpa using method.step_eq_stepMap k x

/-- At the current iterate, the selected cubic step is a global minimizer of the corresponding
cubic model. -/
theorem step_isMinOn
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    IsMinOn
      (cubicRegularizationQuadraticApproximation
        f (method.regularization k) (method k))
      Set.univ
      ((method.step k) (method k)) :=
  (method.step k).isMinOn_apply (method k)

/-- Rewriting the selected owner through the ambient family `stepMap` recovers the same minimizing
step statement at iteration `k`. -/
theorem stepMap_isMinOn
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    IsMinOn
      (cubicRegularizationQuadraticApproximation
        f (method.regularization k) (method k))
      Set.univ
      (stepMap (method.regularization k) (method k)) := by
  simpa [method.step_apply_eq_stepMap k (method k)] using method.step_isMinOn k

/-- Forgetting the stronger lower bound `L₀ ≤ M_k` turns a cubic-regularization method into the
weaker chapter owner `RelaxedRegularizedNewtonIteration`. -/
def toRelaxedRegularizedNewtonIteration
    (method : CubicRegularizationMethod f stepMap L0 L x0) :
    RelaxedRegularizedNewtonIteration stepMap L where
  x := method.x
  regularization := method.regularization
  regularization_mem_Ioc k := by
    refine ⟨?_, (method.regularization_mem_Icc k).2⟩
    exact lt_of_lt_of_le method.L0_mem_Ioc.1 (method.regularization_mem_Icc k).1
  x_succ k := by
    simpa [method.step_apply_eq_stepMap k (method k)] using method.x_succ k

/-- Every chosen regularization parameter also satisfies the weaker chapter interval condition
`M_k ∈ (0, 2L]`. -/
theorem regularization_mem_Ioc
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    method.regularization k ∈ Set.Ioc (0 : ℝ) (2 * L) :=
  method.toRelaxedRegularizedNewtonIteration.regularization_mem_Ioc k

/-- Every chosen regularization parameter is bounded below by `L₀`. -/
theorem L0_le_regularization
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    L0 ≤ method.regularization k :=
  (method.regularization_mem_Icc k).1

/-- Every chosen regularization parameter in a cubic-regularization method is positive. -/
theorem regularization_pos
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    0 < method.regularization k :=
  method.toRelaxedRegularizedNewtonIteration.regularization_pos k

/-- Every chosen regularization parameter is bounded above by `2L`. -/
theorem regularization_le_two_mul_L
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    method.regularization k ≤ 2 * L :=
  method.toRelaxedRegularizedNewtonIteration.regularization_le_two_mul_L k

/-- At iteration `k`, the chosen regularization parameter belongs to the canonical accepted-step
set at the current iterate `x_k`. -/
theorem regularization_mem_acceptedParameters
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    method.regularization k ∈
      RegularizedNewton.acceptedParameters
        f stepMap
        (fun M x ↦
          EReal.toReal
            (SetConstrainedMinimizationProblem.optimalValue
              (cubicRegularizationProblem f M x)))
        L0 L (method k) :=
  RegularizedNewton.mem_acceptedParameters_of_mem_Icc_of_le_modelValue
    (method k)
    (method.regularization k)
    (method.regularization_mem_Icc k)
    (by
      simpa [method.step_apply_eq_stepMap k (method k)] using method.objective_step_le_value k)

/-- The accepted trial point used at iteration `k`. -/
def acceptedTrialPoint
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    E :=
  (method.step k) (method k)

/-- The accepted trial point at iteration `k` is exactly the next iterate `x_{k+1}`. -/
theorem acceptedTrialPoint_eq_succ
    (method : CubicRegularizationMethod f stepMap L0 L x0) (k : ℕ) :
    method.acceptedTrialPoint k = method (k + 1) := by
  simpa [acceptedTrialPoint] using (method.x_succ k).symm

end CubicRegularizationMethod
