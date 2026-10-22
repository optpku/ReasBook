/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: projected first-order subgradient methods for convex minimization over a simple
closed convex feasible set with one aggregate functional constraint.

Relevant owner-style declarations sampled before refinement:
- `FirstOrderConvexMinimizationProblem` in `Definition_3_40` for the ambient feasible set `Q`,
  the objective, the canonical projection onto `Q`, and the objective first-order oracle;
- `ProjectedMultipleConstraintFirstOrderProblem` in `Algorithm_3_4` for the projected
  one-constraint owner used by Algorithm 3.3;
- `FirstOrderOracle.correctionStepsize` in `Definition_3_40` for the canonical correction scalar
  attached to an oracle reply;
- `SimpleSetSubgradientMethod.iterates` in `Algorithm_3_2` and
  `ApproximateLagrangeMultiplierSwitchingMethod.nextIterate` in `Algorithm_3_4` for the chapter
  pattern of recursively applying owner-defined projected steps.

Owner abstraction:
- the ambient projected one-constraint problem is best owned by
  `ProjectedMultipleConstraintFirstOrderProblem E 1`.

Source/core/bridge triage:
- `source-facing`: `FunctionalConstraintSubgradientMethod`, `takesObjectiveStep`, `nextIterate`,
  and `iterates`;
- `core/canonical`: `ProjectedMultipleConstraintFirstOrderProblem E 1`;
- `bridge/view`: the objective-branch and constraint-branch formulas for `nextIterate`.

Primitive data:
- the aggregate constraint function `f̄`, represented canonically as the unique member
  `problem.constraints 0` of the `Fin 1` constraint family together with its oracle
  `problem.constraintOracle 0`;
- a feasible starting point `x₀`;
- the fixed accuracy parameter `ε`.

Derived API:
- the objective-branch predicate `f̄(x) ≤ ε`;
- the owner-derived correction scalar `(problem.constraintOracle 0).correctionStepsize x`;
- the projected successor iterate;
- the recursive iterate sequence and its feasibility.

Accordingly, this file works directly over the projected specialization
`ProjectedMultipleConstraintFirstOrderProblem E 1`, and derives the Algorithm 3.3 branch formulas
from the same owner correction scalar and projected-step API already used elsewhere in the
chapter. -/

/-- Algorithm 3.3: a subgradient method with functional constraints is determined by a
one-constraint first-order problem, a feasible starting point `x₀ ∈ Q`, and a fixed accuracy
parameter `ε`. At iterate `x_k`, if the unique constraint value
`problem.constraints 0 x_k = f̄(x_k)` satisfies `problem.constraints 0 x_k ≤ ε`, the method takes
the objective step
`x_{k+1} = π_Q (x_k - (ε / ‖g(x_k)‖²) • g(x_k))`;
otherwise it takes the aggregate-constraint correction
`x_{k+1} = π_Q (x_k - (f̄(x_k) / ‖ḡ(x_k)‖²) • ḡ(x_k))`. -/
structure FunctionalConstraintSubgradientMethod
    (problem : ProjectedMultipleConstraintFirstOrderProblem E 1) where
  /-- The prescribed initial point `x₀`. -/
  x0 : E
  /-- The initial point lies in the simple feasible set `Q`. -/
  x0_mem : x0 ∈ problem.feasibleSet
  /-- The target accuracy parameter `ε`. -/
  ε : ℝ

namespace FunctionalConstraintSubgradientMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E 1}

/-- The textbook objective-branch test at `x`: take the objective step exactly when
`f̄(x) ≤ ε`. -/
def takesObjectiveStep
    (method : FunctionalConstraintSubgradientMethod problem) (x : E) : Prop :=
  problem.constraints 0 x ≤ method.ε

section Projection

variable [CompleteSpace E]

/-- The one-step update of Algorithm 3.3 uses the fixed-`ε` objective step on the admissible
branch and otherwise the aggregate-constraint correction built from the owner scalar
`(problem.constraintOracle 0).correctionStepsize x`. -/
def nextIterate (method : FunctionalConstraintSubgradientMethod problem) (x : E) : E :=
  if takesObjectiveStep method x then
    problem.normalizedSubgradientStep (method.ε / ‖problem.oracle.subgradient x‖) x
  else
    let g := (problem.constraintOracle 0).subgradient x
    problem.projection (x - (problem.constraintOracle 0).correctionStepsize x • g)

/-- The iterate sequence starts from `x₀` and repeatedly applies the Algorithm 3.3 update. -/
def iterates (method : FunctionalConstraintSubgradientMethod problem) : ℕ → E
  | 0 => method.x0
  | k + 1 => method.nextIterate (iterates method k)

/-- A functional-constraint subgradient method can be used as its underlying iterate sequence. -/
instance : CoeFun (FunctionalConstraintSubgradientMethod problem) (fun _ ↦ ℕ → E) where
  coe method := iterates method

/-- The textbook admissible index family `𝒜(N)`: among `x₀, ..., x_N`, keep exactly the indices
where Algorithm 3.3 takes the objective branch. -/
def admissibleIndices
    (method : FunctionalConstraintSubgradientMethod problem) (N : ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun k ↦ method.takesObjectiveStep (method k)

/-- Membership in `𝒜(N)` means exactly that the corresponding iterate satisfies the textbook
constraint test `f̄(x_k) ≤ ε`. -/
@[simp] theorem mem_admissibleIndices_iff
    (method : FunctionalConstraintSubgradientMethod problem) (N : ℕ) {k : Fin (N + 1)} :
    k ∈ method.admissibleIndices N ↔ problem.constraints 0 (method k) ≤ method.ε := by
  simp [admissibleIndices, takesObjectiveStep]

/-- Every one-step update belongs to the simple feasible set `Q`. -/
theorem nextIterate_mem (method : FunctionalConstraintSubgradientMethod problem) (x : E) :
    method.nextIterate x ∈ problem.feasibleSet := by
  by_cases hx : takesObjectiveStep method x <;> simp [nextIterate, hx]

/-- If `f̄(x) ≤ ε`, the next iterate is the owner normalized objective step with length
`ε / ‖g(x)‖`. -/
theorem nextIterate_eq_objective
    (method : FunctionalConstraintSubgradientMethod problem) {x : E}
    (hx : problem.constraints 0 x ≤ method.ε) :
    method.nextIterate x =
      problem.normalizedSubgradientStep (method.ε / ‖problem.oracle.subgradient x‖) x := by
  simp [nextIterate, takesObjectiveStep, hx]

/-- If `ε < f̄(x)`, the next iterate is the projected aggregate-constraint correction built from
the owner scalar `(problem.constraintOracle 0).correctionStepsize x`. -/
theorem nextIterate_eq_constraint
    (method : FunctionalConstraintSubgradientMethod problem) {x : E}
    (hx : method.ε < problem.constraints 0 x) :
    method.nextIterate x =
      problem.projection
        (x - (problem.constraintOracle 0).correctionStepsize x •
          (problem.constraintOracle 0).subgradient x) := by
  simp [nextIterate, takesObjectiveStep, not_le.mpr hx]

/-- Bridge/view: on the constraint branch, the owner scalar
`(problem.constraintOracle 0).correctionStepsize x` unfolds to the textbook ratio
`f̄(x) / ‖ḡ(x)‖²`. -/
theorem nextIterate_eq_constraint_ratio
    (method : FunctionalConstraintSubgradientMethod problem) {x : E}
    (hx : method.ε < problem.constraints 0 x) :
    method.nextIterate x =
      problem.projection
        (x - (problem.constraints 0 x / ‖(problem.constraintOracle 0).subgradient x‖ ^ (2 : ℕ)) •
          (problem.constraintOracle 0).subgradient x) := by
  rw [method.nextIterate_eq_constraint hx]
  simp [FirstOrderOracle.correctionStepsize]

/-- The zeroth iterate is the prescribed starting point `x₀`. -/
theorem iterates_zero (method : FunctionalConstraintSubgradientMethod problem) :
    method 0 = method.x0 := rfl

/-- Each successor iterate is obtained by applying the Algorithm 3.3 update to the previous one. -/
theorem iterates_succ (method : FunctionalConstraintSubgradientMethod problem) (k : ℕ) :
    method (k + 1) = method.nextIterate (method k) := rfl

/-- Every iterate belongs to the simple feasible set `Q`. -/
theorem iterates_mem (method : FunctionalConstraintSubgradientMethod problem) (k : ℕ) :
    method k ∈ problem.feasibleSet := by
  induction k with
  | zero =>
      simpa [method.iterates_zero] using method.x0_mem
  | succ k _ =>
      rw [method.iterates_succ]
      exact method.nextIterate_mem (method k)

end Projection

end FunctionalConstraintSubgradientMethod

end
