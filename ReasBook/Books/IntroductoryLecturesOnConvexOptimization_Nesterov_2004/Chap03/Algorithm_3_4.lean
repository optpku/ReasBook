/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open NormedSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Primary domain: first-order convex optimization with finitely many inequality constraints, with
Algorithm 3.4 adding a projected switching specialization.

Relevant owner-style declarations sampled before refinement:
- `FirstOrderOracle` and `FirstOrderOracle.correctionStepsize` in `Definition_3_40` for the
  canonical whole-space first-order reply and the scalar `f(x) / ‖g(x)‖²`;
- `FirstOrderConvexMinimizationProblem` in `Definition_3_40` for the projected owner on a simple
  closed convex feasible set `Q`;
- `KelleyMethod` in `Algorithm_3_9` for the chapter pattern that stores arbitrary stepwise
  choices as run data and derives iterates recursively from those choices.

Best owner abstraction:
- source-facing core owner: `MultipleConstraintFirstOrderProblem E m`;
- source-facing projected specialization: `ProjectedMultipleConstraintFirstOrderProblem E m`.

Source/core/bridge triage:
- source-facing: `MultipleConstraintFirstOrderProblem`,
  `ProjectedMultipleConstraintFirstOrderProblem`,
  `ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet`,
  and `ApproximateLagrangeMultiplierSwitchingMethod`;
- core/canonical: `FirstOrderOracle`, `FirstOrderOracle.correctionStepsize`, and
  `FirstOrderConvexMinimizationProblem`;
- bridge/view: `ProjectedMultipleConstraintFirstOrderProblem.toFirstOrderConvexMinimizationProblem`
  and `ProjectedMultipleConstraintFirstOrderProblem.toLagrangianProblem`.

Primitive data:
- on the whole-space owner: the objective, its first-order oracle, the finite constraint family,
  and the corresponding first-order oracles;
- on the projected specialization: the simple feasible set `Q` together with its nonempty,
  closed, and convex witnesses;
- on the run owner: the feasible initial point `x₀`, the scalar `h`, and the stepwise branch
  choices `j_k`.

Derived API:
- whole-space convexity of the objective and each constraint;
- the whole-space correction step, objective step, branch-selected step, and recursive iterate
  family for method `(3.2.24)`;
- the projected bridge to `FirstOrderConvexMinimizationProblem`;
- the active set `𝒥(x)`, the projected switching step, and the recursively generated iterates.

Accordingly, the whole-space multi-constraint first-order owner is now the main chapter owner,
while the Algorithm 3.4 package is the projected specialization built on top of it. -/

/-- A whole-space first-order problem with a convex objective and `m` inequality constraints. This
owner stores only the objective, the finite constraint family, and the corresponding first-order
oracles. Feasible-set and projection data belong to projected specializations built on top of this
core owner. -/
structure MultipleConstraintFirstOrderProblem (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (m : ℕ) where
  /-- The objective function `f`. -/
  objective : E → ℝ
  /-- A first-order oracle for the objective. -/
  oracle : FirstOrderOracle objective
  /-- The inequality constraints `f_j : E → ℝ`, `j = 1, ..., m`. -/
  constraints : Fin m → E → ℝ
  /-- A first-order oracle for each constraint function. -/
  constraintOracle (j : Fin m) : FirstOrderOracle (constraints j)

namespace MultipleConstraintFirstOrderProblem

/-- A whole-space multi-constraint first-order problem can be used as its objective function. -/
instance : CoeFun (MultipleConstraintFirstOrderProblem E m) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

/-- A first-order oracle already certifies whole-space convexity of the objective. -/
theorem objective_convex (problem : MultipleConstraintFirstOrderProblem E m) :
    ConvexOn ℝ Set.univ problem.objective :=
  problem.oracle.convexOn_univ

/-- Each constraint is convex on all of `E`, derived canonically from its first-order oracle. -/
theorem constraints_convex (problem : MultipleConstraintFirstOrderProblem E m) (j : Fin m) :
    ConvexOn ℝ Set.univ (problem.constraints j) :=
  (problem.constraintOracle j).convexOn_univ

/-- The whole-space correction step for a specific violated constraint `j` at `x`, written with
the canonical scalar `f_j(x) / ‖g_j(x)‖²`. Since the scalar vanishes when the chosen subgradient
vanishes, this totalizes to `x` in that case. -/
def constraintStep
    (problem : MultipleConstraintFirstOrderProblem E m) (j : Fin m) (x : E) : E :=
  let g := (problem.constraintOracle j).subgradient x
  x - (problem.constraintOracle j).correctionStepsize x • g

/-- The whole-space objective step of method `(3.2.24)` at `x`, written as the normalized
subgradient update with step length `ε / ‖g(x)‖`. Since `normalize 0 = 0`, this totalizes to `x`
when the chosen objective subgradient vanishes. -/
def objectiveStep
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x : E) : E :=
  let g := problem.oracle.subgradient x
  x - (ε / ‖g‖) • normalize g

/-- One whole-space update of method `(3.2.24)` from the current iterate `x`: choose `none` for
the objective step and `some j` for the correction step associated to the violated constraint
`j`. -/
def step
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x : E)
    (selectedConstraint : Option (Fin m)) : E :=
  match selectedConstraint with
  | none => problem.objectiveStep ε x
  | some j => problem.constraintStep j x

/-- The recursively generated whole-space iterate family of method `(3.2.24)`, determined by the
initial point `x₀`, the tolerance `ε`, and the stepwise branch choices. -/
def iterates
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) : ℕ → E
  | 0 => x0
  | k + 1 =>
      let xk := problem.iterates ε x0 selectedConstraintAt k
      problem.step ε xk (selectedConstraintAt k)

end MultipleConstraintFirstOrderProblem

/-- A projected multi-constraint first-order problem over a simple closed convex feasible set
`Q`. This is the owner needed by Algorithm 3.4. -/
structure ProjectedMultipleConstraintFirstOrderProblem (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (m : ℕ)
    extends MultipleConstraintFirstOrderProblem E m where
  /-- The feasible set `Q`. -/
  feasibleSet : Set E
  /-- The feasible set `Q` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet

namespace ProjectedMultipleConstraintFirstOrderProblem

/-- A projected multi-constraint first-order problem can be used as its objective function. -/
instance : CoeFun (ProjectedMultipleConstraintFirstOrderProblem E m) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

/-- The projected specialization inherits whole-space convexity of the objective from its
first-order oracle. -/
theorem objective_convex (problem : ProjectedMultipleConstraintFirstOrderProblem E m) :
    ConvexOn ℝ Set.univ problem.objective :=
  problem.oracle.convexOn_univ

/-- Each constraint is convex on all of `E`, derived canonically from the inherited
whole-space owner. -/
theorem constraints_convex (problem : ProjectedMultipleConstraintFirstOrderProblem E m)
    (j : Fin m) :
    ConvexOn ℝ Set.univ (problem.constraints j) :=
  problem.toMultipleConstraintFirstOrderProblem.constraints_convex j

/-- The canonical bridge from the projected multi-constraint owner to the projected first-order
convex minimization owner on the same feasible set `Q`. -/
def toFirstOrderConvexMinimizationProblem
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) :
    FirstOrderConvexMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := problem.objective
  feasibleSet_nonempty := problem.feasibleSet_nonempty
  feasibleSet_closed := problem.feasibleSet_closed
  feasibleSet_convex := problem.feasibleSet_convex
  oracle := problem.oracle

/-- The Chapter 1 Lagrangian owner attached to the objective and constraint family of a
multiple-constraint first-order problem, restricted to the feasible-set domain `Q`. -/
def toLagrangianProblem (problem : ProjectedMultipleConstraintFirstOrderProblem E m) :
    LagrangianProblem problem.feasibleSet m where
  objective := fun x ↦ problem.objective x
  constraints := fun j x ↦ problem.constraints j x

/-- The active constraint set at `x` for threshold `h`, namely the indices `j` with
`f_j(x) > h ‖g_j(x)‖`. -/
def switchingActiveSet
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) (h : ℝ) (x : E) :
    Finset (Fin m) :=
  Finset.univ.filter fun j ↦
    let g := (problem.constraintOracle j).subgradient x
    h * ‖g‖ < problem.constraints j x

end ProjectedMultipleConstraintFirstOrderProblem

section Projection

variable [CompleteSpace E]

namespace ProjectedMultipleConstraintFirstOrderProblem

/-- The canonical Euclidean projection onto the feasible set `Q` of the projected specialization.
-/
noncomputable def projection
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) : E → E :=
  problem.toFirstOrderConvexMinimizationProblem.projection

/-- The canonical Euclidean projection lands in the feasible set `Q`. -/
@[simp] theorem projection_mem
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) (x : E) :
    problem.projection x ∈ problem.feasibleSet :=
  problem.toFirstOrderConvexMinimizationProblem.projection_mem x

/-- The projected normalized subgradient step of length `h` at `x`. -/
def normalizedSubgradientStep
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) (h : ℝ) (x : E) : E :=
  problem.toFirstOrderConvexMinimizationProblem.normalizedSubgradientStep h x

/-- The projected normalized subgradient step lands in the feasible set `Q`. -/
@[simp] theorem normalizedSubgradientStep_mem
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) (h : ℝ) (x : E) :
    problem.normalizedSubgradientStep h x ∈ problem.feasibleSet :=
  problem.toFirstOrderConvexMinimizationProblem.normalizedSubgradientStep_mem h x

/-- One branch-selected update of Algorithm 3.4 at the current point `x`: choose `none` for the
objective step and `some j` for the correction step using the selected active constraint `j`. -/
def switchingStep
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) (h : ℝ) (x : E) :
    Option (Fin m) → E
  | none => problem.normalizedSubgradientStep h x
  | some j =>
      let g := (problem.constraintOracle j).subgradient x
      problem.projection (x - (problem.constraintOracle j).correctionStepsize x • g)

/-- The iterate sequence of Algorithm 3.4 is determined recursively by the initial point `x₀`,
the constant threshold `h`, and the stepwise branch choices `j_k`. -/
def switchingIterates
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) (h : ℝ) (x0 : E)
    (selectedIndexAt : ℕ → Option (Fin m)) : ℕ → E
  | 0 => x0
  | k + 1 =>
      let xk := problem.switchingIterates h x0 selectedIndexAt k
      problem.switchingStep h xk (selectedIndexAt k)

end ProjectedMultipleConstraintFirstOrderProblem
end Projection

/-- Algorithm 3.4: a subgradient switching strategy for approximate Lagrange multipliers is
determined by a constrained first-order problem with feasible set `Q`, a feasible initial point
`x₀`, a scalar `h`, and a stepwise choice sequence `j_k`. Here `j_k = none` exactly on objective
iterations, while `j_k = some j` records the chosen active constraint `j ∈ 𝒥_k` on correction
iterations. This matches the textbook's arbitrary per-iteration choices `j_k ∈ 𝒥_k` without
packaging an off-trajectory selector. To keep the run owner below completeness, the iterate
sequence `x_k` is stored directly as primitive run data, while the textbook projection recursion
is recorded separately by `step_rule` exactly on the completeness-dependent layer where the
projection map is available. Positivity consequences for `h` are kept as separate theorem
hypotheses rather than as primitive owner data. -/
structure ApproximateLagrangeMultiplierSwitchingMethod
    (problem : ProjectedMultipleConstraintFirstOrderProblem E m) where
  /-- The prescribed initial point `x₀`. -/
  x0 : E
  /-- The initial point lies in the feasible set `Q`. -/
  x0_mem : x0 ∈ problem.feasibleSet
  /-- The constant scalar `h` from the textbook rule defining the active set. -/
  h : ℝ
  /-- The chosen branch at time `k`, recorded as `none` exactly on objective steps and as
  `some j` on selected active-constraint steps. -/
  selectedIndexAt : ℕ → Option (Fin m)
  /-- The iterate sequence `x₀, x₁, ...` of the run. -/
  iterates : ℕ → E
  /-- The zeroth iterate is the prescribed starting point `x₀`. -/
  iterates_zero : iterates 0 = x0
  /-- Along the run, the chosen branch is `none` exactly when the active set is empty and
  otherwise records an index from that active set. -/
  selectedIndexAt_valid (k : ℕ) :
    match selectedIndexAt k with
    | none => problem.switchingActiveSet h (iterates k) = ∅
    | some j => j ∈ problem.switchingActiveSet h (iterates k)
  /-- Whenever the projection operator is available, the iterates satisfy the textbook switching
  recursion. -/
  step_rule [CompleteSpace E] (k : ℕ) :
    iterates (k + 1) = problem.switchingStep h (iterates k) (selectedIndexAt k)

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

/-- An approximate-Lagrange-multiplier switching method can be used as its underlying iterate
sequence. -/
instance : CoeFun (ApproximateLagrangeMultiplierSwitchingMethod problem) (fun _ ↦ ℕ → E) where
  coe method := method.iterates

/-- The successor iterate `x_{k+1}` of the run. -/
def nextIterate
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) : E :=
  method (k + 1)

/-- The objective subgradient sequence `g(x_k)` attached to the iterates of Algorithm 3.4. -/
def objectiveSubgradient
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) : E :=
  problem.oracle.subgradient (method k)

/-- The active constraint set `𝒥_k` at time `k`, evaluated at the current iterate `x_k`. -/
def activeSet
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) : Finset (Fin m) :=
  problem.switchingActiveSet method.h (method k)

/-- The zeroth iterate is the prescribed starting point `x₀`. -/
@[simp] theorem iterates_zero_eq_x0
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) :
    method 0 = method.x0 :=
  method.iterates_zero

/-- Each successor iterate is the stored next iterate `x_{k+1}`. -/
@[simp] theorem iterates_succ
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) :
    method (k + 1) = method.nextIterate k :=
  rfl

/-- Along the actual run, the selector returns `none` exactly when the active set is empty and
otherwise returns an index in that active set. -/
theorem selectedIndexAt_spec
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) :
    match method.selectedIndexAt k with
    | none => method.activeSet k = ∅
    | some j => j ∈ method.activeSet k := by
  simpa [activeSet] using method.selectedIndexAt_valid k

/-- Under completeness, the stored successor iterate agrees with the textbook switching update
rule. -/
theorem nextIterate_eq_switchingStep [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) :
    method.nextIterate k =
      problem.switchingStep method.h (method k) (method.selectedIndexAt k) := by
  exact method.step_rule k

/-- On the objective branch, the projected update is the owner normalized subgradient step. -/
theorem nextIterate_eq_objective [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {k : ℕ}
    (hsel : method.selectedIndexAt k = none) :
    method.nextIterate k = problem.normalizedSubgradientStep method.h (method k) := by
  rw [method.nextIterate_eq_switchingStep]
  simp [ProjectedMultipleConstraintFirstOrderProblem.switchingStep, hsel]

/-- On a selected active-constraint branch, the projected update is the corresponding textbook
correction step with scalar `f_j(x) / ‖g_j(x)‖²`. -/
theorem nextIterate_eq_constraint [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {k : ℕ} {j : Fin m}
    (hsel : method.selectedIndexAt k = some j) :
    method.nextIterate k =
      problem.projection
        (method k - (problem.constraintOracle j).correctionStepsize (method k) •
          (problem.constraintOracle j).subgradient (method k)) := by
  rw [method.nextIterate_eq_switchingStep]
  simp [ProjectedMultipleConstraintFirstOrderProblem.switchingStep, hsel,
    FirstOrderOracle.correctionStepsize]

/-- Every one-step update belongs to the feasible set `Q`. -/
theorem nextIterate_mem [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) :
    method.nextIterate k ∈ problem.feasibleSet := by
  rw [method.nextIterate_eq_switchingStep]
  cases hsel : method.selectedIndexAt k <;>
    simp [ProjectedMultipleConstraintFirstOrderProblem.switchingStep]

/-- Every iterate produced by Algorithm 3.4 belongs to the feasible set `Q`. -/
theorem iterates_mem [CompleteSpace E]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ) :
    method k ∈ problem.feasibleSet := by
  induction k with
  | zero =>
      simpa [method.iterates_zero_eq_x0] using method.x0_mem
  | succ k _ =>
      rw [method.iterates_succ]
      exact method.nextIterate_mem k

end ApproximateLagrangeMultiplierSwitchingMethod

end
