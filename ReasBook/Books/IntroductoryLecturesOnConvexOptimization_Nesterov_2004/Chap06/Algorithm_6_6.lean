/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 6.6 lies in the Chapter 6 second-order trust-region / composite convex minimization
domain.

Mandatory domain-style sampling pass:
- `CompositeConvexMinimizationProblem` in `Chap03/Definition_3_21`, the chapter owner of the
  ambient closed convex composite problem;
- `ContractedFeasibleSetTrustRegionScheme` and `contractedFeasibleSet` in `Algorithm_6_5`, the
  chapter's recursive owner pattern for contracted trust-region updates;
- `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the canonical second-order Taylor
  model owner;
- `hessian` in `Chap01/Definition_1_4_16`, the canonical intrinsic Hessian operator used by that
  Taylor model.

Best owner abstraction:
- source-facing: `CompositeTrustRegionContractionMethod`;
- core/canonical: `CompositeConvexMinimizationProblem E`, `secondOrderTaylorModelAt`,
  `hessian`, `contractedFeasibleSet`, and `argmin[Q]`;
- bridge/view: the source-facing Taylor increment
  `secondOrderTaylorIncrementAt`, the composite local model built from it, and the recursive
  iterate sequence derived from a one-step solver.

Primitive data:
- the ambient composite convex problem `problem`;
- the prescribed initial feasible point `x₀ : problem.feasibleSet`;
- second-order regularity of the inherited smooth part on `problem.feasibleSet`;
- the contraction sequence `τ_t ∈ (0, 1]`;
- a chosen one-step solver for the contracted quadratic composite subproblem.

Derived API:
- the quadratic increment and composite model, both built from the canonical owner
  `secondOrderTaylorModelAt` instead of primitive gradient/Hessian fields;
- successor argmin membership and `IsMinOn`;
- the iterate family `x₀, x₁, x₂, ...`, defined recursively from the one-step solver;
- feasibility of every iterate, derived from convexity of the inherited feasible set.

This refinement moves Algorithm 6.6 to the same recursive owner layer already used by
Algorithm 6.5, deletes the duplicate primitive iterate/gradient/Hessian packaging, and keeps the
source-facing quadratic increment only as a thin bridge from the canonical Taylor-model owner. -/

/-- The source-facing quadratic increment of the canonical second-order Taylor model centered at
`x`, obtained by removing the constant term `f x`. -/
def secondOrderTaylorIncrementAt (f : E → ℝ) (x : E) : E → ℝ :=
  fun y ↦ secondOrderTaylorModelAt f x y - f x

/-- Evaluating `secondOrderTaylorIncrementAt f x` at `y` gives the linear term
`⟪∇ f(x), y - x⟫` plus the quadratic Hessian term. -/
theorem secondOrderTaylorIncrementAt_apply
    (f : E → ℝ) (x y : E) :
    secondOrderTaylorIncrementAt f x y =
      inner ℝ (∇ f x) (y - x) +
        (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x) := by
  simp [secondOrderTaylorIncrementAt, secondOrderTaylorModelAt_apply, hessian, add_assoc]

/-- The contracted composite second-order local model at `x`, written using the source-facing
quadratic increment together with the chapter owner `_root_.compositeObjective`. -/
def contractedCompositeSecondOrderModel
    (problem : CompositeConvexMinimizationProblem E) (x : E) : E → WithTop ℝ :=
  _root_.compositeObjective (secondOrderTaylorIncrementAt problem.smoothPart x)
    problem.nonsmoothPart

/-- Evaluating the contracted composite second-order model recovers the quadratic increment plus
the regularizer value. -/
theorem contractedCompositeSecondOrderModel_apply
    (problem : CompositeConvexMinimizationProblem E) (x y : E) :
    contractedCompositeSecondOrderModel problem x y =
      (((inner ℝ (∇ problem.smoothPart x) (y - x) +
          (1 / 2 : ℝ) *
            inner ℝ (hessian problem.smoothPart x (y - x)) (y - x) : ℝ) :
        WithTop ℝ) + problem.nonsmoothPart y) := by
  simp [contractedCompositeSecondOrderModel, secondOrderTaylorIncrementAt_apply]

/-- Algorithm 6.6: for a composite convex minimization problem `problem`, a composite trust-
region method with contraction consists of a twice continuously differentiable inherited smooth
part on the feasible set, an initial feasible point `x₀`, a contraction sequence `τ_t ∈ (0, 1]`,
and a chosen one-step solver sending each feasible current iterate `x_t` to a successor
`x_{t+1}` that minimizes the contracted quadratic composite subproblem
`arg min_{y = (1 - τ_t) x_t + τ_t x, x ∈ Q}
  ⟪∇ f(x_t), y - x_t⟫ + (1 / 2) ⟪∇² f(x_t) (y - x_t), y - x_t⟫ + Ψ(y)`. -/
structure CompositeTrustRegionContractionMethod
    (problem : CompositeConvexMinimizationProblem E) (x0 : problem.feasibleSet) where
  /-- The inherited smooth part is twice continuously differentiable on the feasible set. -/
  objective_contDiffOn : ContDiffOn ℝ 2 problem.smoothPart problem.feasibleSet
  /-- The contraction sequence `τ₀, τ₁, τ₂, ...`. -/
  stepSize : ℕ → ℝ
  /-- Each contraction factor lies in `(0, 1]`. -/
  stepSize_mem_Ioc : ∀ t : ℕ, stepSize t ∈ Set.Ioc (0 : ℝ) 1
  /-- The chosen contracted quadratic subproblem solver at time `t` and feasible current point
  `x_t`. -/
  nextIterate (t : ℕ) (x : problem.feasibleSet) : E
  /-- The one-step solver returns a minimizer of the contracted quadratic composite model centered
  at the current feasible iterate. -/
  nextIterate_mem_argmin (t : ℕ) (x : problem.feasibleSet) :
    nextIterate t x ∈
      argmin[contractedFeasibleSet problem.feasibleSet (x : E) (stepSize t)]
        (contractedCompositeSecondOrderModel problem x)

namespace CompositeTrustRegionContractionMethod

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- Every one-step update chosen by Algorithm 6.6 remains in the inherited feasible set `Q`. -/
theorem nextIterate_mem_feasibleSet
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (x : problem.feasibleSet) :
    method.nextIterate t x ∈ problem.feasibleSet := by
  have hstep :
      method.nextIterate t x ∈
        contractedFeasibleSet problem.feasibleSet (x : E) (method.stepSize t) :=
    (mem_constrainedArgmin_iff.mp (method.nextIterate_mem_argmin t x)).1
  rcases (mem_contractedFeasibleSet_iff.mp hstep) with ⟨z, hzQ, hz⟩
  rw [hz]
  have hτ := method.stepSize_mem_Ioc t
  simpa [AffineMap.lineMap_apply_module] using
    problem.feasibleSet_convex.lineMap_mem x.property hzQ ⟨le_of_lt hτ.1, hτ.2⟩

/-- The iterate sequence starts from `x₀` and recursively applies the contracted quadratic
subproblem solver at each feasible iterate. -/
def iterates
    (method : CompositeTrustRegionContractionMethod problem x0) :
    ℕ → problem.feasibleSet
  | 0 => x0
  | t + 1 =>
      let x := iterates method t
      ⟨method.nextIterate t x, method.nextIterate_mem_feasibleSet t x⟩

/-- A composite trust-region method with contraction can be used as its iterate sequence. -/
instance :
    CoeFun (CompositeTrustRegionContractionMethod problem x0) (fun _ ↦ ℕ → E) where
  coe method := fun t ↦ method.iterates t

/-- The zeroth iterate is the prescribed initial point `x₀`. -/
@[simp] theorem x_zero
    (method : CompositeTrustRegionContractionMethod problem x0) :
    method 0 = x0 :=
  rfl

/-- Each successor iterate is obtained by applying the contracted quadratic subproblem solver to
the previous feasible iterate. -/
@[simp] theorem iterates_succ
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method (t + 1) = method.nextIterate t (method.iterates t) :=
  rfl

omit [CompleteSpace E] in
/-- The prescribed initial point `x₀` belongs to the feasible set `Q`. -/
theorem x0_mem :
    (x0 : E) ∈ problem.feasibleSet :=
  x0.property

/-- Each successor iterate belongs to the argmin set of the contracted quadratic composite
subproblem at the previous iterate. -/
theorem iterates_succ_mem_argmin
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method (t + 1) ∈
      argmin[contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t)]
        (contractedCompositeSecondOrderModel problem (method t)) := by
  simpa using method.nextIterate_mem_argmin t (method.iterates t)

/-- Each successor iterate belongs to the contracted feasible set and minimizes the quadratic
composite local model there. -/
theorem iterates_succ_mem_and_isMinOn
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method (t + 1) ∈ contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t) ∧
      IsMinOn
        (contractedCompositeSecondOrderModel problem (method t))
        (contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t))
        (method (t + 1)) := by
  exact mem_constrainedArgmin_iff.mp (method.iterates_succ_mem_argmin t)

/-- Every iterate produced by Algorithm 6.6 belongs to the inherited feasible set `Q`. -/
theorem iterates_mem_feasibleSet
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method t ∈ problem.feasibleSet :=
  (method.iterates t).property

end CompositeTrustRegionContractionMethod

end
