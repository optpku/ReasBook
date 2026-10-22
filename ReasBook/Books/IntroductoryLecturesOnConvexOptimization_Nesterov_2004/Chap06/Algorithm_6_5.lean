/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Algorithm 6.5 lies in the Chapter 6 contracted conditional-gradient / composite convex
minimization domain.

Sampled owner-style declarations:
- `CompositeConvexMinimizationProblem` in `Chap03/Definition_3_21`, the chapter owner of a
  closed convex feasible set together with a smooth convex term and a closed convex regularizer;
- `HasFDerivWithinAt` and `HasFDerivWithinAt.fderivWithin` in `Chap02/Definition_2_6`, the
  canonical pointwise within-derivative owner and its recovery of `fderivWithin` on feasible
  sets;
- `_root_.compositeObjective` in `Chap03/Definition_3_21`, the canonical owner for affine-plus-
  regularizer models with `WithTop ℝ` values;
- `AffineMap.lineMap`, the canonical affine owner for contractions
  `z ↦ (1 - τ) • x + τ • z`;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for constrained minimizers.

Best owner abstraction:
- source-facing: `ContractedFeasibleSetTrustRegionScheme`;
- core/canonical: `CompositeConvexMinimizationProblem E`, `AffineMap.lineMap`,
  `_root_.compositeObjective`, and `argmin[Q]`;
- bridge/view: `mem_contractedFeasibleSet_iff`, the recursive iterate sequence `iterates`,
  `iterates_succ_mem_and_isMinOn`, and the derived iterate-feasibility theorem below.

Primitive data:
- the ambient composite convex problem `problem`;
- the prescribed initial feasible point `x₀ : problem.feasibleSet`;
- the canonical within-feasible-set derivative witness for the inherited smooth part on
  `problem.feasibleSet`;
- the step-size sequence `τ_t`;
- a chosen one-step solver `x ↦ x⁺` for each contracted linearized subproblem.

Derived API:
- closedness/convexity of the feasible set and closed-convex regularizer data, inherited from
  `problem` rather than re-stored primitively;
- the contracted feasible set;
- the canonical affine-plus-regularizer local model, expressed directly through
  `_root_.compositeObjective`;
- successor argmin membership and `IsMinOn`;
- the recursive iterate sequence `x₀, x₁, x₂, ...`, defined from the one-step solver;
- feasibility of all iterates, derived from convexity of the inherited feasible set.

This refinement keeps Algorithm 6.5 as the source-facing owner, but moves its ambient problem
data onto the existing chapter owner `CompositeConvexMinimizationProblem`, deletes the exact-
interface linear-model wrapper in favor of `_root_.compositeObjective`, and keeps the public
algorithm centered on the recursive contracted-step construction instead of a primitive full
iterate sequence. -/

/-- The contracted feasible set obtained from `Q` by moving every feasible point toward the
current iterate `x` with contraction factor `τ`. -/
def contractedFeasibleSet (Q : Set E) (x : E) (τ : ℝ) : Set E :=
  (fun z : E ↦ AffineMap.lineMap x z τ) '' Q

-- Proof sketch: unfold `contractedFeasibleSet`, rewrite image membership, and expand
-- `AffineMap.lineMap`.
/-- Membership in `contractedFeasibleSet Q x τ` means that the point is of the form
`(1 - τ) x + τ z` for some feasible point `z ∈ Q`. -/
theorem mem_contractedFeasibleSet_iff
    {Q : Set E} {x y : E} {τ : ℝ} :
    y ∈ contractedFeasibleSet Q x τ ↔ ∃ z ∈ Q, y = (1 - τ) • x + τ • z := by
  constructor
  · rintro ⟨z, hzQ, rfl⟩
    exact ⟨z, hzQ, by simpa using AffineMap.lineMap_apply_module x z τ⟩
  · rintro ⟨z, hzQ, rfl⟩
    exact ⟨z, hzQ, by simpa using AffineMap.lineMap_apply_module x z τ⟩

section

/-- Algorithm 6.5: for a composite convex minimization problem `problem`, a contracted-feasible-
set trust-region scheme with linear model consists of the canonical within-derivative witness for
the inherited smooth part on the feasible set, an initial feasible point `x₀`, a step-size
sequence `τ_t ∈ (0, 1]`, and a chosen one-step rule sending each feasible current iterate `x_t`
to a successor `x_{t+1}` that minimizes the canonical affine-plus-regularizer model
`_root_.compositeObjective (fun y ↦ fderivWithin ℝ f Q x_t y) Ψ`
on the contracted feasible set
`{(1 - τ_t) x_t + τ_t x | x ∈ Q}`. -/
structure ContractedFeasibleSetTrustRegionScheme
    (problem : CompositeConvexMinimizationProblem E) (x0 : problem.feasibleSet) where
  /-- The inherited smooth part has the canonical within derivative at every feasible point. -/
  smoothPart_hasFDerivWithinAt :
    ∀ x : problem.feasibleSet,
      HasFDerivWithinAt problem.smoothPart
        (fderivWithin ℝ problem.smoothPart problem.feasibleSet x)
        problem.feasibleSet x
  /-- The step-size sequence `τ₀, τ₁, τ₂, ...`. -/
  stepSize : ℕ → ℝ
  /-- Each step size belongs to `(0, 1]`. -/
  stepSize_mem_Ioc : ∀ t : ℕ, stepSize t ∈ Set.Ioc (0 : ℝ) 1
  /-- The chosen one-step contracted subproblem solver at time `t` and feasible current point
  `x_t`. -/
  nextIterate (t : ℕ) (x : problem.feasibleSet) : E
  /-- The chosen one-step solver returns a minimizer of the contracted linearized composite model
  centered at the current feasible point `x_t`. -/
  nextIterate_mem_argmin (t : ℕ) (x : problem.feasibleSet) :
    nextIterate t x ∈
      argmin[contractedFeasibleSet problem.feasibleSet (x : E) (stepSize t)]
        (_root_.compositeObjective
          (fun y ↦ fderivWithin ℝ problem.smoothPart problem.feasibleSet x y)
          problem.nonsmoothPart)

namespace ContractedFeasibleSetTrustRegionScheme

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- The canonical derivative field attached to Algorithm 6.5, obtained from the within-feasible-
set derivative of the inherited smooth part. -/
abbrev gradient
    (_method : ContractedFeasibleSetTrustRegionScheme problem x0) : E → StrongDual ℝ E :=
  fun x ↦ fderivWithin ℝ problem.smoothPart problem.feasibleSet x

/-- At every feasible point, `gradient` recovers the within-feasible-set derivative stored in the
scheme data. -/
theorem hasFDerivWithinAt_gradient
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
    {x : E} (hx : x ∈ problem.feasibleSet) :
    HasFDerivWithinAt problem.smoothPart (method.gradient x) problem.feasibleSet x := by
  simpa [gradient] using method.smoothPart_hasFDerivWithinAt ⟨x, hx⟩

/-- Every one-step update chosen by Algorithm 6.5 remains in the inherited feasible set `Q`. -/
theorem nextIterate_mem_feasibleSet
    (method : ContractedFeasibleSetTrustRegionScheme problem x0)
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

/-- The iterate sequence starts from `x₀` and recursively applies the contracted subproblem
solver at each feasible iterate. -/
def iterates
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) :
    ℕ → problem.feasibleSet
  | 0 => x0
  | t + 1 =>
      let x := iterates method t
      ⟨method.nextIterate t x, method.nextIterate_mem_feasibleSet t x⟩

/-- A contracted-feasible-set trust-region scheme can be used as its iterate sequence. -/
instance :
    CoeFun (ContractedFeasibleSetTrustRegionScheme problem x0) (fun _ ↦ ℕ → E) where
  coe method := fun t ↦ method.iterates t

/-- The zeroth iterate is the prescribed initial point `x₀`. -/
@[simp] theorem x_zero
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) :
    method 0 = x0 :=
  rfl

/-- Each successor iterate is obtained by applying the contracted one-step solver to the previous
feasible iterate. -/
@[simp] theorem iterates_succ
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (t : ℕ) :
    method (t + 1) = method.nextIterate t (method.iterates t) :=
  rfl

/-- The prescribed initial point `x₀` of the scheme belongs to the feasible set `Q`. -/
theorem x0_mem :
    (x0 : E) ∈ problem.feasibleSet :=
  x0.property

/-- Each successor iterate belongs to the argmin set of the linearized composite subproblem at
the previous iterate. -/
theorem iterates_succ_mem_argmin
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (t : ℕ) :
    method (t + 1) ∈
      argmin[contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t)]
        (_root_.compositeObjective
          (fun y ↦ fderivWithin ℝ problem.smoothPart problem.feasibleSet (method t) y)
          problem.nonsmoothPart) := by
  simpa using method.nextIterate_mem_argmin t (method.iterates t)

/-- Each successor iterate belongs to the contracted feasible set and minimizes the linearized
composite model there. -/
theorem iterates_succ_mem_and_isMinOn
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (t : ℕ) :
    method (t + 1) ∈ contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t) ∧
      IsMinOn
        (_root_.compositeObjective
          (fun y ↦ fderivWithin ℝ problem.smoothPart problem.feasibleSet (method t) y)
          problem.nonsmoothPart)
        (contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t))
        (method (t + 1)) := by
  exact mem_constrainedArgmin_iff.mp (method.iterates_succ_mem_argmin t)

/-- Every iterate produced by Algorithm 6.5 belongs to the inherited feasible set `Q`. -/
theorem iterates_mem_feasibleSet
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (t : ℕ) :
    method t ∈ problem.feasibleSet :=
  (method.iterates t).property

end ContractedFeasibleSetTrustRegionScheme

end

end
