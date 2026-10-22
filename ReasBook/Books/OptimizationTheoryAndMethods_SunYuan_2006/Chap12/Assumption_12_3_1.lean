/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Order.Filter.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_6_7

noncomputable section

section Chapter12Assumption1231

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)

-- Canonical reuse:
-- * `StandardPenaltyProblem` is the repository owner for mixed equality/inequality problems.
-- * `StandardPenaltyProblem.activeConstraintSet` is the Chapter 10 bridge to the canonical
--   Chapter 8 active-set owner on `problem.toConstrainedOptimizationProblem`.
-- * `StandardPenaltyProblem.LicqAt` and Chapter 10's KKT owner are the canonical
--   constraint-qualification and multiplier layers on the mixed-constraint surface.
-- * This file keeps only the Chapter 12 SQP-specific source-facing companions and bridges.

namespace StandardPenaltyProblem

/-- The source active-inequality set `I(x)` of `problem`, written on the canonical Chapter 8
active-index owner of `problem.toConstrainedOptimizationProblem`. -/
noncomputable abbrev activeIneqIndexSet
    (problem : StandardPenaltyProblem n m) (x : Point) : Set (Fin m) :=
  problem.toConstrainedOptimizationProblem.activeIneqIndexSet x.ofLp

/-- The source Hessian operator `W(x, lam)` of `problem`, written on the canonical Chapter 8
Lagrangian-Hessian owner of `problem.toConstrainedOptimizationProblem`. -/
noncomputable abbrev lagrangianHessianAt
    (problem : StandardPenaltyProblem n m) (x : Point) (lam : Multiplier) :
    Point →L[ℝ] Point :=
  problem.toConstrainedOptimizationProblem.lagrangianHessianAt x.ofLp lam.ofLp

/-- Membership in `I[problem](xStar)` is exactly the source active-inequality condition
`i ∈ I(xStar)`. -/
@[simp] theorem mem_activeIneqIndexSet_iff
    (problem : StandardPenaltyProblem n m) (xStar : Point) (i : Fin m) :
    i ∈ problem.activeIneqIndexSet xStar ↔
      problem.eqCount ≤ i.1 ∧ problem.constraint i xStar = 0 :=
  problem.mem_activeIneqIndexSet_toConstrainedOptimizationProblem_iff xStar i

/-- Rewriting `i ∈ problem.activeConstraintSet xStar` through `problem.activeIneqIndexSet xStar`
recovers the source decomposition `E ∪ I(xStar)`. -/
theorem mem_activeConstraintSet_iff_eq_or_mem_activeIneqIndexSet
    (problem : StandardPenaltyProblem n m) (xStar : Point) (i : Fin m) :
    i ∈ problem.activeConstraintSet xStar ↔
      i.1 < problem.eqCount ∨ i ∈ problem.activeIneqIndexSet xStar := by
  rw [mem_activeConstraintSet_iff, mem_activeIneqIndexSet_iff]

/-- A multiplier vector `lamStar` is a Chapter 12 SQP KKT multiplier at `xStar` when `xStar`
satisfies the equality and inequality constraints, the inequality multipliers are nonnegative,
the Lagrangian is stationary at `xStar`, and complementary slackness holds on the inequality
block. -/
class IsSqpLagrangeMultiplier
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : Multiplier) : Prop where
  feasible_eq :
    ∀ i : Fin m, i.1 < problem.eqCount → problem.constraint i xStar = 0
  feasible_ineq :
    ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ problem.constraint i xStar
  dualFeasible :
    ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ lamStar i
  stationarity :
    gradient (fun x : Point ↦ problem.lagrangian x lamStar) xStar = 0
  complementarySlackness :
    ∀ i : Fin m, problem.eqCount ≤ i.1 → lamStar i * problem.constraint i xStar = 0

/-- Unfolding formula for `problem.IsSqpLagrangeMultiplier xStar lamStar`. -/
theorem isSqpLagrangeMultiplier_iff
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : Multiplier) :
    problem.IsSqpLagrangeMultiplier xStar lamStar ↔
      (∀ i : Fin m, i.1 < problem.eqCount → problem.constraint i xStar = 0) ∧
        (∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ problem.constraint i xStar) ∧
        (∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ lamStar i) ∧
        gradient (fun x : Point ↦ problem.lagrangian x lamStar) xStar = 0 ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 →
          lamStar i * problem.constraint i xStar = 0 := by
  constructor
  · intro h
    exact ⟨h.feasible_eq, h.feasible_ineq, h.dualFeasible, h.stationarity,
      h.complementarySlackness⟩
  · rintro ⟨h_feasible_eq, h_feasible_ineq, h_dualFeasible, h_stationarity, h_slack⟩
    exact
      ⟨h_feasible_eq, h_feasible_ineq, h_dualFeasible, h_stationarity, h_slack⟩

/-- A Chapter 12 SQP KKT multiplier is feasible for `problem`. -/
theorem IsSqpLagrangeMultiplier.feasible
    {problem : StandardPenaltyProblem n m} {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsSqpLagrangeMultiplier xStar lamStar) :
    xStar ∈ problem := by
  change xStar ∈ problem.feasibleSet
  rw [mem_feasibleSet_iff]
  exact ⟨h.feasible_eq, h.feasible_ineq⟩

/-- Under the global `C²` assumptions used in Assumption 12.3.1, a Chapter 12 SQP KKT
multiplier gives the canonical Chapter 10 KKT owner. -/
theorem IsSqpLagrangeMultiplier.toIsLagrangeMultiplier_of_contDiff
    {problem : StandardPenaltyProblem n m} {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsSqpLagrangeMultiplier xStar lamStar)
    (h_objective : ContDiff ℝ 2 problem.objective)
    (h_constraint : ∀ i : Fin m, ContDiff ℝ 2 (problem.constraint i)) :
    problem.IsLagrangeMultiplier xStar lamStar := by
  -- Package the SQP-side feasibility, stationarity, and slackness data into the Chapter 10 owner.
  refine (problem.isLagrangeMultiplier_iff xStar lamStar).2 ⟨h.feasible, h.dualFeasible, ?_, ?_,
    h.complementarySlackness⟩
  · -- The global `C²` hypotheses give differentiability of the Point-side Lagrangian.
    have hObjectiveContDiffAt : ContDiffAt ℝ 2 problem.objective xStar :=
      h_objective.contDiffAt
    have hConstraintSumContDiffAt :
        ContDiffAt ℝ 2
          (fun x : Point ↦ ∑ i : Fin m, lamStar i * problem.constraint i x)
          xStar := by
      refine ContDiffAt.sum ?_
      intro i _
      exact contDiffAt_const.mul (h_constraint i).contDiffAt
    have hLagrangianContDiffAt :
        ContDiffAt ℝ 2 (fun x : Point ↦ problem.lagrangian x lamStar) xStar := by
      simpa [StandardPenaltyProblem.lagrangian_eq] using
        hObjectiveContDiffAt.sub hConstraintSumContDiffAt
    exact hLagrangianContDiffAt.differentiableAt (by norm_num)
  · -- The stored SQP stationarity condition is already the Chapter 10 stationarity field.
    exact h.stationarity

/-- `problem.activeConstraintOrthogonal xStar d` is the source condition `A(xStar)ᵀ d = 0`,
written componentwise against every index in `E ∪ I(xStar)`. -/
def activeConstraintOrthogonal
    (problem : StandardPenaltyProblem n m) (xStar d : Point) : Prop :=
  ∀ i : Fin m, i ∈ problem.activeConstraintSet xStar →
    problem.linearizedConstraintPairing xStar d i = 0

/-- Unfolding `problem.activeConstraintOrthogonal xStar d` gives the componentwise orthogonality
conditions against the active constraint gradients. -/
theorem activeConstraintOrthogonal_iff
    (problem : StandardPenaltyProblem n m) (xStar d : Point) :
    problem.activeConstraintOrthogonal xStar d ↔
      ∀ i : Fin m, i ∈ problem.activeConstraintSet xStar →
        problem.linearizedConstraintPairing xStar d i = 0 :=
  Iff.rfl

/-- Evaluating `W[problem](xStar, lamStar)` on `d` gives the Fréchet derivative of the gradient
of the Lagrangian at `(xStar, lamStar)` applied to `d`. -/
theorem lagrangianHessianAt_apply
    (problem : StandardPenaltyProblem n m)
    (xStar : Point) (lamStar : Multiplier) (d : Point) :
    problem.lagrangianHessianAt xStar lamStar d =
      (fderiv ℝ (gradient (fun x : Point ↦ problem.lagrangian x lamStar)) xStar) d :=
by
  -- Unfold the Chapter 8 Hessian owner and rewrite its Euclidean Lagrangian to the Point-side
  -- Lagrangian used in this file.
  simp [StandardPenaltyProblem.lagrangianHessianAt,
    ConstrainedOptimizationProblem.lagrangianHessianAt,
    problem.euclideanLagrangian_eq_lagrangian lamStar]

/-- The canonical quadratic form `problem.lagrangianHessianQuadratic xStar lamStar d` agrees
with the operator expression `dᵀ W(xStar, lamStar) d`. -/
theorem lagrangianHessianQuadratic_eq_dotProduct_lagrangianHessianAt
    (problem : StandardPenaltyProblem n m)
    (xStar : Point) (lamStar : Multiplier) (d : Point) :
    problem.lagrangianHessianQuadratic xStar lamStar d =
      dotProduct d (problem.lagrangianHessianAt xStar lamStar d) := by
  -- Rewrite the canonical quadratic form to the Euclidean inner product expression.
  rw [StandardPenaltyProblem.lagrangianHessianQuadratic_eq,
    ConstrainedOptimizationProblem.lagrangianHessianQuadratic_eq]
  -- Replace the transported Hessian operator by the Point-side operator from this file.
  rw [StandardPenaltyProblem.lagrangianHessianAt_apply]
  -- Over `ℝ`, the Euclidean inner product is the coordinate dot product up to argument order.
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]

/-- `problem.SqpSecondOrderSufficientCondition xStar lamStar` is the source condition `(12.3.6)`:
the quadratic form `d ↦ dᵀ W(xStar, lamStar) d` is strictly positive on every nonzero direction
annihilated by `A(xStar)ᵀ`. -/
def SqpSecondOrderSufficientCondition
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : Multiplier) : Prop :=
  ∀ d : Point,
    d ≠ 0 →
    problem.activeConstraintOrthogonal xStar d →
    0 < problem.lagrangianHessianQuadratic xStar lamStar d

/-- Unfolding formula for `problem.SqpSecondOrderSufficientCondition xStar lamStar`. -/
theorem sqpSecondOrderSufficientCondition_iff
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : Multiplier) :
    problem.SqpSecondOrderSufficientCondition xStar lamStar ↔
      ∀ d : Point,
        d ≠ 0 →
        problem.activeConstraintOrthogonal xStar d →
        0 < problem.lagrangianHessianQuadratic xStar lamStar d :=
  Iff.rfl

/-- The source second-order sufficient condition `(12.3.6)` implies the Chapter 12
nondegeneracy condition `dᵀ W(xStar, lamStar) d ≠ 0` on the nullspace of `A(xStar)ᵀ`. -/
theorem lagrangianHessianQuadratic_ne_zero_of_sqpSecondOrderSufficientCondition
    (problem : StandardPenaltyProblem n m) {xStar : Point} {lamStar : Multiplier}
    (h_sosc : problem.SqpSecondOrderSufficientCondition xStar lamStar) :
    ∀ d : Point,
      d ≠ 0 →
      problem.activeConstraintOrthogonal xStar d →
      problem.lagrangianHessianQuadratic xStar lamStar d ≠ 0 := by
  intro d hd h_orthogonal
  exact ne_of_gt (h_sosc d hd h_orthogonal)

end StandardPenaltyProblem

/-- Chapter12 Assumption 12.3.1: for the SQP problem `problem`, the objective and constraints are
twice continuously differentiable, the iterates `xSeq k` converge to a KKT point `xStar` with
multiplier `lamStar`, the active gradients `∇ c_i(xStar)` for `i ∈ E ∪ I(xStar)` are linearly
independent, the quadratic form `d ↦ dᵀ W(xStar, lamStar) d` is nondegenerate on the nullspace
of `A(xStar)ᵀ`, and the active inequality set at the solution is eventually identified by the
working sets `activeSet k`. -/
structure HasSqpSuperlinearConvergenceAssumptions
    (problem : StandardPenaltyProblem n m) (xSeq : ℕ → Point) where
  activeSet : ℕ → Set (Fin m)
  xStar : Point
  lamStar : Multiplier
  objective_contDiff : ContDiff ℝ 2 problem.objective
  constraint_contDiff : ∀ i : Fin m, ContDiff ℝ 2 (problem.constraint i)
  tendsto_xSeq : Filter.Tendsto xSeq Filter.atTop (nhds xStar)
  isSqpLagrangeMultiplier : problem.IsSqpLagrangeMultiplier xStar lamStar
  activeConstraint_linearIndependent :
    LinearIndepOn ℝ (fun i : Fin m ↦ gradient (problem.constraint i) xStar)
      (problem.activeConstraintSet xStar)
  lagrangianHessianQuadratic_nondegenerate :
    ∀ d : Point,
      d ≠ 0 →
      problem.activeConstraintOrthogonal xStar d →
      problem.lagrangianHessianQuadratic xStar lamStar d ≠ 0
  activeSet_eventually_eq :
    ∀ᶠ k in Filter.atTop, activeSet k = problem.activeIneqIndexSet xStar

/-- A Chapter 12 SQP assumption package provides the source-facing SQP KKT multiplier data at its
limit point. -/
instance HasSqpSuperlinearConvergenceAssumptions.instIsSqpLagrangeMultiplier
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    problem.IsSqpLagrangeMultiplier h.xStar h.lamStar :=
  h.isSqpLagrangeMultiplier

/-- The global `C²` and active-gradient assumptions in `h` recover the canonical Chapter 10 LICQ
owner at the limit point `h.xStar`. -/
theorem HasSqpSuperlinearConvergenceAssumptions.licqAt
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    problem.LicqAt h.xStar := by
  -- Transport the source constraint regularity across the Chapter 10 bridge.
  have hToLpContDiffAt :
      ContDiffAt ℝ 2 (WithLp.toLp 2 : (Fin n → ℝ) → Point) h.xStar.ofLp :=
    PiLp.contDiff_toLp.contDiffAt
  have hBridgeConstraintContDiffAt :
      ∀ i,
        ContDiffAt ℝ 2 (problem.toConstrainedOptimizationProblem.constraint i) h.xStar.ofLp := by
    intro i
    change ContDiffAt ℝ 2 (problem.constraint i ∘ WithLp.toLp 2) h.xStar.ofLp
    simpa [Function.comp] using
      ((h.constraint_contDiff i).contDiffAt.comp h.xStar.ofLp hToLpContDiffAt)
  have hEuclideanConstraintEq :
      ∀ i : Fin m,
        problem.toConstrainedOptimizationProblem.euclideanConstraint i = problem.constraint i := by
    intro i
    funext x
    simp [ConstrainedOptimizationProblem.euclideanConstraint,
      StandardPenaltyProblem.toConstrainedOptimizationProblem,
      Function.comp]
  have hGradientFamilyEq :
      (fun i : Fin m ↦
        gradient (problem.toConstrainedOptimizationProblem.euclideanConstraint i) h.xStar) =
        fun i : Fin m ↦ gradient (problem.constraint i) h.xStar := by
    funext i
    rw [hEuclideanConstraintEq i]
  refine
    { hasActiveConstraintGradientsAt := ?_
      linearIndepOn := ?_ }
  · -- Every bridge constraint is differentiable at `h.xStar`, hence every active one is.
    intro i hi
    exact (hBridgeConstraintContDiffAt i).differentiableAt (by norm_num)
  · -- The stored active-gradient independence is already the LICQ linear-independence field.
    simpa [StandardPenaltyProblem.activeConstraintSet, hGradientFamilyEq] using
      h.activeConstraint_linearIndependent

/-- A Chapter 12 SQP assumption package also provides the canonical Chapter 10 LICQ owner at its
limit point. -/
instance HasSqpSuperlinearConvergenceAssumptions.instLicqAt
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    problem.LicqAt h.xStar :=
  h.licqAt

/-- A Chapter 12 SQP assumption package also provides the canonical Chapter 10 KKT owner at its
limit point. -/
instance HasSqpSuperlinearConvergenceAssumptions.instIsLagrangeMultiplier
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    problem.IsLagrangeMultiplier h.xStar h.lamStar :=
  h.isSqpLagrangeMultiplier.toIsLagrangeMultiplier_of_contDiff
    h.objective_contDiff h.constraint_contDiff

/-- The working sets in `h` agree with the active inequality set `I(h.xStar)` for all
sufficiently large iterates. -/
theorem HasSqpSuperlinearConvergenceAssumptions.eventuallyEq_activeSet
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    ∀ᶠ k in Filter.atTop, h.activeSet k = problem.activeIneqIndexSet h.xStar :=
  h.activeSet_eventually_eq

/-- The working sets in `h` eventually agree with the active inequality set `I(h.xStar)`. -/
theorem HasSqpSuperlinearConvergenceAssumptions.eventually_activeSet_eq
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    ∃ N : ℕ, ∀ ⦃k : ℕ⦄, N ≤ k → h.activeSet k = problem.activeIneqIndexSet h.xStar := by
  simpa [Filter.eventually_atTop] using h.eventuallyEq_activeSet

/-- The Chapter 12 assumption package exposes the nondegeneracy condition
`dᵀ W(h.xStar, h.lamStar) d ≠ 0` on the nullspace of `A(h.xStar)ᵀ`. -/
theorem HasSqpSuperlinearConvergenceAssumptions.lagrangianHessianQuadratic_ne_zero
    {problem : StandardPenaltyProblem n m} {xSeq : ℕ → Point}
    (h : HasSqpSuperlinearConvergenceAssumptions problem xSeq) :
    ∀ d : Point,
      d ≠ 0 →
      problem.activeConstraintOrthogonal h.xStar d →
      problem.lagrangianHessianQuadratic h.xStar h.lamStar d ≠ 0 :=
  h.lagrangianHessianQuadratic_nondegenerate

end Chapter12Assumption1231
