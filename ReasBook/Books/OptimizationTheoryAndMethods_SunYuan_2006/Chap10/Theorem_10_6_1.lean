/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.StandardPenaltyProblemBridge
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Filter

section Chapter10Theorem1061

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "∇" => @gradient ℝ Point _ _ _ _

-- Domain sampling:
-- * `StandardPenaltyProblem`, `problem.feasibleSet`, and the source notation `c⁽-⁾[problem]`
--   are already owned by `Definition_10_1_extra_1`.
-- * `StandardPenaltyProblem.toConstrainedOptimizationProblem` and
--   `StandardPenaltyProblem.IsGlobalMinimizer` are the chapter's reusable mixed-constraint
--   bridge/view owners in `StandardPenaltyProblemBridge`.
-- * `ConstrainedOptimizationProblem.IsKKTPoint`,
--   `ConstrainedOptimizationProblem.linearizedFeasibleDirectionSet`, and
--   `ConstrainedOptimizationProblem.lagrangianHessianQuadratic` in Chapter 8 are the canonical
--   constrained-optimization owners reused here through a mixed-constraint bridge.
-- * `IsStrongDistanceFunction` is the chapter's canonical kernel owner from
--   `Definition_10_6_extra_1`.
-- * `IsStrictLocalMin` is the canonical strict local minimizer owner from
--   `Chapter01.Definition_1_4_1`.
-- This file therefore keeps the Chapter 10 source-facing SOSC surface and strict-penalty
-- conclusion while presenting its KKT, feasible-direction, and Hessian APIs as thin bridges to
-- the Chapter 8 constrained-optimization owners.

namespace StandardPenaltyProblem

/-- The finite-sum Lagrangian associated to `problem` and multiplier vector `lam`, viewed through
the Chapter 8 constrained-problem bridge. -/
noncomputable abbrev lagrangian
    (problem : StandardPenaltyProblem n m) (x : Point) (lam : ConstraintPoint) : ℝ :=
  problem.toConstrainedOptimizationProblem.lagrangian x.ofLp lam.ofLp

/-- Evaluating `problem.lagrangian x lam` expands to the source finite-sum formula. -/
theorem lagrangian_eq
    (problem : StandardPenaltyProblem n m) (x : Point) (lam : ConstraintPoint) :
    problem.lagrangian x lam =
      problem.objective x - ∑ i : Fin m, lam i * problem.constraint i x := by
  simp [StandardPenaltyProblem.lagrangian, StandardPenaltyProblem.toConstrainedOptimizationProblem,
    ConstrainedOptimizationProblem.lagrangian]

@[simp] theorem toLp_of_euclideanEquiv (x : Point) :
    WithLp.toLp 2 ((EuclideanSpace.equiv (Fin n) ℝ) x) = x := by
  ext i
  rfl

/-- The Euclidean Chapter 8 Lagrangian bridge agrees with the Chapter 10 mixed-constraint
Lagrangian on `Point = ℝⁿ`. -/
theorem euclideanLagrangian_eq_lagrangian
    (problem : StandardPenaltyProblem n m) (lam : ConstraintPoint) :
    problem.toConstrainedOptimizationProblem.euclideanLagrangian lam.ofLp =
      fun x : Point ↦ problem.lagrangian x lam := by
  funext x
  simp [StandardPenaltyProblem.lagrangian, StandardPenaltyProblem.toConstrainedOptimizationProblem,
    ConstrainedOptimizationProblem.euclideanLagrangian, ConstrainedOptimizationProblem.lagrangian,
    StandardPenaltyProblem.toLp_of_euclideanEquiv]

/-- The first-order pairing in the Chapter 10 mixed-constraint surface is the Chapter 8
linearized-constraint pairing transported to `Point = ℝⁿ`. -/
noncomputable abbrev linearizedConstraintPairing
    (problem : StandardPenaltyProblem n m) (xStar d : Point) (i : Fin m) : ℝ :=
  problem.toConstrainedOptimizationProblem.linearizedConstraintPairing xStar.ofLp d.ofLp i

/-- `problem.linearizedConstraintPairing xStar d i` is the Chapter 10 transport of the Chapter 8
canonical first-order pairing. -/
@[simp] theorem linearizedConstraintPairing_eq
    (problem : StandardPenaltyProblem n m) (xStar d : Point) (i : Fin m) :
    problem.linearizedConstraintPairing xStar d i =
      problem.toConstrainedOptimizationProblem.linearizedConstraintPairing
        xStar.ofLp d.ofLp i :=
  rfl

/-- The set `LFD(xStar, X)` of Chapter 10 linearized feasible directions at `xStar`, expressed as
the Chapter 8 linearized feasible-direction owner on the mixed-constraint bridge. -/
def linearizedFeasibleDirectionSet
    (problem : StandardPenaltyProblem n m) (xStar : Point) : Set Point :=
  {d | d.ofLp ∈ problem.toConstrainedOptimizationProblem.linearizedFeasibleDirectionSet xStar.ofLp}

/-- Membership in `problem.linearizedFeasibleDirectionSet xStar` is exactly the mixed-constraint
linearized feasibility condition on the active constraints of `problem`. -/
@[simp] theorem mem_linearizedFeasibleDirectionSet_iff
    (problem : StandardPenaltyProblem n m) (xStar d : Point) :
    d ∈ problem.linearizedFeasibleDirectionSet xStar ↔
      xStar ∈ problem ∧
        problem.toConstrainedOptimizationProblem.HasActiveConstraintGradientsAt xStar.ofLp ∧
        (∀ i : Fin m, i.1 < problem.eqCount →
          problem.linearizedConstraintPairing xStar d i = 0) ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 → problem.constraint i xStar = 0 →
          0 ≤ problem.linearizedConstraintPairing xStar d i := by
  constructor
  · intro hd
    rcases
      (problem.toConstrainedOptimizationProblem.mem_linearizedFeasibleDirectionSet_iff_explicit
        xStar.ofLp d.ofLp).1 hd with
      ⟨hx, hdiff, heq, hineq⟩
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff xStar).1 hx, hdiff, ?_, ?_⟩
    · intro i hi
      simpa [StandardPenaltyProblem.linearizedConstraintPairing] using heq i hi
    · intro i hi hactive
      have hi_active :
          i ∈ problem.toConstrainedOptimizationProblem.activeIneqIndexSet xStar.ofLp := by
        simpa using ⟨hi, hactive⟩
      simpa [StandardPenaltyProblem.linearizedConstraintPairing] using hineq i hi_active
  · rintro ⟨hx, hdiff, heq, hineq⟩
    refine
      (problem.toConstrainedOptimizationProblem.mem_linearizedFeasibleDirectionSet_iff_explicit
        xStar.ofLp d.ofLp).2 ?_
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff xStar).2 hx, hdiff, ?_, ?_⟩
    · intro i hi
      simpa [StandardPenaltyProblem.linearizedConstraintPairing] using heq i hi
    · intro i hi
      have hi' :=
        (problem.mem_activeIneqIndexSet_toConstrainedOptimizationProblem_iff xStar i).1 hi
      have hactive : problem.constraint i xStar = 0 := hi'.2
      simpa [StandardPenaltyProblem.linearizedConstraintPairing] using hineq i hi'.1 hactive

/-- A multiplier vector `lamStar` is a Chapter 10 Lagrange multiplier at `xStar` when the
canonical Chapter 8 KKT owner holds for the mixed-constraint bridge and the Chapter 10 Euclidean
Lagrangian is differentiable at `xStar`. -/
class IsLagrangeMultiplier
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint) :
    Prop where
  toIsKKTPoint :
    problem.toConstrainedOptimizationProblem.IsKKTPoint xStar.ofLp lamStar.ofLp
  lagrangianDifferentiableAt :
    DifferentiableAt ℝ (fun x : Point ↦ problem.lagrangian x lamStar) xStar

/-- Unfolding `problem.IsLagrangeMultiplier xStar lamStar` gives the mixed-constraint KKT data
together with differentiability of the Euclidean Lagrangian. -/
theorem isLagrangeMultiplier_iff
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint) :
    problem.IsLagrangeMultiplier xStar lamStar ↔
      xStar ∈ problem ∧
        (∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ lamStar i) ∧
        DifferentiableAt ℝ (fun x : Point ↦ problem.lagrangian x lamStar) xStar ∧
        ∇ (fun x : Point ↦ problem.lagrangian x lamStar) xStar = 0 ∧
        ∀ i : Fin m, problem.eqCount ≤ i.1 → lamStar i * problem.constraint i xStar = 0 := by
  constructor
  · intro h
    refine ⟨(problem.mem_toConstrainedOptimizationProblem_iff xStar).1 h.toIsKKTPoint.feasible,
      ?_, h.lagrangianDifferentiableAt, ?_, ?_⟩
    · intro i hi
      simpa using h.toIsKKTPoint.dualFeasible i hi
    · simpa [problem.euclideanLagrangian_eq_lagrangian lamStar] using
        h.toIsKKTPoint.stationarity
    · intro i hi
      simpa [toConstrainedOptimizationProblem] using
        h.toIsKKTPoint.complementarySlackness i hi
  · rintro ⟨h_feasible, h_dualFeasible, h_diff, h_stationary, h_slack⟩
    refine ⟨?_, h_diff⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (problem.mem_toConstrainedOptimizationProblem_iff xStar).2 h_feasible
    · intro i hi
      exact h_dualFeasible i hi
    · simpa [problem.euclideanLagrangian_eq_lagrangian lamStar] using h_stationary
    · intro i hi
      exact h_slack i hi

/-- A Chapter 10 Lagrange multiplier is feasible for `problem`. -/
theorem IsLagrangeMultiplier.feasible
    {problem : StandardPenaltyProblem n m} {xStar : Point} {lamStar : ConstraintPoint}
    (h : problem.IsLagrangeMultiplier xStar lamStar) :
    xStar ∈ problem :=
  (problem.mem_toConstrainedOptimizationProblem_iff xStar).1 h.toIsKKTPoint.feasible

/-- A Chapter 10 Lagrange multiplier is dual-feasible on the inequality block of `problem`. -/
theorem IsLagrangeMultiplier.dualFeasible
    {problem : StandardPenaltyProblem n m} {xStar : Point} {lamStar : ConstraintPoint}
    (h : problem.IsLagrangeMultiplier xStar lamStar) :
    ∀ i : Fin m, problem.eqCount ≤ i.1 → 0 ≤ lamStar i := by
  intro i hi
  simpa [ineqIndices] using h.toIsKKTPoint.dualFeasible i hi

/-- A Chapter 10 Lagrange multiplier is stationary for the mixed-constraint Euclidean
Lagrangian. -/
theorem IsLagrangeMultiplier.stationarity
    {problem : StandardPenaltyProblem n m} {xStar : Point} {lamStar : ConstraintPoint}
    (h : problem.IsLagrangeMultiplier xStar lamStar) :
    ∇ (fun x : Point ↦ problem.lagrangian x lamStar) xStar = 0 := by
  simpa [problem.euclideanLagrangian_eq_lagrangian lamStar] using h.toIsKKTPoint.stationarity

/-- A Chapter 10 Lagrange multiplier satisfies complementary slackness on the inequality block
of `problem`. -/
theorem IsLagrangeMultiplier.complementarySlackness
    {problem : StandardPenaltyProblem n m} {xStar : Point} {lamStar : ConstraintPoint}
    (h : problem.IsLagrangeMultiplier xStar lamStar) :
    ∀ i : Fin m, problem.eqCount ≤ i.1 → lamStar i * problem.constraint i xStar = 0 := by
  intro i hi
  simpa [toConstrainedOptimizationProblem] using h.toIsKKTPoint.complementarySlackness i hi

/-- The quadratic form `dᵀ ∇²_xx L(xStar, lamStar) d` is the Chapter 10 transport of the Chapter
8 Lagrangian Hessian quadratic form on the mixed-constraint bridge. -/
noncomputable abbrev lagrangianHessianQuadratic
    (problem : StandardPenaltyProblem n m)
    (xStar : Point) (lamStar : ConstraintPoint) (d : Point) : ℝ :=
  problem.toConstrainedOptimizationProblem.lagrangianHessianQuadratic
    xStar.ofLp lamStar.ofLp d.ofLp

/-- `problem.lagrangianHessianQuadratic xStar lamStar d` is exactly the Chapter 8 canonical
Hessian quadratic form of the mixed-constraint bridge. -/
theorem lagrangianHessianQuadratic_eq
    (problem : StandardPenaltyProblem n m)
    (xStar : Point) (lamStar : ConstraintPoint) (d : Point) :
    problem.lagrangianHessianQuadratic xStar lamStar d =
      problem.toConstrainedOptimizationProblem.lagrangianHessianQuadratic
        xStar.ofLp lamStar.ofLp d.ofLp :=
  rfl

/-- `problem.SecondOrderSufficientCondition xStar lamStar` packages the Chapter 10 second-order
sufficient condition: `lamStar` is a corresponding Lagrange multiplier at `xStar`, the objective
and constraints are `C²` at `xStar`, and the Lagrangian Hessian quadratic form is strictly
positive on every nonzero direction in `problem.linearizedFeasibleDirectionSet xStar`. -/
@[mk_iff secondOrderSufficientCondition_iff]
class SecondOrderSufficientCondition
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint) : Prop where
  isLagrangeMultiplier : problem.IsLagrangeMultiplier xStar lamStar
  objective_contDiffAt : ContDiffAt ℝ 2 problem.objective xStar
  constraint_contDiffAt : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar
  lagrangianHessianQuadratic_pos :
    ∀ d ∈ problem.linearizedFeasibleDirectionSet xStar,
      d ≠ 0 → 0 < problem.lagrangianHessianQuadratic xStar lamStar d

end StandardPenaltyProblem

/-- Helper for Chapter10 Theorem 10.6.1: negating unconstrained strict local minimality produces
a sequence of distinct nearby points whose values do not exceed the base value. -/
lemma exists_counterexample_sequence_of_not_isStrictLocalMin
    {F : Point → ℝ} {xStar : Point}
    (h_not : ¬ IsStrictLocalMin F xStar) :
    ∃ xSeq : ℕ → Point,
      ∀ k,
        xSeq k ≠ xStar ∧
          ‖xSeq k - xStar‖ ≤ 1 / ((k : ℝ) + 1) ∧
          F (xSeq k) ≤ F xStar := by
  have h_no_ball :
      ¬ ∃ δ > 0, ∀ x : Point, x ≠ xStar → ‖x - xStar‖ < δ → F xStar < F x := by
    intro h_ball
    exact h_not ((isStrictLocalMin_iff_exists_forall_norm_sub_lt F xStar).2 h_ball)
  push Not at h_no_ball
  have h_choose :
      ∀ k : ℕ,
        ∃ x : Point,
          x ≠ xStar ∧
            ‖x - xStar‖ < 1 / ((k : ℝ) + 1) ∧
            F x ≤ F xStar := by
    intro k
    have hk_pos : 0 < 1 / ((k : ℝ) + 1) := by
      positivity
    simpa [not_lt] using h_no_ball (1 / ((k : ℝ) + 1)) hk_pos
  choose xSeq hxSeq using h_choose
  refine ⟨xSeq, ?_⟩
  intro k
  rcases hxSeq k with ⟨hx_ne, hx_dist, hx_le⟩
  exact ⟨hx_ne, le_of_lt hx_dist, hx_le⟩

/-- Helper for Chapter10 Theorem 10.6.1: the multiplier-weighted constraint correction vanishes
at a mixed-constraint Lagrange multiplier point. -/
lemma weighted_constraint_sum_eq_zero_of_isLagrangeMultiplier
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint)
    (h_multiplier : problem.IsLagrangeMultiplier xStar lamStar) :
    ∑ i : Fin m, lamStar i * problem.constraint i xStar = 0 := by
  -- Feasibility handles the equality block, and complementary slackness handles the inequality
  -- block.
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hi : i.1 < problem.eqCount
  · have hx_eq :
        problem.constraint i xStar = 0 := by
      exact (problem.mem_feasibleSet_iff xStar).1 h_multiplier.feasible |>.1 i hi
    simp [hx_eq]
  · have hi_ineq : problem.eqCount ≤ i.1 := Nat.le_of_not_lt hi
    exact h_multiplier.complementarySlackness i hi_ineq

/-- Helper for Chapter10 Theorem 10.6.1: at a mixed-constraint Lagrange multiplier point, the
Chapter 10 Lagrangian value agrees with the objective value. -/
lemma lagrangian_eq_objective_of_isLagrangeMultiplier
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint)
    (h_multiplier : problem.IsLagrangeMultiplier xStar lamStar) :
    problem.lagrangian xStar lamStar = problem.objective xStar := by
  -- The multiplier-weighted constraint sum vanishes at the base point.
  rw [problem.lagrangian_eq,
    weighted_constraint_sum_eq_zero_of_isLagrangeMultiplier problem xStar lamStar h_multiplier,
    sub_zero]

/-- Helper for Chapter10 Theorem 10.6.1: each penalty comparison point satisfies the source
multiplier-versus-violation inequality
`-‖λ*‖∞ ‖c⁽-⁾(x)‖₁ ≤ ∑ᵢ λᵢ* cᵢ(x)`. -/
lemma multiplier_constraint_sum_ge_neg_linfty_mul_constraintViolation_l1
    (problem : StandardPenaltyProblem n m) (xStar x : Point) (lamStar : ConstraintPoint)
    (h_multiplier : problem.IsLagrangeMultiplier xStar lamStar) :
    -‖lamStar‖∞ * ‖c⁽-⁾[problem] x‖₁ ≤ ∑ i : Fin m, lamStar i * problem.constraint i x := by
  have hcoord_bound :
      ∀ i : Fin m, |lamStar i| ≤ ‖lamStar‖∞ := by
    intro i
    simpa [EuclideanSpace.linftyNorm_eq, linftyNorm, lpNorm] using
      (PiLp.norm_apply_le (x := WithLp.toLp (⊤ : ENNReal) lamStar.ofLp) i)
  have hcoord :
      ∀ i : Fin m,
        -‖lamStar‖∞ * |(c⁽-⁾[problem] x) i| ≤ lamStar i * problem.constraint i x := by
    intro i
    by_cases hi : i.1 < problem.eqCount
    · have hlam_left : -‖lamStar‖∞ ≤ lamStar i := (abs_le.mp (hcoord_bound i)).1
      have hlam_right : lamStar i ≤ ‖lamStar‖∞ := (abs_le.mp (hcoord_bound i)).2
      have hviolation :
          (c⁽-⁾[problem] x) i = problem.constraint i x := by
        simp [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi]
      by_cases hci : 0 ≤ problem.constraint i x
      · rw [hviolation, abs_of_nonneg hci]
        nlinarith
      · have hci' : problem.constraint i x ≤ 0 := le_of_not_ge hci
        rw [hviolation, abs_of_nonpos hci']
        nlinarith
    · have hi_ineq : problem.eqCount ≤ i.1 := Nat.le_of_not_lt hi
      have hlam_nonneg : 0 ≤ lamStar i := h_multiplier.dualFeasible i hi_ineq
      have hlam_right : lamStar i ≤ ‖lamStar‖∞ := by
        exact (abs_le.mp (hcoord_bound i)).2
      have hviolation :
          (c⁽-⁾[problem] x) i = min (problem.constraint i x) 0 := by
        simp [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi]
      by_cases hci : problem.constraint i x ≤ 0
      · rw [hviolation, min_eq_left hci, abs_of_nonpos hci]
        nlinarith
      · have hci_nonneg : 0 ≤ problem.constraint i x := le_of_not_ge hci
        rw [hviolation, min_eq_right hci_nonneg, abs_zero]
        nlinarith
  -- Sum the coordinatewise bounds and rewrite the `ℓ₁` norm as a finite sum of absolute values.
  calc
    -‖lamStar‖∞ * ‖c⁽-⁾[problem] x‖₁ =
        ∑ i : Fin m, -‖lamStar‖∞ * |(c⁽-⁾[problem] x) i| := by
          rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs, Finset.mul_sum]
    _ ≤ ∑ i : Fin m, lamStar i * problem.constraint i x := by
      exact Finset.sum_le_sum fun i _ ↦ hcoord i

/-- Helper for Chapter10 Theorem 10.6.1: after rewriting the penalty comparison at a bad point,
the Lagrangian gap plus the positive violation coefficient is nonpositive. The helper statement
includes the necessary `σ ≥ 0` hypothesis so the `ℓ₁` lower bound can be scaled correctly. -/
lemma penalty_le_at_base_implies_lagrangian_gap_plus_violation_le_zero
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint)
    (σ δ : ℝ) (h : ConstraintPoint → ℝ) [IsStrongDistanceFunction h]
    (h_multiplier : problem.IsLagrangeMultiplier xStar lamStar)
    (hσ_nonneg : 0 ≤ σ)
    (h_lower_l1 : ∀ c : ConstraintPoint, δ * ‖c‖₁ ≤ h c)
    {x : Point}
    (hx : problem.nonsmoothExactPenalty h σ x ≤ problem.nonsmoothExactPenalty h σ xStar) :
    problem.lagrangian x lamStar - problem.lagrangian xStar lamStar +
      (σ * δ - ‖lamStar‖∞) * ‖c⁽-⁾[problem] x‖₁ ≤ 0 := by
  have hxStar_feasible : xStar ∈ problem := h_multiplier.feasible
  have hPenaltyStar :
      problem.nonsmoothExactPenalty h σ xStar = problem.objective xStar := by
    -- Feasibility makes the penalty term vanish at the base point.
    have hzero : c⁽-⁾[problem] xStar = 0 :=
      (problem.mem_iff_constraintViolation_eq_zero xStar).1 hxStar_feasible
    rw [problem.nonsmoothExactPenalty_apply, hzero]
    simp [IsStrongDistanceFunction.apply_zero h]
  have hPenaltyGap :
      problem.objective x + σ * h (c⁽-⁾[problem] x) ≤ problem.objective xStar := by
    rw [problem.nonsmoothExactPenalty_apply, hPenaltyStar] at hx
    exact hx
  have hScaledLower :
      σ * δ * ‖c⁽-⁾[problem] x‖₁ ≤ σ * h (c⁽-⁾[problem] x) := by
    -- Scale the global `ℓ₁` lower bound by the nonnegative penalty parameter.
    have hbase := h_lower_l1 (c⁽-⁾[problem] x)
    have hmul :
        σ * (δ * ‖c⁽-⁾[problem] x‖₁) ≤ σ * h (c⁽-⁾[problem] x) :=
      mul_le_mul_of_nonneg_left hbase hσ_nonneg
    simpa [mul_assoc] using hmul
  have hPenaltyCore :
      problem.objective x - problem.objective xStar +
        σ * δ * ‖c⁽-⁾[problem] x‖₁ ≤ 0 := by
    nlinarith
  have hMultiplierCore :
      -‖lamStar‖∞ * ‖c⁽-⁾[problem] x‖₁ ≤ ∑ i : Fin m, lamStar i * problem.constraint i x :=
    multiplier_constraint_sum_ge_neg_linfty_mul_constraintViolation_l1
      problem xStar x lamStar h_multiplier
  have hCombined :
      problem.objective x - ∑ i : Fin m, lamStar i * problem.constraint i x -
          problem.objective xStar +
          (σ * δ - ‖lamStar‖∞) * ‖c⁽-⁾[problem] x‖₁ ≤ 0 := by
    nlinarith
  -- Rewrite the Lagrangian values and collapse the base-point correction term.
  rw [problem.lagrangian_eq,
    lagrangian_eq_objective_of_isLagrangeMultiplier problem xStar lamStar h_multiplier]
  exact hCombined

/-- Helper for Chapter10 Theorem 10.6.1: the `C²` objective/constraint data on the Chapter 10
surface transports directly to the canonical Chapter 8 constrained-problem bridge. -/
lemma toConstrainedOptimizationProblem_contDiffAt_data
    (problem : StandardPenaltyProblem n m) (xStar : Point)
    (h_obj : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constr : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar) :
    ContDiffAt ℝ 2 problem.toConstrainedOptimizationProblem.objective xStar.ofLp ∧
      ∀ i, ContDiffAt ℝ 2 (problem.toConstrainedOptimizationProblem.constraint i) xStar.ofLp := by
  have h_toLp : ContDiffAt ℝ 2 (WithLp.toLp 2 : (Fin n → ℝ) → Point) xStar.ofLp :=
    PiLp.contDiff_toLp.contDiffAt
  constructor
  · -- The bridge objective is the source objective precomposed with the linear `toLp` map.
    change ContDiffAt ℝ 2 (problem.objective ∘ WithLp.toLp 2) xStar.ofLp
    simpa [Function.comp] using h_obj.comp xStar.ofLp h_toLp
  · intro i
    -- Each bridge constraint is the corresponding source constraint precomposed with `toLp`.
    change ContDiffAt ℝ 2 (problem.constraint i ∘ WithLp.toLp 2) xStar.ofLp
    simpa [Function.comp] using (h_constr i).comp xStar.ofLp h_toLp

/-- Helper for Chapter10 Theorem 10.6.1: along a sequence of nonzero points converging to
`xStar`, if the normalized displacements converge to `d`, then the first-order quotient of a
differentiable scalar field converges to the directional derivative at `d`. -/
lemma tendsto_div_norm_sub_of_differentiableAt
    {f : Point → ℝ} {xSeq : ℕ → Point} {xStar d : Point}
    (h_diff : DifferentiableAt ℝ f xStar)
    (_hxSeq_ne : ∀ k, xSeq k ≠ xStar)
    (hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar))
    (hd_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) atTop (nhds d)) :
    Tendsto (fun k ↦ (f (xSeq k) - f xStar) / ‖xSeq k - xStar‖)
      atTop (nhds (fderiv ℝ f xStar d)) := by
  let f' := fderiv ℝ f xStar
  have hfd : HasFDerivAt f f' xStar := h_diff.hasFDerivAt
  have hrem :
      Tendsto
        (fun k ↦ ‖xSeq k - xStar‖⁻¹ * ‖f (xSeq k) - f xStar - f' (xSeq k - xStar)‖)
        atTop (nhds 0) := by
    -- The Fréchet remainder is `o (‖x - xStar‖)` along the convergent sequence.
    exact (hasFDerivAt_iff_tendsto.mp hfd).comp hxSeq_tendsto
  have hlin :
      Tendsto (fun k ↦ f' (‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar))) atTop (nhds (f' d)) := by
    -- The derivative term follows from continuity of the fixed linear map `f'`.
    exact f'.continuous.tendsto d |>.comp hd_tendsto
  have hdiffquot :
      Tendsto
        (fun k ↦
          (f (xSeq k) - f xStar) / ‖xSeq k - xStar‖ -
            f' (‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)))
        atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine Tendsto.congr' ?_ hrem
    filter_upwards with k
    have hEq :
        (f (xSeq k) - f xStar) / ‖xSeq k - xStar‖ -
            f' (‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) =
          ‖xSeq k - xStar‖⁻¹ * (f (xSeq k) - f xStar - f' (xSeq k - xStar)) := by
      -- Route correction: isolate the scalar quotient algebra before taking norms.
      rw [div_eq_inv_mul, map_smul]
      ring
    rw [show
      ‖(f (xSeq k) - f xStar) / ‖xSeq k - xStar‖ -
          f' (‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) -
          0‖ =
        ‖(f (xSeq k) - f xStar) / ‖xSeq k - xStar‖ -
            f' (‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar))‖ by
      simp]
    rw [hEq, norm_mul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
  have hsum := hdiffquot.add hlin
  -- Add the vanishing remainder to the derivative limit to recover the original quotient.
  convert hsum using 1
  · ext k
    abel_nf
  · simp [f']

/-- Helper for Chapter10 Theorem 10.6.1: if the penalty comparison already yields
`L(x_k, λ*) - L(x*, λ*) + a ‖c⁽-⁾(x_k)‖₁ ≤ 0` with `a > 0`, then the source violation ratio
`‖c⁽-⁾(x_k)‖₁ / ‖x_k - x*‖` tends to `0`. -/
lemma constraintViolation_ratio_tendsto_zero_of_penalty_upper
    (problem : StandardPenaltyProblem n m) (xStar d : Point) (lamStar : ConstraintPoint)
    (a : ℝ) (ha : 0 < a)
    (h_multiplier : problem.IsLagrangeMultiplier xStar lamStar)
    {xSeq : ℕ → Point}
    (hxSeq_ne : ∀ k, xSeq k ≠ xStar)
    (hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar))
    (hd_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) atTop (nhds d))
    (h_upper :
      ∀ k,
        problem.lagrangian (xSeq k) lamStar - problem.lagrangian xStar lamStar +
          a * ‖c⁽-⁾[problem] (xSeq k)‖₁ ≤ 0) :
    Tendsto (fun k ↦ ‖c⁽-⁾[problem] (xSeq k)‖₁ / ‖xSeq k - xStar‖) atTop (nhds 0) := by
  let gap : ℕ → ℝ := fun k ↦
    (problem.lagrangian (xSeq k) lamStar - problem.lagrangian xStar lamStar) /
      ‖xSeq k - xStar‖
  let ratio : ℕ → ℝ := fun k ↦ ‖c⁽-⁾[problem] (xSeq k)‖₁ / ‖xSeq k - xStar‖
  have hgap_tendsto : Tendsto gap atTop (nhds 0) := by
    have hquot :=
      tendsto_div_norm_sub_of_differentiableAt
        h_multiplier.lagrangianDifferentiableAt hxSeq_ne hxSeq_tendsto hd_tendsto
    have hderiv_zero :
        fderiv ℝ (fun x : Point ↦ problem.lagrangian x lamStar) xStar d = 0 := by
      -- Stationarity kills the first-order Lagrangian term in the source quotient.
      simpa [h_multiplier.stationarity] using
        (inner_gradient_left (𝕜 := ℝ)
          (f := fun x : Point ↦ problem.lagrangian x lamStar) (x := xStar) (y := d)).symm
    simpa [gap, hderiv_zero] using hquot
  have hscaled_tendsto : Tendsto (fun k ↦ a * ratio k) atTop (nhds 0) := by
    have habs_gap_tendsto : Tendsto (fun k ↦ |gap k|) atTop (nhds 0) := by
      have hcomp :
          Tendsto (abs ∘ gap) atTop (nhds (abs 0)) :=
        continuous_abs.continuousAt.tendsto.comp hgap_tendsto
      convert hcomp using 1
      · ext k
        rfl
      · simp
    refine squeeze_zero_norm ?_ habs_gap_tendsto
    intro k
    have hden_pos : 0 < ‖xSeq k - xStar‖ := by
      refine norm_pos_iff.2 ?_
      exact sub_ne_zero.2 (hxSeq_ne k)
    have hratio_nonneg : 0 ≤ ratio k := by
      exact div_nonneg (norm_nonneg _) hden_pos.le
    have hscaled_nonneg : 0 ≤ a * ratio k := mul_nonneg ha.le hratio_nonneg
    have hraw := mul_le_mul_of_nonneg_right (h_upper k) (inv_nonneg.2 hden_pos.le)
    have hdiv : gap k + a * ratio k ≤ 0 := by
      -- Divide the source penalty inequality by the positive step length.
      simpa [gap, ratio, div_eq_mul_inv, add_mul, mul_assoc, mul_left_comm, mul_comm] using hraw
    have hgap_nonpos : gap k ≤ 0 := by
      linarith
    have habs_left : ‖a * ratio k‖ ≤ |gap k| := by
      rw [Real.norm_eq_abs, abs_of_nonneg hscaled_nonneg, abs_of_nonpos hgap_nonpos]
      linarith
    simpa [Real.norm_eq_abs] using habs_left
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hconst_mul :
      Tendsto (fun k ↦ a⁻¹ * (a * ratio k)) atTop (nhds (a⁻¹ * 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ a⁻¹) atTop (nhds a⁻¹)).mul hscaled_tendsto
  -- Cancel the fixed positive coefficient `a` to recover the raw violation ratio.
  simpa [ratio, div_eq_mul_inv, ha_ne, mul_assoc, mul_left_comm, mul_comm] using hconst_mul

/-- Helper for Chapter10 Theorem 10.6.1: the Chapter 10 linearized constraint pairing is exactly
the Fréchet derivative of the original constraint evaluated on Euclidean directions. -/
lemma linearizedConstraintPairing_eq_fderiv_constraint
    (problem : StandardPenaltyProblem n m) (xStar d : Point) (i : Fin m) :
    problem.linearizedConstraintPairing xStar d i =
      fderiv ℝ (problem.constraint i) xStar d := by
  -- The mixed-constraint bridge pairing reduces to the original Euclidean constraint derivative.
  have h_euclideanConstraint :
      problem.toConstrainedOptimizationProblem.euclideanConstraint i = problem.constraint i := by
    funext x
    simp [ConstrainedOptimizationProblem.euclideanConstraint, Function.comp,
      StandardPenaltyProblem.toConstrainedOptimizationProblem]
  calc
    problem.linearizedConstraintPairing xStar d i =
        fderiv ℝ (problem.toConstrainedOptimizationProblem.euclideanConstraint i) xStar d := by
          simpa [StandardPenaltyProblem.linearizedConstraintPairing] using
            problem.toConstrainedOptimizationProblem.linearizedConstraintPairing_eq_euclideanConstraint
              xStar.ofLp d.ofLp i
    _ = fderiv ℝ (problem.constraint i) xStar d := by rw [h_euclideanConstraint]

/-- Helper for Chapter10 Theorem 10.6.1: if the normalized `ℓ₁` violation tends to `0`, then
each fixed violation coordinate divided by the step length also tends to `0`. -/
lemma constraintViolation_coordinate_ratio_tendsto_zero_of_l1
    (problem : StandardPenaltyProblem n m) (xStar : Point) {xSeq : ℕ → Point} (i : Fin m)
    (hxSeq_ne : ∀ k, xSeq k ≠ xStar)
    (h_ratio :
      Tendsto (fun k ↦ ‖c⁽-⁾[problem] (xSeq k)‖₁ / ‖xSeq k - xStar‖) atTop (nhds 0)) :
    Tendsto (fun k ↦ ((c⁽-⁾[problem] (xSeq k)) i) / ‖xSeq k - xStar‖) atTop (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm ?_ h_ratio
  intro k
  have hden_pos : 0 < ‖xSeq k - xStar‖ := by
    refine norm_pos_iff.2 ?_
    exact sub_ne_zero.2 (hxSeq_ne k)
  have hcoord_le :
      |(c⁽-⁾[problem] (xSeq k)) i| ≤ ‖c⁽-⁾[problem] (xSeq k)‖₁ := by
    -- Route correction: replace the stalled norm bookkeeping by the direct coordinate-vs-`ℓ₁`
    -- estimate on the finite sum formula for `‖·‖₁`.
    rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ abs_nonneg ((c⁽-⁾[problem] (xSeq k)) j))
        (Finset.mem_univ i) :
        |(c⁽-⁾[problem] (xSeq k)) i| ≤ ∑ j : Fin m, |(c⁽-⁾[problem] (xSeq k)) j|)
  have hscaled :
      |(c⁽-⁾[problem] (xSeq k)) i| * ‖xSeq k - xStar‖⁻¹ ≤
        ‖c⁽-⁾[problem] (xSeq k)‖₁ * ‖xSeq k - xStar‖⁻¹ :=
    mul_le_mul_of_nonneg_right hcoord_le (inv_nonneg.2 hden_pos.le)
  -- Divide the coordinate bound by the positive step length.
  simpa [sub_zero, Real.norm_eq_abs, div_eq_mul_inv] using hscaled

/-- Helper for Chapter10 Theorem 10.6.1: on an equality coordinate, a vanishing normalized
violation forces the linearized constraint pairing to vanish. -/
lemma linearizedConstraintPairing_eq_zero_of_eq_constraintViolation_ratio_tendsto_zero
    (problem : StandardPenaltyProblem n m) (xStar d : Point) (i : Fin m)
    (hi : i.1 < problem.eqCount)
    (hxStar : xStar ∈ problem)
    (h_constraints : ∀ j, DifferentiableAt ℝ (problem.constraint j) xStar)
    {xSeq : ℕ → Point}
    (hxSeq_ne : ∀ k, xSeq k ≠ xStar)
    (hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar))
    (hd_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) atTop (nhds d))
    (h_coord :
      Tendsto (fun k ↦ ((c⁽-⁾[problem] (xSeq k)) i) / ‖xSeq k - xStar‖) atTop (nhds 0)) :
    problem.linearizedConstraintPairing xStar d i = 0 := by
  have hx_eq : problem.constraint i xStar = 0 :=
    (problem.mem_feasibleSet_iff xStar).1 hxStar |>.1 i hi
  have h_coord_constraint :
      Tendsto
        (fun k ↦ (problem.constraint i (xSeq k) - problem.constraint i xStar) /
          ‖xSeq k - xStar‖)
        atTop (nhds 0) := by
    -- On the equality block, the violation coordinate is the raw constraint value itself.
    have h_coord_eq :
        (fun k ↦ (problem.constraint i (xSeq k) - problem.constraint i xStar) /
          ‖xSeq k - xStar‖) =
          (fun k ↦ ((c⁽-⁾[problem] (xSeq k)) i) / ‖xSeq k - xStar‖) := by
      funext k
      simp [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi, hx_eq]
    simpa [h_coord_eq] using h_coord
  have h_quot :
      Tendsto
        (fun k ↦ (problem.constraint i (xSeq k) - problem.constraint i xStar) /
          ‖xSeq k - xStar‖)
        atTop (nhds (problem.linearizedConstraintPairing xStar d i)) := by
    -- The differentiability quotient limit identifies the equality pairing with that limit.
    rw [linearizedConstraintPairing_eq_fderiv_constraint]
    exact
      tendsto_div_norm_sub_of_differentiableAt
        (f := problem.constraint i) (xSeq := xSeq) (xStar := xStar) (d := d)
        (h_constraints i) hxSeq_ne hxSeq_tendsto hd_tendsto
  have h_unique : 0 = problem.linearizedConstraintPairing xStar d i :=
    tendsto_nhds_unique h_coord_constraint h_quot
  simpa using h_unique.symm

/-- Helper for Chapter10 Theorem 10.6.1: on an active inequality coordinate, a vanishing
normalized violation forces the linearized constraint pairing to be nonnegative. -/
lemma linearizedConstraintPairing_nonneg_of_active_constraintViolation_ratio_tendsto_zero
    (problem : StandardPenaltyProblem n m) (xStar d : Point) (i : Fin m)
    (hi : problem.eqCount ≤ i.1)
    (hactive : problem.constraint i xStar = 0)
    (h_constraints : ∀ j, DifferentiableAt ℝ (problem.constraint j) xStar)
    {xSeq : ℕ → Point}
    (hxSeq_ne : ∀ k, xSeq k ≠ xStar)
    (hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar))
    (hd_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) atTop (nhds d))
    (h_coord :
      Tendsto (fun k ↦ ((c⁽-⁾[problem] (xSeq k)) i) / ‖xSeq k - xStar‖) atTop (nhds 0)) :
    0 ≤ problem.linearizedConstraintPairing xStar d i := by
  have hi_not_lt : ¬ i.1 < problem.eqCount := Nat.not_lt_of_ge hi
  have h_quot :
      Tendsto
        (fun k ↦ (problem.constraint i (xSeq k) - problem.constraint i xStar) /
          ‖xSeq k - xStar‖)
        atTop (nhds (problem.linearizedConstraintPairing xStar d i)) := by
    -- The raw constraint quotient converges to the linearized pairing on the active branch too.
    rw [linearizedConstraintPairing_eq_fderiv_constraint]
    exact
      tendsto_div_norm_sub_of_differentiableAt
        (f := problem.constraint i) (xSeq := xSeq) (xStar := xStar) (d := d)
        (h_constraints i) hxSeq_ne hxSeq_tendsto hd_tendsto
  have h_min :
      Tendsto
        (fun k ↦ min
          ((problem.constraint i (xSeq k) - problem.constraint i xStar) /
            ‖xSeq k - xStar‖) 0)
        atTop (nhds (min (problem.linearizedConstraintPairing xStar d i) 0)) := by
    -- Apply continuity of `t ↦ min t 0` to the differentiability quotient limit.
    exact ((continuous_id.min continuous_const).continuousAt.tendsto).comp h_quot
  have h_coord_min :
      Tendsto
        (fun k ↦ min
          ((problem.constraint i (xSeq k) - problem.constraint i xStar) /
            ‖xSeq k - xStar‖) 0)
        atTop (nhds 0) := by
    -- The inequality violation is exactly the clipped quotient because the step lengths are
    -- positive and the active value at `xStar` is `0`.
    have h_coord_eq :
        (fun k ↦ min
          ((problem.constraint i (xSeq k) - problem.constraint i xStar) /
            ‖xSeq k - xStar‖) 0) =
          (fun k ↦ ((c⁽-⁾[problem] (xSeq k)) i) / ‖xSeq k - xStar‖) := by
      funext k
      have hden_pos : 0 < ‖xSeq k - xStar‖ := by
        refine norm_pos_iff.2 ?_
        exact sub_ne_zero.2 (hxSeq_ne k)
      calc
        min
            ((problem.constraint i (xSeq k) - problem.constraint i xStar) /
              ‖xSeq k - xStar‖) 0
            = min (problem.constraint i (xSeq k) / ‖xSeq k - xStar‖)
                (0 / ‖xSeq k - xStar‖) := by
                  simp [hactive]
        _ = min (problem.constraint i (xSeq k)) 0 / ‖xSeq k - xStar‖ := by
              simpa using
                (min_div_div_right hden_pos.le (problem.constraint i (xSeq k)) 0)
        _ = ((c⁽-⁾[problem] (xSeq k)) i) / ‖xSeq k - xStar‖ := by
              simp [StandardPenaltyProblem.constraintViolation, PiLp.toLp_apply, hi_not_lt]
    simpa [h_coord_eq] using h_coord
  have h_min_eq_zero : min (problem.linearizedConstraintPairing xStar d i) 0 = 0 :=
    tendsto_nhds_unique h_min h_coord_min
  -- Reading off `min a 0 = 0` gives the required nonnegativity of the active pairing.
  by_cases hpair_nonpos : problem.linearizedConstraintPairing xStar d i ≤ 0
  · have hpair_zero : problem.linearizedConstraintPairing xStar d i = 0 := by
      rw [min_eq_left hpair_nonpos] at h_min_eq_zero
      exact h_min_eq_zero
    linarith
  · exact le_of_lt (lt_of_not_ge hpair_nonpos)

/-- Helper for Chapter10 Theorem 10.6.1: a sequence of distinct Euclidean points has a
subsequence of normalized displacements converging to a unit vector. -/
lemma existsTendstoNormalizedEuclideanDisplacementSubseq
    {xSeq : ℕ → Point} {xStar : Point} (h_ne : ∀ k, xSeq k ≠ xStar) :
    ∃ d : Point,
      d ∈ Metric.sphere (0 : Point) 1 ∧
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Tendsto
            (fun k ↦ ‖xSeq (φ k) - xStar‖⁻¹ • (xSeq (φ k) - xStar))
            atTop (nhds d) := by
  let u : ℕ → Point := fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)
  have hu_sphere : ∀ k, u k ∈ Metric.sphere (0 : Point) 1 := by
    intro k
    have hk_norm_ne : ‖xSeq k - xStar‖ ≠ 0 := by
      refine norm_ne_zero_iff.2 ?_
      exact sub_ne_zero.2 (h_ne k)
    -- Each normalized displacement has unit Euclidean norm, so it lies on the unit sphere.
    rw [Metric.mem_sphere, dist_eq_norm]
    simp only [sub_zero]
    dsimp [u]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    exact inv_mul_cancel₀ hk_norm_ne
  rcases (isCompact_sphere (0 : Point) 1).tendsto_subseq hu_sphere with ⟨d, hd, φ, hφ, hlim⟩
  exact ⟨d, hd, φ, hφ, hlim⟩

/-- Helper for Chapter10 Theorem 10.6.1: if the normalized violation ratio tends to `0` along a
normalized bad sequence, then the limiting direction lies in `LFD(xStar, X)`. -/
lemma mem_linearizedFeasibleDirectionSet_of_constraintViolation_ratio_tendsto_zero
    (problem : StandardPenaltyProblem n m) (xStar d : Point)
    (hxStar : xStar ∈ problem)
    (h_activeGrad :
      problem.toConstrainedOptimizationProblem.HasActiveConstraintGradientsAt xStar.ofLp)
    (h_constraints : ∀ i, DifferentiableAt ℝ (problem.constraint i) xStar)
    {xSeq : ℕ → Point}
    (hxSeq_ne : ∀ k, xSeq k ≠ xStar)
    (hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar))
    (hd_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) atTop (nhds d))
    (h_ratio :
      Tendsto (fun k ↦ ‖c⁽-⁾[problem] (xSeq k)‖₁ / ‖xSeq k - xStar‖) atTop (nhds 0)) :
    d ∈ problem.linearizedFeasibleDirectionSet xStar := by
  refine (problem.mem_linearizedFeasibleDirectionSet_iff xStar d).2 ?_
  refine ⟨hxStar, h_activeGrad, ?_, ?_⟩
  · intro i hi
    -- Equality coordinates inherit the zero directional pairing from the coordinatewise limit.
    exact
      linearizedConstraintPairing_eq_zero_of_eq_constraintViolation_ratio_tendsto_zero
        problem xStar d i hi hxStar h_constraints hxSeq_ne hxSeq_tendsto hd_tendsto
        (constraintViolation_coordinate_ratio_tendsto_zero_of_l1
          problem xStar i hxSeq_ne h_ratio)
  · intro i hi hactive
    -- Active inequality coordinates inherit nonnegative directional pairings from the clipped
    -- coordinate limit.
    exact
      linearizedConstraintPairing_nonneg_of_active_constraintViolation_ratio_tendsto_zero
        problem xStar d i hi hactive h_constraints hxSeq_ne hxSeq_tendsto hd_tendsto
        (constraintViolation_coordinate_ratio_tendsto_zero_of_l1
          problem xStar i hxSeq_ne h_ratio)

/-- Chapter10 Theorem 10.6.1: let `xStar` and the corresponding multiplier vector `lamStar`
satisfy the second-order sufficient condition on
`problem.linearizedFeasibleDirectionSet xStar`. If `h` is a strong distance function on
`ConstraintPoint`, if `δ` is a positive lower `ℓ₁` bound constant for `h`, and if
`σ * δ > ‖lamStar‖∞`, then `xStar` is a strict local minimizer of the nonsmooth exact
penalty function `problem.nonsmoothExactPenalty h σ`. The local-minimum assumption from the
prose is omitted because it is already implied by the second-order sufficient condition. -/
theorem isStrictLocalMin_nonsmoothExactPenalty_of_secondOrderSufficientCondition
    (problem : StandardPenaltyProblem n m) (xStar : Point) (lamStar : ConstraintPoint)
    (σ δ : ℝ) (h : ConstraintPoint → ℝ) [IsStrongDistanceFunction h]
    (h_sosc : problem.SecondOrderSufficientCondition xStar lamStar)
    (hδ : 0 < δ)
    (h_lower_l1 : ∀ c : ConstraintPoint, δ * ‖c‖₁ ≤ h c)
    (h_sigma : σ * δ > ‖lamStar‖∞) :
    IsStrictLocalMin (problem.nonsmoothExactPenalty h σ) xStar := by
  have h_multiplier : problem.IsLagrangeMultiplier xStar lamStar :=
    h_sosc.isLagrangeMultiplier
  have hσ_pos : 0 < σ := by
    have hlinfty_nonneg : 0 ≤ ‖lamStar‖∞ := norm_nonneg _
    nlinarith
  have hσ_nonneg : 0 ≤ σ := hσ_pos.le
  by_contra h_not
  rcases exists_counterexample_sequence_of_not_isStrictLocalMin h_not with ⟨xSeq, hxSeq⟩
  have hxSeq_ne : ∀ k, xSeq k ≠ xStar := fun k ↦ (hxSeq k).1
  have hxSeq_bound :
      ∀ k, ‖xSeq k - xStar‖ ≤ 1 / ((k : ℝ) + 1) := fun k ↦ (hxSeq k).2.1
  have hxSeq_penalty :
      ∀ k,
        problem.lagrangian (xSeq k) lamStar - problem.lagrangian xStar lamStar +
            (σ * δ - ‖lamStar‖∞) * ‖c⁽-⁾[problem] (xSeq k)‖₁ ≤ 0 := by
    intro k
    -- Every counterexample point satisfies the source penalty-vs-Lagrangian inequality.
    exact penalty_le_at_base_implies_lagrangian_gap_plus_violation_le_zero
      problem xStar lamStar σ δ h h_multiplier hσ_nonneg h_lower_l1 (hxSeq k).2.2
  have hxSeq_norm_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖) atTop (nhds (0 : ℝ)) := by
    -- The explicit radius bound forces the counterexample points back to `xStar`.
    refine squeeze_zero (fun k ↦ norm_nonneg _) hxSeq_bound tendsto_one_div_add_atTop_nhds_zero_nat
  have hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hxSeq_norm_tendsto
  rcases existsTendstoNormalizedEuclideanDisplacementSubseq hxSeq_ne with
    ⟨d, hd_sphere, φ, hφ, hd_tendsto⟩
  have hsubseq_tendsto : Tendsto (xSeq ∘ φ) atTop (nhds xStar) :=
    hxSeq_tendsto.comp hφ.tendsto_atTop
  have ha : 0 < σ * δ - ‖lamStar‖∞ := by
    linarith
  have h_ratio_subseq :
      Tendsto
        (fun k ↦ ‖c⁽-⁾[problem] (xSeq (φ k))‖₁ / ‖xSeq (φ k) - xStar‖)
        atTop (nhds 0) := by
    -- The bad penalty comparison drives the normalized violation ratio to `0` on the chosen
    -- subsequence.
    exact
      constraintViolation_ratio_tendsto_zero_of_penalty_upper
        problem xStar d lamStar (σ * δ - ‖lamStar‖∞) ha h_multiplier
        (fun k ↦ hxSeq_ne (φ k)) hsubseq_tendsto hd_tendsto (fun k ↦ hxSeq_penalty (φ k))
  have h_bridge_data :
      ContDiffAt ℝ 2 problem.toConstrainedOptimizationProblem.objective xStar.ofLp ∧
        ∀ i,
          ContDiffAt ℝ 2 (problem.toConstrainedOptimizationProblem.constraint i) xStar.ofLp := by
    -- Transport the Chapter 10 `C²` data to the Chapter 8 constrained-problem owner once.
    exact
      toConstrainedOptimizationProblem_contDiffAt_data
        problem xStar h_sosc.objective_contDiffAt h_sosc.constraint_contDiffAt
  have h_bridge_constraints :
      problem.toConstrainedOptimizationProblem.HasConstraintGradientsAt xStar.ofLp := by
    intro i
    exact (h_bridge_data.2 i).differentiableAt (by norm_num)
  have h_source_constraints : ∀ i, DifferentiableAt ℝ (problem.constraint i) xStar := by
    intro i
    exact (h_sosc.constraint_contDiffAt i).differentiableAt (by norm_num)
  have hd_linearized :
      d ∈ problem.linearizedFeasibleDirectionSet xStar := by
    -- Route correction: the source `(10.6.9) -> (10.6.10)` step is the dedicated Chapter 10
    -- bridge from the vanishing normalized violation ratio to linearized feasibility.
    exact
      mem_linearizedFeasibleDirectionSet_of_constraintViolation_ratio_tendsto_zero
        problem xStar d h_multiplier.feasible
        h_bridge_constraints.hasActiveConstraintGradientsAt h_source_constraints
        (fun k ↦ hxSeq_ne (φ k)) hsubseq_tendsto hd_tendsto h_ratio_subseq
  have hd_nonzero : d ≠ 0 := by
    -- A limit point on the unit sphere cannot vanish.
    have hd_norm : ‖d‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_sphere
    intro hd_zero
    simp [hd_zero] at hd_norm
  let delta : ℕ → ℝ := fun k ↦ ‖xSeq (φ k) - xStar‖
  let dSeq : ℕ → Point := fun k ↦ (delta k)⁻¹ • (xSeq (φ k) - xStar)
  let dSeqBridge : ℕ → Fin n → ℝ := fun k ↦ (dSeq k).ofLp
  have h_delta_pos : ∀ k, 0 < delta k := by
    intro k
    dsimp [delta]
    exact norm_pos_iff.2 (sub_ne_zero.2 (hxSeq_ne (φ k)))
  have hdSeq_tendsto : Tendsto dSeq atTop (nhds d) := by
    simpa [dSeq, delta] using hd_tendsto
  have hdSeqBridge_tendsto :
      Tendsto dSeqBridge atTop (nhds d.ofLp) := by
    -- The point-space trace directions are just the Euclidean ones viewed through `ofLp`.
    change Tendsto (WithLp.ofLp ∘ dSeq) atTop (nhds d.ofLp)
    exact ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n ↦ ℝ)).tendsto d).comp hdSeq_tendsto
  have hdelta_tendsto : Tendsto delta atTop (nhds (0 : ℝ)) := by
    change Tendsto ((fun k ↦ ‖xSeq k - xStar‖) ∘ φ) atTop (nhds (0 : ℝ))
    exact hxSeq_norm_tendsto.comp hφ.tendsto_atTop
  have htrace_eq : ∀ k, xStar + delta k • dSeq k = xSeq (φ k) := by
    intro k
    have hk_ne : delta k ≠ 0 := ne_of_gt (h_delta_pos k)
    dsimp [delta, dSeq]
    rw [smul_smul, mul_inv_cancel₀ hk_ne, one_smul]
    simp [sub_eq_add_neg]
  have h_upper :
      ∀ k,
        problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp
            (WithLp.toLp 2 (xStar.ofLp + delta k • dSeqBridge k)) ≤
          problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp
            (WithLp.toLp 2 xStar.ofLp) := by
    intro k
    have hgap :
        problem.lagrangian (xSeq (φ k)) lamStar ≤ problem.lagrangian xStar lamStar := by
      have hviolation_nonneg :
          0 ≤ (σ * δ - ‖lamStar‖∞) * ‖c⁽-⁾[problem] (xSeq (φ k))‖₁ := by
        exact mul_nonneg ha.le (norm_nonneg _)
      linarith [hxSeq_penalty (φ k)]
    have hlagrangian_eq :
        ∀ x : Point,
          problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp x =
            problem.lagrangian x lamStar := by
      intro x
      exact congrArg (fun f : Point → ℝ ↦ f x) (problem.euclideanLagrangian_eq_lagrangian lamStar)
    -- Rewrite the Chapter 8 trace point back to the source sequence point.
    calc
      problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp
          (WithLp.toLp 2 (xStar.ofLp + delta k • dSeqBridge k)) =
            problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp
              (xStar + delta k • dSeq k) := by
                simp [dSeqBridge]
      _ = problem.lagrangian (xStar + delta k • dSeq k) lamStar := by
            exact hlagrangian_eq (xStar + delta k • dSeq k)
      _ = problem.lagrangian (xSeq (φ k)) lamStar := by rw [htrace_eq k]
      _ ≤ problem.lagrangian xStar lamStar := hgap
      _ = problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp xStar := by
            symm
            exact hlagrangian_eq xStar
      _ = problem.toConstrainedOptimizationProblem.euclideanLagrangian lamStar.ofLp
            (WithLp.toLp 2 xStar.ofLp) := by
              simp
  have h_hessian_nonpos :
      problem.toConstrainedOptimizationProblem.lagrangianHessianQuadratic
        xStar.ofLp lamStar.ofLp d.ofLp ≤ 0 := by
    -- The Chapter 8 upper-trace Taylor estimate closes the contradiction once the direction is
    -- known to be linearized feasible.
    exact
      ConstrainedOptimizationProblem.lagrangianHessianQuadratic_nonpos_of_lagrangian_upper_along_trace
        problem.toConstrainedOptimizationProblem xStar.ofLp d.ofLp lamStar.ofLp dSeqBridge delta
        h_multiplier.toIsKKTPoint h_bridge_data.1 h_bridge_data.2 h_delta_pos hdSeqBridge_tendsto
        hdelta_tendsto h_upper
  exact
    (not_le_of_gt
      (h_sosc.lagrangianHessianQuadratic_pos d hd_linearized hd_nonzero))
      (by simpa [StandardPenaltyProblem.lagrangianHessianQuadratic_eq] using h_hessian_nonpos)

end Chapter10Theorem1061
