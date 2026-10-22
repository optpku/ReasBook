/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace

local notation "X" => EuclideanSpace ℝ (Fin 2)
local notation "ψ" => lagrangianRelaxationExample.dualFunction ∘ single 0
local notation "X⋆" => lagrangianRelaxationExample.lagrangianMinimizers ∘ single 0

/- Primary domain: explicit Lagrangian-duality computations for the single-constraint example from
Definition 1.10.3.

Owner declarations sampled before refining this file:
* `LagrangianProblem.dualDomain`, `LagrangianProblem.lagrangianMinimizers`, and
  `LagrangianProblem.dualFunction` in `Definition_1_10_2`;
* `lagrangianRelaxationExample` in `Definition_1_10_3`, together with the owner theorem
  `LagrangianProblem.lagrangian_single_eq` specialized to that example by unfolding the structure
  literal;
* `LagrangianProblem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers` in
  `Proposition_1_10_7`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection` and
  `LagrangianMinimizerSelection.dualFunction_eq_lagrangian` in `Definition_2_31`.

Best owner abstraction: the primitive owner is `lagrangianRelaxationExample : LagrangianProblem X
1`.

Layering in this file:
* source-facing primitive data: the explicit minimizer path `λ ↦ x(λ)`;
* bridge/view API: its coordinate formulas and the scalar specializations of the owner dual-domain,
  minimizer-set, and dual-function declarations.

No extra public wrapper is introduced here: Proposition 1.10.5 is an explicit example
computation attached to the owner `LagrangianProblem`, not a second owner abstraction. -/

/-- The explicit minimizer trajectory for the Lagrangian relaxation example. -/
def lagrangianRelaxationExampleMinimizerTrajectory (lam : ℝ) : X :=
  WithLp.toLp 2 ![(1 : ℝ) - lam, 1 / (1 - lam)]

/- Proposition 1.10.5 splits naturally into the effective-domain statement, the explicit
singleton description of the minimizer set, and the closed formula for the dual function. -/

/-- Helper for Proposition 1.10.5: the example Lagrangian matches the scalar quadratic formula
from the source proof. -/
lemma lagrangianRelaxationExample_lagrangian_eq_explicit (x : X) (lam : ℝ) :
    lagrangianRelaxationExample.lagrangian x (single 0 lam) =
      (1 / 2 : ℝ) * ((x 0 - 1) ^ (2 : ℕ) + (x 1 - 1) ^ (2 : ℕ)) +
        lam * (x 0 - (1 / 2 : ℝ) * x 1 ^ (2 : ℕ)) := by
  -- Rewrite the owner Lagrangian into the textbook objective-plus-constraint form.
  rw [LagrangianProblem.lagrangian_single_eq]
  rw [lagrangianRelaxationExample_apply, lagrangianRelaxationExample_constraint_apply]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

/-- Helper for Proposition 1.10.5: completing the squares isolates the unique minimizer when
`λ < 1`. -/
lemma lagrangianRelaxationExample_lagrangian_eq_completed_square
    (x : X) (lam : ℝ) (h_lam : lam ≠ 1) :
    lagrangianRelaxationExample.lagrangian x (single 0 lam) =
      (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) +
        ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) +
          (lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - 1 / (2 * (1 - lam)) + (1 / 2 : ℝ)) := by
  -- Complete the square in each coordinate and keep the constant term separate.
  rw [lagrangianRelaxationExample_lagrangian_eq_explicit]
  have hdenom : 1 - lam ≠ 0 := sub_ne_zero.mpr h_lam.symm
  field_simp [hdenom]
  ring_nf

/-- Helper for Proposition 1.10.5: the vertical ray `(0,t)` exposes the unbounded-below regime
when `λ ≥ 1`. -/
lemma lagrangianRelaxationExample_lagrangian_on_vertical_ray (lam t : ℝ) :
    lagrangianRelaxationExample.lagrangian (WithLp.toLp 2 ![(0 : ℝ), t]) (single 0 lam) =
      1 - t + ((1 - lam) / 2 : ℝ) * t ^ (2 : ℕ) := by
  -- Evaluate the scalar formula on the ray `x¹ = 0`.
  rw [lagrangianRelaxationExample_lagrangian_eq_explicit]
  simp
  ring

/-- Helper for Proposition 1.10.5: for `λ < 1`, the textbook trajectory realizes the Lagrangian
minimum. -/
lemma lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers
    (lam : ℝ) (h_lam : lam < 1) :
    lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam := by
  -- Use the completed-square decomposition to compare the trajectory against any point.
  simp only [Function.comp_apply]
  rw [LagrangianProblem.mem_lagrangianMinimizers_iff, isMinOn_iff]
  intro y hy
  have hne : lam ≠ 1 := ne_of_lt h_lam
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square
      (lagrangianRelaxationExampleMinimizerTrajectory lam) lam hne]
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square y lam hne]
  have hcoef : 0 ≤ ((1 - lam) / 2 : ℝ) := by
    nlinarith
  have hsquare0 : 0 ≤ (1 / 2 : ℝ) * (y 0 - (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (y 0 - (1 - lam))]
  have hsquare1 :
      0 ≤ ((1 - lam) / 2 : ℝ) * (y 1 - 1 / (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (y 1 - 1 / (1 - lam)), hcoef]
  simp [lagrangianRelaxationExampleMinimizerTrajectory]
  nlinarith

/-- Helper for Proposition 1.10.5: every minimizer at `λ < 1` must coincide with the explicit
trajectory point. -/
lemma eq_lagrangianRelaxationExampleMinimizerTrajectory_of_mem_lagrangianMinimizers
    (lam : ℝ) (h_lam : lam < 1) {x : X} (hx : x ∈ X⋆ lam) :
    x = lagrangianRelaxationExampleMinimizerTrajectory lam := by
  have hne : lam ≠ 1 := ne_of_lt h_lam
  have hx' : x ∈ lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
    simpa only [Function.comp_apply] using hx
  have hxMin :
      IsMinOn (fun y ↦ lagrangianRelaxationExample.lagrangian y (single 0 lam)) Set.univ x := by
    rw [← LagrangianProblem.mem_lagrangianMinimizers_iff]
    exact hx'
  have htraj :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam :=
    lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam
  have htraj' :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈
        lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
    simpa only [Function.comp_apply] using htraj
  have htrajMin :
      IsMinOn
        (fun y ↦ lagrangianRelaxationExample.lagrangian y (single 0 lam))
        Set.univ
        (lagrangianRelaxationExampleMinimizerTrajectory lam) := by
    rw [← LagrangianProblem.mem_lagrangianMinimizers_iff]
    exact htraj'
  -- Compare the unknown minimizer with the explicit trajectory to force equality in the squares.
  have hle_left :=
    (isMinOn_iff.mp hxMin)
      (lagrangianRelaxationExampleMinimizerTrajectory lam) (by simp)
  have hle_right := (isMinOn_iff.mp htrajMin) x (by simp)
  have heq :
      lagrangianRelaxationExample.lagrangian x (single 0 lam) =
        lagrangianRelaxationExample.lagrangian
          (lagrangianRelaxationExampleMinimizerTrajectory lam) (single 0 lam) :=
    le_antisymm hle_left hle_right
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square x lam hne] at heq
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square
      (lagrangianRelaxationExampleMinimizerTrajectory lam) lam hne] at heq
  have hsquare0 : 0 ≤ (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x 0 - (1 - lam))]
  have hcoef : 0 < ((1 - lam) / 2 : ℝ) := by
    nlinarith
  have hsquare1 :
      0 ≤ ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x 1 - 1 / (1 - lam)), le_of_lt hcoef]
  have hsum :
      (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) +
        ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) = 0 := by
    simpa [lagrangianRelaxationExampleMinimizerTrajectory] using heq
  have hsquare0_eq :
      (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) = 0 := by
    nlinarith [hsquare0, hsquare1, hsum]
  have hsquare1_eq :
      ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) = 0 := by
    nlinarith [hsquare0, hsquare1, hsum]
  -- Each nonnegative square term must vanish, so both coordinates are forced.
  have hx0 : x 0 = 1 - lam := by
    have hsq : (x 0 - (1 - lam)) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hsquare0_eq).resolve_left (show (1 / 2 : ℝ) ≠ 0 by norm_num)
    have hzero : x 0 - (1 - lam) = 0 := sq_eq_zero_iff.mp hsq
    linarith
  have hx1 : x 1 = 1 / (1 - lam) := by
    have hsq : (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hsquare1_eq).resolve_left (ne_of_gt hcoef)
    have hzero : x 1 - 1 / (1 - lam) = 0 := sq_eq_zero_iff.mp hsq
    linarith
  ext i
  fin_cases i
  · simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hx0
  · simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hx1

/-- Helper for Proposition 1.10.5: once `λ ≥ 1`, the example dual function is `-∞`. -/
lemma lagrangianRelaxationExample_dualFunction_eq_bot_of_one_le
    (lam : ℝ) (h_lam : 1 ≤ lam) :
    ψ lam = (⊥ : EReal) := by
  -- Push the vertical ray far enough so that the Lagrangian value falls below any prescribed
  -- real threshold.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro c
  let t : ℝ := max 0 (2 - c)
  have ht_gt : 1 - t < c := by
    dsimp [t]
    by_cases hcase : 2 - c ≤ 0
    · rw [max_eq_left hcase]
      linarith
    · have hcase' : 0 < 2 - c := lt_of_not_ge hcase
      rw [max_eq_right hcase'.le]
      linarith
  have hcoef_nonpos : ((1 - lam) / 2 : ℝ) ≤ 0 := by
    nlinarith
  have hray_lt :
      lagrangianRelaxationExample.lagrangian (WithLp.toLp 2 ![(0 : ℝ), t]) (single 0 lam) < c := by
    rw [lagrangianRelaxationExample_lagrangian_on_vertical_ray]
    have hquad_nonpos : ((1 - lam) / 2 : ℝ) * t ^ (2 : ℕ) ≤ 0 := by
      nlinarith [sq_nonneg t, hcoef_nonpos]
    linarith
  -- The dual value is bounded above by every feasible point of the unconstrained subproblem.
  have hdual_le :
      lagrangianRelaxationExample.dualFunction (single 0 lam) ≤
        (lagrangianRelaxationExample.lagrangian (WithLp.toLp 2 ![(0 : ℝ), t]) (single 0 lam) :
          EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun x : X ↦ lagrangianRelaxationExample.lagrangian x (single 0 lam)))
        (x := WithLp.toLp 2 ![(0 : ℝ), t])
        (by simp))
  exact lt_of_le_of_lt hdual_le (by exact_mod_cast hray_lt)

/-- Proposition 1.10.5 (1): along the scalar multiplier parametrization, the effective domain of
the example dual function is `(-∞, 1)`. -/
-- Proof sketch: rewrite membership in `lagrangianRelaxationExample.dualDomain` along the scalar
-- multiplier path as boundedness below of the example Lagrangian, then analyze the coefficient of
-- `(x 1)^2` to show boundedness occurs exactly when `λ < 1`.
theorem lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff (lam : ℝ) :
    single 0 lam ∈ lagrangianRelaxationExample.dualDomain ↔ lam < 1 := by
  constructor
  · intro hdom
    -- Outside `(-∞, 1)`, the vertical-ray argument forces the dual value to be `-∞`.
    by_contra hnot
    have hge : 1 ≤ lam := not_lt.mp hnot
    have hbot : lagrangianRelaxationExample.dualFunction (single 0 lam) = (⊥ : EReal) := by
      simpa only [Function.comp_apply] using
        lagrangianRelaxationExample_dualFunction_eq_bot_of_one_le lam hge
    rw [LagrangianProblem.mem_dualDomain_iff, bot_lt_iff_ne_bot, hbot] at hdom
    exact hdom rfl
  · intro h_lam
    -- Inside `(-∞, 1)`, the explicit trajectory attains the dual value as a finite real number.
    have htraj :
        lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam :=
      lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam
    have htraj' :
        lagrangianRelaxationExampleMinimizerTrajectory lam ∈
          lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
      simpa only [Function.comp_apply] using htraj
    rw [LagrangianProblem.mem_dualDomain_iff, bot_lt_iff_ne_bot]
    rw [LagrangianProblem.dualFunction_eq_lagrangian
      (problem := lagrangianRelaxationExample) htraj']
    exact EReal.coe_ne_bot _

/-- Proposition 1.10.5 (2): for every `λ < 1`, the Lagrangian subproblem has the unique minimizer
with coordinates `x¹(λ) = 1 - λ` and `x²(λ) = 1 / (1 - λ)`. -/
-- Proof sketch: solve the first-order optimality equations for the example Lagrangian and use
-- strict convexity for `λ < 1` to identify the unique minimizer.
theorem lagrangianRelaxationExample_lagrangianMinimizers_eq_singleton
    (lam : ℝ) (h_lam : lam < 1) :
    X⋆ lam =
      ({lagrangianRelaxationExampleMinimizerTrajectory lam} : Set X) :=
  by
  ext x
  constructor
  · intro hx
    -- Any minimizer must make both completed-square terms vanish.
    have hxeq :
        x = lagrangianRelaxationExampleMinimizerTrajectory lam :=
      eq_lagrangianRelaxationExampleMinimizerTrajectory_of_mem_lagrangianMinimizers lam h_lam hx
    simp [hxeq]
  · intro hx
    -- The explicit trajectory is already known to be a minimizer.
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam

/-- Proposition 1.10.5 (3): for every `λ < 1`, the dual function of the example is
`λ - (1 / 2) λ² - 1 / (2 (1 - λ)) + 1 / 2`. -/
-- Proof sketch: evaluate the Lagrangian at the explicit minimizer trajectory and simplify the
-- resulting expression using the coordinate formulas for the minimizer.
theorem lagrangianRelaxationExample_dualFunction_eq_closedForm
    (lam : ℝ) (h_lam : lam < 1) :
    ψ lam =
      ((lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - 1 / (2 * (1 - lam)) + (1 / 2 : ℝ)) : EReal) :=
  by
  have htraj :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam :=
    lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam
  have htraj' :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈
        lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
    simpa only [Function.comp_apply] using htraj
  have hne : lam ≠ 1 := ne_of_lt h_lam
  -- Evaluate the dual function at the unique minimizer and simplify the completed-square form.
  simp only [Function.comp_apply]
  rw [LagrangianProblem.dualFunction_eq_lagrangian
    (problem := lagrangianRelaxationExample) htraj']
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square
    (lagrangianRelaxationExampleMinimizerTrajectory lam) lam hne]
  simp [lagrangianRelaxationExampleMinimizerTrajectory]
  have hdenom : 1 - lam ≠ 0 := by
    linarith
  have hvalue :
      (lam - (2⁻¹ : ℝ) * lam ^ (2 : ℕ) - (1 - lam)⁻¹ * (2⁻¹ : ℝ) + (2⁻¹ : ℝ)) =
        (lam - (2⁻¹ : ℝ) * lam ^ (2 : ℕ) - (2 * (1 - lam))⁻¹ + (2⁻¹ : ℝ)) := by
    field_simp [hdenom]
  have hvalueE :
      (↑lam : EReal) - ↑(2⁻¹ : ℝ) * ↑lam ^ (2 : ℕ) - ↑((1 - lam)⁻¹ : ℝ) * ↑(2⁻¹ : ℝ) +
          ↑(2⁻¹ : ℝ) =
        (↑lam : EReal) - ↑(2⁻¹ : ℝ) * ↑lam ^ (2 : ℕ) - ↑((2 * (1 - lam))⁻¹ : ℝ) +
          ↑(2⁻¹ : ℝ) := by
    exact_mod_cast hvalue
  rw [show (2 * (1 - (lam : EReal)))⁻¹ = (((2 * (1 - lam))⁻¹ : ℝ) : EReal) by rfl]
  exact hvalueE
