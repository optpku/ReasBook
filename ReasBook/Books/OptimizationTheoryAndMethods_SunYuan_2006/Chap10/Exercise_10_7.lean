/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_6_extra_1
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open scoped BigOperators

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `StandardPenaltyProblem`, `IsStrongDistanceFunction`,
--   `StandardPenaltyProblem.nonsmoothExactPenalty`, and `PenaltyFunction.nonsmoothExact`
--   from `Definition_10_6_extra_1` are the chapter's canonical owners for exact-penalty
--   kernels, source-facing penalty objectives, and bundled penalty functions.
-- * The source exercise adds only the log-sum-exp smoothing kernel on `ℝ^m` and its
--   constant-offset relation to that existing exact-penalty layer.
-- This file therefore keeps the source-facing `problem.logSumExpPenalty σ`, equips the
-- centered kernel with the chapter's canonical strong-distance structure, and packages the
-- resulting centered penalty function as `PenaltyFunction.logSumExp`, using the existing
-- exact-penalty owners only as the implementation bridge.

/-- The log-sum-exp approximation of the coordinatewise maximum on `ConstraintPoint`, evaluated on
the absolute values of the coordinates. -/
def logSumExpAbs (c : ConstraintPoint) : ℝ :=
  Real.log (∑ i : Fin m, Real.exp |c i|)

/-- Evaluating `logSumExpAbs c` unfolds to `log (∑ i, exp |c i|)`. -/
@[simp] theorem logSumExpAbs_eq (c : ConstraintPoint) :
    logSumExpAbs c = Real.log (∑ i : Fin m, Real.exp |c i|) :=
  rfl

/-- The exercise kernel sends the zero vector to `log m`. -/
@[simp] theorem logSumExpAbs_zero :
    logSumExpAbs (0 : ConstraintPoint) = Real.log (m : ℝ) := by
  simp [logSumExpAbs]

/-- Each coordinate of `c` is bounded above by the log-sum-exp approximation of the maximum of
the absolute values of the coordinates. -/
theorem abs_apply_le_logSumExpAbs (c : ConstraintPoint) (i : Fin m) :
    |c i| ≤ logSumExpAbs c := by
  have hsingle :
      Real.exp |c i| ≤ ∑ j : Fin m, Real.exp |c j| := by
    exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos |c j|).le) (Finset.mem_univ i)
  rw [logSumExpAbs, Real.le_log_iff_exp_le]
  · simpa using hsingle
  · exact lt_of_lt_of_le (Real.exp_pos |c i|) hsingle

/-- Centering `logSumExpAbs` by its value at `0` gives the canonical penalty-term bridge that
vanishes on the zero vector. -/
def centeredLogSumExpAbs (c : ConstraintPoint) : ℝ :=
  logSumExpAbs c - Real.log (m : ℝ)

/-- Evaluating `centeredLogSumExpAbs c` unfolds to the centered log-sum-exp formula. -/
@[simp] theorem centeredLogSumExpAbs_eq (c : ConstraintPoint) :
    centeredLogSumExpAbs c = logSumExpAbs c - Real.log (m : ℝ) :=
  rfl

/-- The centered log-sum-exp kernel vanishes at the zero vector. -/
@[simp] theorem centeredLogSumExpAbs_zero :
    centeredLogSumExpAbs (0 : ConstraintPoint) = 0 := by
  simp [centeredLogSumExpAbs]

/-- Helper for Chapter10 Exercise 10.7: each exponential coordinate of the affine combination
`a • x + b • y` is bounded by the weighted geometric mean of the exponential coordinates of `x`
and `y`. -/
theorem exp_abs_smul_add_apply_le_mul_rpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x y : ConstraintPoint) (i : Fin m) :
    Real.exp |(a • x + b • y) i| ≤
      (Real.exp |x i|) ^ a * (Real.exp |y i|) ^ b := by
  -- First replace the absolute value of the affine combination by the triangle inequality.
  have habs :
      |(a • x + b • y) i| ≤ a * |x i| + b * |y i| := by
    calc
      |(a • x + b • y) i| = |a * x i + b * y i| := by
        simp [smul_eq_mul]
      _ ≤ |a * x i| + |b * y i| := abs_add_le _ _
      _ = a * |x i| + b * |y i| := by
        rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
  -- Then monotonicity of `exp` and the `exp (u + v) = exp u * exp v` identity finish the bridge.
  have hx :
      Real.exp (a * |x i|) = (Real.exp |x i|) ^ a := by
    rw [mul_comm, Real.exp_mul]
  have hy :
      Real.exp (b * |y i|) = (Real.exp |y i|) ^ b := by
    rw [mul_comm, Real.exp_mul]
  calc
    Real.exp |(a • x + b • y) i| ≤ Real.exp (a * |x i| + b * |y i|) := by
      gcongr
    _ = Real.exp (a * |x i|) * Real.exp (b * |y i|) := by
      rw [Real.exp_add]
    _ = (Real.exp |x i|) ^ a * (Real.exp |y i|) ^ b := by
      rw [hx, hy]

/-- Helper for Chapter10 Exercise 10.7: the exponential sum defining `logSumExpAbs` satisfies
the multiplicative interpolation inequality behind log-sum-exp convexity. -/
theorem sumExpAbs_smul_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (x y : ConstraintPoint) :
    (∑ i : Fin m, Real.exp |(a • x + b • y) i|) ≤
      (∑ i : Fin m, Real.exp |x i|) ^ a * (∑ i : Fin m, Real.exp |y i|) ^ b := by
  by_cases ha0 : a = 0
  · -- If `a = 0`, the affine combination collapses to `y`.
    have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · -- If `b = 0`, the affine combination collapses to `x`.
    have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hsum :
      (∑ i : Fin m, Real.exp |(a • x + b • y) i|) ≤
        ∑ i : Fin m, (Real.exp |x i|) ^ a * (Real.exp |y i|) ^ b := by
    -- Sum the pointwise interpolation inequality over all coordinates.
    refine Finset.sum_le_sum fun i _ ↦ exp_abs_smul_add_apply_le_mul_rpow ha hb x y i
  refine hsum.trans ?_
  -- Hölder upgrades the pointwise weighted geometric mean bound to the sum inequality.
  have hpq : a⁻¹.HolderConjugate b⁻¹ :=
    Real.HolderConjugate.inv_inv ha' hb' hab
  have hxpow : ∀ i : Fin m, ((Real.exp |x i|) ^ a) ^ a⁻¹ = Real.exp |x i| := by
    intro i
    rw [← Real.rpow_mul (le_of_lt (Real.exp_pos _)), mul_inv_cancel₀ ha0, Real.rpow_one]
  have hypow : ∀ i : Fin m, ((Real.exp |y i|) ^ b) ^ b⁻¹ = Real.exp |y i| := by
    intro i
    rw [← Real.rpow_mul (le_of_lt (Real.exp_pos _)), mul_inv_cancel₀ hb0, Real.rpow_one]
  have hholder :
      ∑ i : Fin m, (Real.exp |x i|) ^ a * (Real.exp |y i|) ^ b ≤
        (∑ i : Fin m, ((Real.exp |x i|) ^ a) ^ a⁻¹) ^ (1 / a⁻¹) *
          (∑ i : Fin m, ((Real.exp |y i|) ^ b) ^ b⁻¹) ^ (1 / b⁻¹) :=
    (Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
      (f := fun i : Fin m ↦ (Real.exp |x i|) ^ a)
      (g := fun i : Fin m ↦ (Real.exp |y i|) ^ b)
      hpq
      (fun i _ ↦ Real.rpow_nonneg (le_of_lt (Real.exp_pos _)) _)
      (fun i _ ↦ Real.rpow_nonneg (le_of_lt (Real.exp_pos _)) _) : _)
  simpa [one_div, ha0, hb0, hxpow, hypow] using hholder

/-- Helper for Chapter10 Exercise 10.7: for `m > 0`, the exponential sum in `logSumExpAbs` is
strictly positive. -/
theorem sumExpAbs_pos (hm : 0 < m) (c : ConstraintPoint) :
    0 < ∑ i : Fin m, Real.exp |c i| := by
  -- A single positive summand already forces the whole finite sum to be positive.
  let i : Fin m := ⟨0, hm⟩
  have hsingle :
      Real.exp |c i| ≤ ∑ j : Fin m, Real.exp |c j| := by
    exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos |c j|).le) (Finset.mem_univ i)
  exact lt_of_lt_of_le (Real.exp_pos |c i|) hsingle

/-- Helper for Chapter10 Exercise 10.7: the uncentered kernel `logSumExpAbs` is convex on
`ConstraintPoint`. -/
theorem convexOn_univ_logSumExpAbs :
    ConvexOn ℝ (Set.univ : Set ConstraintPoint) (logSumExpAbs : ConstraintPoint → ℝ) := by
  by_cases hm : m = 0
  · subst hm
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    -- In dimension zero every point is `0`, so the kernel is constant.
    have hx : x = 0 := by
      ext i
      exact Fin.elim0 i
    have hy : y = 0 := by
      ext i
      exact Fin.elim0 i
    simp [hx, hy]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    -- The multiplicative interpolation lemma is the core convexity estimate.
    have hsum := sumExpAbs_smul_add_le ha hb hab x y
    have hxy_pos : 0 < ∑ i : Fin m, Real.exp |(a • x + b • y) i| :=
      sumExpAbs_pos hmpos (a • x + b • y)
    have hx_pos : 0 < ∑ i : Fin m, Real.exp |x i| :=
      sumExpAbs_pos hmpos x
    have hy_pos : 0 < ∑ i : Fin m, Real.exp |y i| :=
      sumExpAbs_pos hmpos y
    -- Taking `log` turns the multiplicative estimate into the convexity inequality.
    calc
      logSumExpAbs (a • x + b • y)
          = Real.log (∑ i : Fin m, Real.exp |(a • x + b • y) i|) := by
            rw [logSumExpAbs_eq]
      _ ≤ Real.log
          ((∑ i : Fin m, Real.exp |x i|) ^ a * (∑ i : Fin m, Real.exp |y i|) ^ b) := by
            exact Real.log_le_log hxy_pos hsum
      _ = Real.log ((∑ i : Fin m, Real.exp |x i|) ^ a) +
            Real.log ((∑ i : Fin m, Real.exp |y i|) ^ b) := by
            rw [Real.log_mul
              (by positivity : (∑ i : Fin m, Real.exp |x i|) ^ a ≠ 0)
              (by positivity : (∑ i : Fin m, Real.exp |y i|) ^ b ≠ 0)]
      _ = a * Real.log (∑ i : Fin m, Real.exp |x i|) +
            b * Real.log (∑ i : Fin m, Real.exp |y i|) := by
            rw [Real.log_rpow hx_pos a, Real.log_rpow hy_pos b]
      _ = a • logSumExpAbs x + b • logSumExpAbs y := by
            simp [logSumExpAbs_eq, smul_eq_mul]

/-- Helper for Chapter10 Exercise 10.7: the centered kernel dominates the transported `ℓ₁` norm
with constant `(m : ℝ)⁻¹` when `m > 0`. -/
theorem inv_card_mul_l1Norm_le_centeredLogSumExpAbs {c : ConstraintPoint} (hm : 0 < m) :
    ((m : ℝ)⁻¹) * ‖c‖₁ ≤ centeredLogSumExpAbs c := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hweights : ∑ i : Fin m, (m : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, hm0]
  have hconcave :=
    strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := Finset.univ)
      (w := fun _ : Fin m ↦ (m : ℝ)⁻¹)
      (p := fun i : Fin m ↦ Real.exp |c i|)
      (h₀ := fun _ _ ↦ by positivity)
      (h₁ := hweights)
      (hmem := fun i _ ↦ by simpa using Real.exp_pos |c i|)
  -- Jensen for `log` on the equally weighted exponential coordinates yields the lower bound.
  calc
    ((m : ℝ)⁻¹) * ‖c‖₁
        = ∑ i : Fin m, (m : ℝ)⁻¹ * Real.log (Real.exp |c i|) := by
            rw [_root_.l1Norm_eq_sum_abs c.ofLp]
            simp [Finset.mul_sum]
    _ ≤ Real.log (∑ i : Fin m, (m : ℝ)⁻¹ * Real.exp |c i|) := by
          simpa [smul_eq_mul] using hconcave
    _ = Real.log ((m : ℝ)⁻¹ * ∑ i : Fin m, Real.exp |c i|) := by
          rw [Finset.mul_sum]
    _ = centeredLogSumExpAbs c := by
          rw [centeredLogSumExpAbs, logSumExpAbs]
          rw [Real.log_mul (inv_ne_zero hm0) (sumExpAbs_pos hm c).ne', Real.log_inv]
          ring

/-- Chapter10 Exercise 10.7: the centered log-sum-exp kernel is a strong distance function in the
sense of Definition 10.6-extra-1, so the chapter's exact-penalty owners apply to it directly. -/
instance instIsStrongDistanceFunctionCenteredLogSumExpAbs :
    IsStrongDistanceFunction (centeredLogSumExpAbs : ConstraintPoint → ℝ) where
  convexOn_univ := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    -- Subtracting the same constant from both sides preserves the convexity inequality.
    have hmain :
        logSumExpAbs (a • x + b • y) ≤ a • logSumExpAbs x + b • logSumExpAbs y := by
      exact convexOn_univ_logSumExpAbs.2 (x := x) (by simp) (y := y) (by simp) ha hb hab
    let L : ℝ := Real.log (m : ℝ)
    have hconst : a * L + b * L = L := by
      calc
        a * L + b * L = (a + b) * L := by ring
        _ = L := by rw [hab, one_mul]
    calc
      centeredLogSumExpAbs (a • x + b • y) = logSumExpAbs (a • x + b • y) - L := by
        rfl
      _ ≤ (a • logSumExpAbs x + b • logSumExpAbs y) - L := by
        exact sub_le_sub_right hmain L
      _ = a * logSumExpAbs x + b * logSumExpAbs y - L := by
        rfl
      _ = a * logSumExpAbs x + b * logSumExpAbs y - (a * L + b * L) := by
        rw [hconst]
      _ = a * (logSumExpAbs x - L) + b * (logSumExpAbs y - L) := by
        ring
      _ = a • centeredLogSumExpAbs x + b • centeredLogSumExpAbs y := by
        simp [centeredLogSumExpAbs, L, smul_eq_mul]
  map_zero := centeredLogSumExpAbs_zero
  exists_pos_le_mul_l1Norm := by
    by_cases hm : m = 0
    · subst hm
      -- In dimension zero every point is `0`, so any positive witness works.
      refine ⟨1, zero_lt_one, ?_⟩
      intro c
      have hc : c = 0 := by
        ext i
        exact Fin.elim0 i
      rw [hc]
      rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
      simp
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      -- For `m > 0`, Jensen provides the uniform witness `δ = (m : ℝ)⁻¹`.
      refine ⟨(m : ℝ)⁻¹, by positivity, ?_⟩
      intro c
      exact inv_card_mul_l1Norm_le_centeredLogSumExpAbs hmpos

namespace PenaltyFunction

/-- Canonical owner layer for Chapter10 Exercise 10.7: for a positive penalty parameter `σ`, the
centered log-sum-exp penalty function is the bundled `PenaltyFunction` whose penalty term is
`c ↦ σ * centeredLogSumExpAbs c`. -/
def logSumExp (problem : StandardPenaltyProblem n m) (σ : ℝ) (hσ : 0 < σ) :
    PenaltyFunction problem :=
  nonsmoothExact problem (centeredLogSumExpAbs : ConstraintPoint → ℝ) σ hσ

/-- Evaluating `PenaltyFunction.logSumExp problem σ hσ` expands to the centered log-sum-exp
penalty formula `f(x) + σ * centeredLogSumExpAbs (c⁽-⁾[problem] x)`. -/
@[simp] theorem logSumExp_apply
    (problem : StandardPenaltyProblem n m) (σ : ℝ) (hσ : 0 < σ) (x : Point) :
    logSumExp problem σ hσ x =
      problem.objective x + σ * centeredLogSumExpAbs (c⁽-⁾[problem] x) := by
  rw [logSumExp, nonsmoothExact_apply, problem.nonsmoothExactPenalty_apply]

end PenaltyFunction

namespace StandardPenaltyProblem

/-- Source-facing formulation for Chapter10 Exercise 10.7: the smooth replacement of the `L∞`
penalty function is
`x ↦ problem.objective x + σ * log (∑ i, exp |c⁽-⁾[problem] x i|)`. -/
def logSumExpPenalty (problem : StandardPenaltyProblem n m) (σ : ℝ) : Point → ℝ :=
  fun x ↦ problem.objective x + σ * logSumExpAbs (c⁽-⁾[problem] x)

/-- Evaluating `problem.logSumExpPenalty σ` unfolds to the source formula
`f(x) + σ * log (∑ i, exp |cᵢ⁽-⁾(x)|)`. -/
@[simp] theorem logSumExpPenalty_apply
    (problem : StandardPenaltyProblem n m) (σ : ℝ) (x : Point) :
    problem.logSumExpPenalty σ x =
      problem.objective x + σ * Real.log (∑ i : Fin m, Real.exp |c⁽-⁾[problem] x i|) := by
  rfl

/-- The source-facing Exercise 10.7 objective differs from the centered Chapter 10 exact-penalty
objective with kernel `centeredLogSumExpAbs` only by the constant offset `σ * log m`. -/
theorem logSumExpPenalty_eq_nonsmoothExactPenalty_add_log_card
    (problem : StandardPenaltyProblem n m) (σ : ℝ) :
    problem.logSumExpPenalty σ =
      fun x ↦
        problem.nonsmoothExactPenalty (centeredLogSumExpAbs : ConstraintPoint → ℝ) σ x +
          σ * Real.log (m : ℝ) := by
  funext x
  rw [problem.nonsmoothExactPenalty_apply, logSumExpPenalty_apply]
  simp [centeredLogSumExpAbs]
  ring

/-- Under the positivity hypothesis needed for `PenaltyFunction.logSumExp problem σ hσ`, the
source-facing Exercise 10.7 objective differs from that canonical bundled penalty-function view
only by the constant offset `σ * log m`. -/
theorem logSumExpPenalty_eq_logSumExp_add_log_card
    (problem : StandardPenaltyProblem n m) (σ : ℝ) (hσ : 0 < σ) :
    problem.logSumExpPenalty σ =
      fun x ↦
        PenaltyFunction.logSumExp problem σ hσ x +
          σ * Real.log (m : ℝ) := by
  funext x
  rw [PenaltyFunction.logSumExp_apply]
  exact congrFun (problem.logSumExpPenalty_eq_nonsmoothExactPenalty_add_log_card σ) x

/-- If `x` is feasible for `problem`, then the Exercise 10.7 penalty function reduces to the
objective plus the constant offset `σ * log m`. -/
theorem logSumExpPenalty_eq_objective_add_log_card_of_mem
    (problem : StandardPenaltyProblem n m) (σ : ℝ) {x : Point} (hx : x ∈ problem) :
    problem.logSumExpPenalty σ x = problem.objective x + σ * Real.log (m : ℝ) := by
  have hx0 : c⁽-⁾[problem] x = 0 :=
    (problem.mem_iff_constraintViolation_eq_zero x).mp hx
  simp [logSumExpPenalty, hx0]

/-- Each coordinate of the absolute violation vector is bounded above by the log-sum-exp penalty
term applied to that violation vector. -/
theorem abs_constraintViolation_le_logSumExpAbs
    (problem : StandardPenaltyProblem n m) (x : Point) (i : Fin m) :
    |c⁽-⁾[problem] x i| ≤ logSumExpAbs (c⁽-⁾[problem] x) :=
  abs_apply_le_logSumExpAbs (c⁽-⁾[problem] x) i

/-- If the Chapter 10 violation vector vanishes at `x`, then the Exercise 10.7 penalty function
reduces to the objective plus the constant offset `σ * log m`. -/
theorem logSumExpPenalty_eq_objective_add_log_card_of_constraintViolation_eq_zero
    (problem : StandardPenaltyProblem n m) (σ : ℝ) {x : Point}
    (hx : c⁽-⁾[problem] x = 0) :
    problem.logSumExpPenalty σ x = problem.objective x + σ * Real.log (m : ℝ) := by
  exact problem.logSumExpPenalty_eq_objective_add_log_card_of_mem σ
    ((problem.mem_iff_constraintViolation_eq_zero x).mpr hx)

end StandardPenaltyProblem

#print axioms StandardPenaltyProblem.constraintViolation
#print axioms logSumExpAbs
#print axioms PenaltyFunction.logSumExp
#print axioms StandardPenaltyProblem.logSumExpPenalty
#print axioms instIsStrongDistanceFunctionCenteredLogSumExpAbs

end
