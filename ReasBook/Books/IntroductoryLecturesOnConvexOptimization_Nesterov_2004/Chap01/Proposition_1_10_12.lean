/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set EuclideanSpace

/-
Source/core/bridge triage for Proposition 1.10.12:
- source-facing: the textbook scalar maximizer `λ_*` and the trajectory value `x(λ_*)`;
- core/canonical owner: `lagrangianRelaxationExample.dualFunction`;
- bridge/view: `lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff` and
  `lagrangianRelaxationExample_dualFunction_eq_closedForm`, together with the owner-side
  maximality and dual-feasibility bridges for `single 0 λ_*`.

Primitive data already live upstream:
- the owner `lagrangianRelaxationExample : LagrangianProblem _ 1`,
- the scalar-domain and closed-form bridge theorems listed above,
- the explicit minimizer trajectory `lagrangianRelaxationExampleMinimizerTrajectory`.

This file only names the textbook scalar maximizer `λ_*` and records the derived maximizer and
trajectory statements attached to that owner data.
-/

local notation "D" => Iio (1 : ℝ)
local notation "ψ" => lagrangianRelaxationExample.dualFunction ∘ single 0

/-- The unique maximizer of the example dual function on `(-∞, 1)`. -/
def lagrangianRelaxationExampleLambdaStar : ℝ :=
  1 - Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ)

/-- Helper for Proposition 1.10.12: the real closed form of the example dual function on
`(-∞, 1)`. -/
def lagrangianRelaxationExampleClosedForm (lam : ℝ) : ℝ :=
  lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - (1 - lam)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ)

/-- Helper for Proposition 1.10.12: the first derivative of the real closed form. -/
def lagrangianRelaxationExampleClosedFormDeriv (lam : ℝ) : ℝ :=
  1 - lam - ((1 - lam) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ)

/-- Helper for Proposition 1.10.12: on `(-∞, 1)`, the owner-side dual function agrees with the
real closed form. -/
lemma lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one
    {lam : ℝ} (h_lam : lam ∈ D) :
    ψ lam = (lagrangianRelaxationExampleClosedForm lam : EReal) := by
  -- The scalar interval `D` is exactly the domain where Proposition 1.10.5 gives the closed form.
  have hreal :
      lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - 1 / (2 * (1 - lam)) + (1 / 2 : ℝ) =
        lagrangianRelaxationExampleClosedForm lam := by
    have hlamlt : lam < 1 := h_lam
    have hne : 1 - lam ≠ 0 := by
      linarith
    unfold lagrangianRelaxationExampleClosedForm
    field_simp [hne]
  rw [← hreal]
  exact lagrangianRelaxationExample_dualFunction_eq_closedForm lam h_lam

/-- Helper for Proposition 1.10.12: the owner-side `IsMaxOn` statement is equivalent to the real
closed-form `IsMaxOn` statement on `(-∞, 1)`. -/
lemma lagrangianRelaxationExample_closedForm_isMaxOn_iff
    {lam : ℝ} (h_lam : lam ∈ D) :
    IsMaxOn ψ D lam ↔ IsMaxOn lagrangianRelaxationExampleClosedForm D lam := by
  rw [isMaxOn_iff, isMaxOn_iff]
  constructor
  · intro hmax y hy
    -- Rewrite both dual values into finite real numbers before comparing them.
    have hy_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one hy
    have hlam_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one h_lam
    have hle := hmax y hy
    rw [hy_eq, hlam_eq] at hle
    exact EReal.coe_le_coe_iff.mp hle
  · intro hmax y hy
    -- Transport the real comparison back into `EReal` using the same closed-form identities.
    have hy_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one hy
    have hlam_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one h_lam
    rw [hy_eq, hlam_eq]
    exact EReal.coe_le_coe_iff.mpr (hmax y hy)

/-- Helper for Proposition 1.10.12: the closed form is continuous on `(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedForm_continuousOn :
    ContinuousOn lagrangianRelaxationExampleClosedForm D := by
  intro x hx
  -- The only singularity comes from `1 - x = 0`, excluded by `x < 1`.
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by
    linarith
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
        x := by
    fun_prop (disch := assumption)
  change ContinuousWithinAt
    (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
    D x
  exact hcont.continuousWithinAt

/-- Helper for Proposition 1.10.12: the closed form is differentiable at every point of
`(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedForm_differentiableAt
    {x : ℝ} (hx : x ∈ D) :
    DifferentiableAt ℝ lagrangianRelaxationExampleClosedForm x := by
  -- Again, the denominator does not vanish because `x < 1`.
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by
    linarith
  change DifferentiableAt ℝ
    (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
    x
  fun_prop (disch := assumption)

/-- Helper for Proposition 1.10.12: the closed form has the expected first derivative on
`(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedForm_hasDerivAt
    {x : ℝ} (hx : x ∈ D) :
    HasDerivAt lagrangianRelaxationExampleClosedForm
      (lagrangianRelaxationExampleClosedFormDeriv x) x := by
  -- Differentiate the affine, quadratic, and reciprocal pieces separately.
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by
    linarith
  have hid : HasDerivAt (fun y : ℝ ↦ y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ)) x x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)
  have hu : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hinv : HasDerivAt (fun y : ℝ ↦ (1 - y)⁻¹) (((1 - x) ^ (2 : ℕ))⁻¹) x := by
    simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hu.inv hne
  have hhalf :
      HasDerivAt
        (fun y : ℝ ↦ (1 - y)⁻¹ * (1 / 2 : ℝ))
        (((1 - x) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ)) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      hinv.mul_const (1 / 2 : ℝ)
  change HasDerivAt
    (fun y : ℝ ↦ y - (1 / 2 : ℝ) * y ^ (2 : ℕ) - (1 - y)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
    (lagrangianRelaxationExampleClosedFormDeriv x) x
  simpa [lagrangianRelaxationExampleClosedFormDeriv, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using
    ((hid.sub hsq).sub hhalf).add_const (1 / 2 : ℝ)

/-- Helper for Proposition 1.10.12: the derivative of the closed form has the expected textbook
formula. -/
lemma lagrangianRelaxationExampleClosedForm_deriv
    {x : ℝ} (hx : x ∈ D) :
    deriv lagrangianRelaxationExampleClosedForm x =
      lagrangianRelaxationExampleClosedFormDeriv x := by
  -- The derivative is already packaged by the explicit `HasDerivAt` computation above.
  exact (lagrangianRelaxationExampleClosedForm_hasDerivAt hx).deriv

/-- Helper for Proposition 1.10.12: the explicit derivative is continuous on `(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedFormDeriv_continuousOn :
    ContinuousOn lagrangianRelaxationExampleClosedFormDeriv D := by
  intro x hx
  -- The derivative only has the same pole at `x = 1`, which is still outside the domain.
  have hxlt : x < 1 := hx
  have hx0 : 0 < 1 - x := by
    linarith
  have hne : ((1 - x) ^ (2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ 1 - t - ((1 - t) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ))
        x := by
    fun_prop (disch := assumption)
  change ContinuousWithinAt
    (fun t : ℝ ↦ 1 - t - ((1 - t) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ))
    D x
  exact hcont.continuousWithinAt

/-- Helper for Proposition 1.10.12: the explicit first derivative itself has derivative
`-1 - (1 - x)⁻³`. -/
lemma lagrangianRelaxationExampleClosedFormDeriv_hasDerivAt
    {x : ℝ} (hx : x ∈ D) :
    HasDerivAt lagrangianRelaxationExampleClosedFormDeriv
      (-1 - ((1 - x) ^ (3 : ℕ))⁻¹) x := by
  -- Differentiate the inverse-square term explicitly and simplify the resulting algebra.
  have hxlt : x < 1 := hx
  have hx0 : 0 < 1 - x := by
    linarith
  have hne : ((1 - x) ^ (2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hu : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hsq : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ (2 : ℕ)) (-2 * (1 - x)) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hu.pow 2
  have hinv :
      HasDerivAt (fun t : ℝ ↦ ((1 - t) ^ (2 : ℕ) : ℝ)⁻¹)
        (2 * (1 - x) / (((1 - x) ^ (2 : ℕ) : ℝ) ^ (2 : ℕ))) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsq.inv hne
  have hhalf :
      HasDerivAt
        (fun t : ℝ ↦ ((1 - t) ^ (2 : ℕ) : ℝ)⁻¹ * (1 / 2 : ℝ))
        ((1 - x) / (((1 - x) ^ (2 : ℕ) : ℝ) ^ (2 : ℕ))) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hinv.mul_const (1 / 2 : ℝ)
  convert hu.sub hhalf using 1
  have hne1 : 1 - x ≠ 0 := by
    linarith
  field_simp [hne1]

/-- Helper for Proposition 1.10.12: the explicit derivative is strictly decreasing on
`(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedFormDeriv_strictAntiOn :
    StrictAntiOn lagrangianRelaxationExampleClosedFormDeriv D := by
  -- The second derivative is strictly negative everywhere on the interval.
  have hconv : Convex ℝ (Iio (1 : ℝ)) := convex_Iio (1 : ℝ)
  refine strictAntiOn_of_deriv_neg hconv
    lagrangianRelaxationExampleClosedFormDeriv_continuousOn ?_
  intro x hx
  have hxD : x ∈ D := interior_subset hx
  rw [show deriv lagrangianRelaxationExampleClosedFormDeriv x =
      -1 - ((1 - x) ^ (3 : ℕ))⁻¹ by
      exact (lagrangianRelaxationExampleClosedFormDeriv_hasDerivAt hxD).deriv]
  have hx0 : 0 < 1 - x := by
    have hxlt : x < 1 := by
      simpa using hx
    linarith
  have hcubeInv : 0 < (((1 - x) ^ (3 : ℕ) : ℝ)⁻¹) := by
    positivity
  linarith

/-- Helper for Proposition 1.10.12: the real closed form is strictly concave on `(-∞, 1)`. -/
lemma lagrangianRelaxationExample_closedForm_strictConcaveOn :
    StrictConcaveOn ℝ D lagrangianRelaxationExampleClosedForm := by
  -- Transfer the strict antitonicity of the explicit derivative to `deriv closedForm`.
  have hantiDeriv :
      StrictAntiOn (deriv lagrangianRelaxationExampleClosedForm) (interior D) := by
    simpa using
      (lagrangianRelaxationExampleClosedFormDeriv_strictAntiOn.congr
        (fun x hx ↦ (lagrangianRelaxationExampleClosedForm_deriv hx).symm))
  have hconv : Convex ℝ (Iio (1 : ℝ)) := convex_Iio (1 : ℝ)
  exact hantiDeriv.strictConcaveOn_of_deriv hconv
    lagrangianRelaxationExampleClosedForm_continuousOn

/-- Helper for Proposition 1.10.12: the derivative of the closed form vanishes at the textbook
critical point `λ_*`. -/
lemma lagrangianRelaxationExampleClosedForm_deriv_eq_zero_at_lambdaStar :
    deriv lagrangianRelaxationExampleClosedForm lagrangianRelaxationExampleLambdaStar = 0 := by
  -- Substitute `1 - λ_* = (1 / 2)^(1 / 3)` and use the cubic identity `((1 / 2)^(1 / 3))^3 = 1/2`.
  have hstar :
      lagrangianRelaxationExampleLambdaStar ∈ D := by
    unfold lagrangianRelaxationExampleLambdaStar
    have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    simpa using sub_lt_self (1 : ℝ) hpos
  rw [lagrangianRelaxationExampleClosedForm_deriv hstar]
  have hr_pos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hr_ne : Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hcube :
      (Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ)) ^ (3 : ℕ) = (1 / 2 : ℝ) := by
    have h := Real.rpow_inv_rpow
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show (3 : ℝ) ≠ 0 by norm_num)
    simpa [one_div, Real.rpow_natCast] using h
  unfold lagrangianRelaxationExampleClosedFormDeriv lagrangianRelaxationExampleLambdaStar
  field_simp [hr_ne]
  nlinarith [hcube]

/-- Helper for Proposition 1.10.12: the textbook critical point `λ_*` is a global maximizer of the
real closed form on `(-∞, 1)`. -/
lemma lagrangianRelaxationExample_closedForm_isMaxOn_lambdaStar :
    IsMaxOn lagrangianRelaxationExampleClosedForm D
      lagrangianRelaxationExampleLambdaStar := by
  -- Use the strict concavity route to make the derivative sign test stable on both sides of `λ_*`.
  have hstar :
      lagrangianRelaxationExampleLambdaStar ∈ D := by
    unfold lagrangianRelaxationExampleLambdaStar
    have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    simpa using sub_lt_self (1 : ℝ) hpos
  have hstarlt : lagrangianRelaxationExampleLambdaStar < 1 := hstar
  have hcontAt :
      ContinuousAt lagrangianRelaxationExampleClosedForm
        lagrangianRelaxationExampleLambdaStar := by
    have hne : 1 - lagrangianRelaxationExampleLambdaStar ≠ 0 := by
      linarith
    change ContinuousAt
      (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
      lagrangianRelaxationExampleLambdaStar
    exact
      (show ContinuousAt
        (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
        lagrangianRelaxationExampleLambdaStar by
        fun_prop (disch := assumption))
  have hdiffLeft :
      DifferentiableOn ℝ lagrangianRelaxationExampleClosedForm
        (Iio lagrangianRelaxationExampleLambdaStar) := by
    intro x hx
    exact
      (lagrangianRelaxationExampleClosedForm_differentiableAt
        (show x ∈ D from lt_trans hx hstarlt)).differentiableWithinAt
  have hdiffRight :
      DifferentiableOn ℝ lagrangianRelaxationExampleClosedForm
        (Ioo lagrangianRelaxationExampleLambdaStar 1) := by
    intro x hx
    exact (lagrangianRelaxationExampleClosedForm_differentiableAt hx.2).differentiableWithinAt
  have hanti :
      AntitoneOn (deriv lagrangianRelaxationExampleClosedForm) D := by
    exact lagrangianRelaxationExample_closedForm_strictConcaveOn.concaveOn.antitoneOn_deriv
      (fun x hx ↦ lagrangianRelaxationExampleClosedForm_differentiableAt hx)
  refine isMaxOn_Iio_of_deriv hcontAt hdiffLeft hdiffRight ?_ ?_
  · intro x hx
    -- To the left of `λ_*`, antitonicity forces `φ'(x) ≥ φ'(λ_*) = 0`.
    have hxD : x ∈ D := by
      exact lt_trans hx hstarlt
    have hle :=
      hanti hxD hstar hx.le
    simpa [lagrangianRelaxationExampleClosedForm_deriv_eq_zero_at_lambdaStar,
      lagrangianRelaxationExampleClosedForm_deriv hxD] using hle
  · intro x hx
    -- To the right of `λ_*`, the same antitonicity gives `φ'(x) ≤ φ'(λ_*) = 0`.
    have hle := hanti hstar hx.2 hx.1.le
    simpa [lagrangianRelaxationExampleClosedForm_deriv_eq_zero_at_lambdaStar,
      lagrangianRelaxationExampleClosedForm_deriv hx.2] using hle

-- Proof sketch: compute the first and second derivatives of `ψ` on `(-∞, 1)`, deduce strict
-- concavity from `ψ''(λ) < 0`, and solve the critical-point equation to identify the unique
-- maximizer.
/-- Proposition 1.10.12: a scalar `λ` lies in `(-∞, 1)` and is a global maximizer of the example
dual function on that interval exactly when `λ = 1 - (1 / 2)^(1 / 3)`. -/
theorem lagrangianRelaxationExample_dualFunction_isMaxOn_iff
    (lam : ℝ) :
    lam ∈ D ∧ IsMaxOn ψ D lam ↔
      lam = lagrangianRelaxationExampleLambdaStar := by
  constructor
  · rintro ⟨h_lam, hmax⟩
    -- Transport the maximizer statement to the real closed form and use strict concavity.
    have hmaxClosed :
        IsMaxOn lagrangianRelaxationExampleClosedForm D lam :=
      (lagrangianRelaxationExample_closedForm_isMaxOn_iff h_lam).1 hmax
    have hstar :
        lagrangianRelaxationExampleLambdaStar ∈ D := by
      unfold lagrangianRelaxationExampleLambdaStar
      have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
        exact Real.rpow_pos_of_pos (by norm_num) _
      simpa using sub_lt_self (1 : ℝ) hpos
    have hstarlt : lagrangianRelaxationExampleLambdaStar < 1 := hstar
    exact lagrangianRelaxationExample_closedForm_strictConcaveOn.eq_of_isMaxOn
      hmaxClosed
      lagrangianRelaxationExample_closedForm_isMaxOn_lambdaStar
      h_lam
      hstar
  · intro hlam
    constructor
    · -- The explicit formula for `λ_*` visibly lies in `(-∞, 1)`.
      subst hlam
      unfold lagrangianRelaxationExampleLambdaStar
      have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
        exact Real.rpow_pos_of_pos (by norm_num) _
      simpa using sub_lt_self (1 : ℝ) hpos
    · -- Push the real closed-form maximizer back to the owner-side `EReal` dual function.
      subst hlam
      exact (lagrangianRelaxationExample_closedForm_isMaxOn_iff (by
        unfold lagrangianRelaxationExampleLambdaStar
        have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
          exact Real.rpow_pos_of_pos (by norm_num) _
        simpa using sub_lt_self (1 : ℝ) hpos)).2
          lagrangianRelaxationExample_closedForm_isMaxOn_lambdaStar

/-- The scalar maximizer `λ_*` lies in the effective dual domain `(-∞, 1)`. -/
theorem lagrangianRelaxationExampleLambdaStar_lt_one :
    lagrangianRelaxationExampleLambdaStar < 1 := by
  change lagrangianRelaxationExampleLambdaStar ∈ Iio (1 : ℝ)
  exact
    ((lagrangianRelaxationExample_dualFunction_isMaxOn_iff
      lagrangianRelaxationExampleLambdaStar).2 rfl).1

/-- The owner multiplier `single 0 λ_*` lies in the dual-feasible set. -/
theorem lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet :
    single 0 lagrangianRelaxationExampleLambdaStar ∈
      lagrangianRelaxationExample.dualFeasibleSet := by
  rw [lagrangianRelaxationExample.mem_dualFeasibleSet_iff]
  constructor
  · -- Dual-domain membership is the scalar inequality `λ_* < 1`.
    exact (lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff
      lagrangianRelaxationExampleLambdaStar).2 lagrangianRelaxationExampleLambdaStar_lt_one
  · intro j
    fin_cases j
    -- The nonnegativity condition follows from `(1 / 2)^(1 / 3) ≤ 1`.
    have hrpow_le_one :
        Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) ≤ 1 := by
      have hmono :=
        Real.monotoneOn_rpow_Ici_of_exponent_nonneg (show 0 ≤ (1 / 3 : ℝ) by norm_num)
      simpa using hmono
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Ici 0)
        (by norm_num : (1 : ℝ) ∈ Set.Ici 0)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    unfold lagrangianRelaxationExampleLambdaStar
    simpa using sub_nonneg.mpr hrpow_le_one

/-- The owner multiplier `single 0 λ_*` maximizes the example dual function on the dual-feasible
set. -/
theorem lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet :
    IsMaxOn lagrangianRelaxationExample.dualFunction
      lagrangianRelaxationExample.dualFeasibleSet
      (single 0 lagrangianRelaxationExampleLambdaStar) := by
  rw [isMaxOn_iff]
  intro μ hμ
  -- Every one-dimensional multiplier is determined by its unique coordinate.
  have hμ_eq : μ = single 0 (μ 0) := by
    ext i
    fin_cases i
    simp
  have hμ_dom :
      μ ∈ lagrangianRelaxationExample.dualDomain :=
    (lagrangianRelaxationExample.mem_dualFeasibleSet_iff.mp hμ).1
  have hscalar : μ 0 < 1 := by
    have hscalarDom : single 0 (μ 0) ∈ lagrangianRelaxationExample.dualDomain := by
      rwa [hμ_eq]
    exact (lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff (μ 0)).1 hscalarDom
  have hscalarMax :
      IsMaxOn ψ D lagrangianRelaxationExampleLambdaStar :=
    ((lagrangianRelaxationExample_dualFunction_isMaxOn_iff
      lagrangianRelaxationExampleLambdaStar).2 rfl).2
  -- Reduce the owner comparison to the scalar comparison supplied by the maximizer theorem.
  have hleScalar :
      ψ (μ 0) ≤ ψ lagrangianRelaxationExampleLambdaStar :=
    (isMaxOn_iff.mp hscalarMax) (μ 0) hscalar
  rw [hμ_eq]
  simpa [Function.comp_apply] using hleScalar

-- Proof sketch: substitute `λ_* = 1 - (1 / 2)^(1 / 3)` into the explicit trajectory formula
-- `x(λ) = (1 - λ, (1 - λ)⁻¹)` and simplify both coordinates.
/-- The textbook trajectory evaluated at `λ_*` has coordinates `(2^(-1 / 3), 2^(1 / 3))`. -/
theorem lagrangianRelaxationExampleTrajectory_atLambdaStar :
    lagrangianRelaxationExampleMinimizerTrajectory lagrangianRelaxationExampleLambdaStar =
      WithLp.toLp 2
        ![Real.rpow (2 : ℝ) (-(1 / 3 : ℝ)),
          Real.rpow (2 : ℝ) (1 / 3 : ℝ)] := by
  -- Evaluate the explicit trajectory coordinatewise at `λ_*`.
  ext i
  fin_cases i
  · have hcoord :
        1 - lagrangianRelaxationExampleLambdaStar =
          Real.rpow (2 : ℝ) (-(1 / 3 : ℝ)) := by
      unfold lagrangianRelaxationExampleLambdaStar
      ring_nf
      convert (Real.rpow_neg_eq_inv_rpow (2 : ℝ) ((3 : ℝ)⁻¹)).symm using 1 <;> norm_num
    simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hcoord
  · have hcoord :
        1 / (1 - lagrangianRelaxationExampleLambdaStar) =
          Real.rpow (2 : ℝ) (1 / 3 : ℝ) := by
      unfold lagrangianRelaxationExampleLambdaStar
      ring_nf
      simpa [one_div] using congrArg Inv.inv
        (Real.inv_rpow (show 0 ≤ (2 : ℝ) by positivity) (1 / 3 : ℝ))
    simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hcoord
