/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- The candidate function `t ↦ exp (-|t|^α)` appearing in Exercise 15.4.3. -/
noncomputable def phi_alpha (α : ℝ) : ℝ → ℂ :=
  fun t ↦ Complex.exp (-(Real.rpow |t| α))

-- Proof sketch: evaluate the defining formula for `phi_alpha` at `t = 0`, use `|0| = 0`,
-- `Real.zero_rpow` for positive exponent, and `Complex.exp_zero`.
/-- The function `phi_alpha` is normalized at the origin when `α` is positive. -/
theorem phi_alpha_zero (α : ℝ) (hα : 0 < α) :
    phi_alpha α 0 = 1 := by
  -- Evaluate the defining expression at `0` and collapse the real power term.
  simp [phi_alpha, Real.zero_rpow hα.ne']

/-- Helper for Exercise 15.4.3: the real part of `phi_alpha α t` is the real exponential
`exp (-|t|^α)`. -/
lemma phiAlphaRealPart (α t : ℝ) :
    Complex.re (phi_alpha α t) = Real.exp (-(Real.rpow |t| α)) := by
  -- The exponent is real, so taking the real part just removes the complex coercion.
  simpa [phi_alpha] using Complex.exp_ofReal_re (-(Real.rpow |t| α))

/-- Helper for Exercise 15.4.3: every real probability characteristic function satisfies the
doubling-defect bound `1 - Re φ(2t) ≤ 4 (1 - Re φ(t))`. -/
lemma oneSubReCharFun_double_le_four_mul {μ : Measure ℝ} [IsProbabilityMeasure μ] (t : ℝ) :
    1 - Complex.re (charFun μ (2 * t)) ≤ 4 * (1 - Complex.re (charFun μ t)) := by
  have hint₂ : Integrable (BoundedContinuousFunction.innerProbChar (2 * t)) μ :=
    BoundedContinuousFunction.integrable μ _
  have hint₁ : Integrable (BoundedContinuousFunction.innerProbChar t) μ :=
    BoundedContinuousFunction.integrable μ _
  have hcos₂ : Integrable (fun x ↦ Real.cos (inner ℝ x (2 * t))) μ := by
    convert hint₂.re using 1
    funext x
    rw [BoundedContinuousFunction.innerProbChar_apply]
    simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re (inner ℝ x (2 * t))).symm
  have hcos₁ : Integrable (fun x ↦ Real.cos (inner ℝ x t)) μ := by
    convert hint₁.re using 1
    funext x
    rw [BoundedContinuousFunction.innerProbChar_apply]
    simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re (inner ℝ x t)).symm
  have hre₂ :
      Complex.re (charFun μ (2 * t)) = ∫ x, Real.cos (inner ℝ x (2 * t)) ∂μ := by
    rw [charFun_eq_integral_innerProbChar]
    calc
      Complex.re (∫ x, BoundedContinuousFunction.innerProbChar (2 * t) x ∂μ)
        = ∫ x, Complex.re (BoundedContinuousFunction.innerProbChar (2 * t) x) ∂μ := by
            simpa using (integral_re hint₂).symm
      _ = ∫ x, Real.cos (inner ℝ x (2 * t)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [BoundedContinuousFunction.innerProbChar_apply]
            simpa [mul_comm] using Complex.exp_ofReal_mul_I_re (inner ℝ x (2 * t))
  have hre₁ : Complex.re (charFun μ t) = ∫ x, Real.cos (inner ℝ x t) ∂μ := by
    rw [charFun_eq_integral_innerProbChar]
    calc
      Complex.re (∫ x, BoundedContinuousFunction.innerProbChar t x ∂μ)
        = ∫ x, Complex.re (BoundedContinuousFunction.innerProbChar t x) ∂μ := by
            simpa using (integral_re hint₁).symm
      _ = ∫ x, Real.cos (inner ℝ x t) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [BoundedContinuousFunction.innerProbChar_apply]
            simpa [mul_comm] using Complex.exp_ofReal_mul_I_re (inner ℝ x t)
  have hleft :
      1 - Complex.re (charFun μ (2 * t)) =
        ∫ x, 1 - Real.cos (inner ℝ x (2 * t)) ∂μ := by
    -- Rewrite the defect as the integral of the pointwise cosine defect.
    calc
      1 - Complex.re (charFun μ (2 * t))
        = ∫ x, (1 : ℝ) ∂μ - ∫ x, Real.cos (inner ℝ x (2 * t)) ∂μ := by rw [hre₂]; simp
      _ = ∫ x, 1 - Real.cos (inner ℝ x (2 * t)) ∂μ := by
        rw [← integral_sub (integrable_const 1) hcos₂]
  have hright :
      1 - Complex.re (charFun μ t) =
        ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by
    -- The same rewrite at frequency `t` gives the right-hand comparison target.
    calc
      1 - Complex.re (charFun μ t)
        = ∫ x, (1 : ℝ) ∂μ - ∫ x, Real.cos (inner ℝ x t) ∂μ := by rw [hre₁]; simp
      _ = ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by
        rw [← integral_sub (integrable_const 1) hcos₁]
  have hpoint :
      ∀ x, 1 - Real.cos (inner ℝ x (2 * t)) ≤ 4 * (1 - Real.cos (inner ℝ x t)) := by
    intro x
    have hinner_eq : inner ℝ x (2 * t) = 2 * inner ℝ x t := by
      rw [show (2 * t : ℝ) = (2 : ℝ) • t by simp, real_inner_smul_right]
    rw [hinner_eq, Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (inner ℝ x t) - 1)]
  rw [hleft]
  calc
    ∫ x, 1 - Real.cos (inner ℝ x (2 * t)) ∂μ
      ≤ ∫ x, 4 * (1 - Real.cos (inner ℝ x t)) ∂μ := by
          refine integral_mono ((integrable_const 1).sub hcos₂)
            (((integrable_const 1).sub hcos₁).const_mul 4) hpoint
    _ = 4 * ∫ x, 1 - Real.cos (inner ℝ x t) ∂μ := by rw [integral_const_mul]
    _ = 4 * (1 - Complex.re (charFun μ t)) := by rw [← hright]

/-- Helper for Exercise 15.4.3: for `α > 2`, the function `phi_alpha α` violates the universal
doubling-defect inequality satisfied by characteristic functions. -/
lemma exists_phiAlphaDoublingCounterexample (α : ℝ) (hα : 2 < α) :
    ∃ t : ℝ, 4 * (1 - Complex.re (phi_alpha α t)) <
      1 - Complex.re (phi_alpha α (2 * t)) := by
  have hα0 : 0 < α := by linarith
  let c : ℝ := Real.rpow 2 α
  have hc : 4 < c := by
    have htwo_lt : 1 < (2 : ℝ) := by norm_num
    have hfour_rpow : (4 : ℝ) = Real.rpow 2 2 := by norm_num
    have hc' := Real.rpow_lt_rpow_of_exponent_lt htwo_lt hα
    simpa [c, hfour_rpow] using hc'
  have hc0 : 0 < c := by linarith
  let u : ℝ := (c - 4) / (2 * c ^ 2)
  have hu : 0 < u := by
    have hc4 : 0 < c - 4 := by linarith
    dsimp [u]
    positivity
  let t : ℝ := u ^ (α⁻¹ : ℝ)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_rpow : Real.rpow t α = u := by
    -- The choice `t = u^(1/α)` turns `|t|^α` back into the small parameter `u`.
    simpa [t] using Real.rpow_inv_rpow hu.le hα0.ne'
  have habs_t_pow : Real.rpow |t| α = u := by
    rw [abs_of_nonneg ht_nonneg]
    exact ht_rpow
  have habs_two_t_pow : Real.rpow |2 * t| α = c * u := by
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by positivity
    calc
      Real.rpow |2 * t| α = Real.rpow (2 * t) α := by
        rw [abs_of_nonneg]
        positivity
      _ = Real.rpow 2 α * Real.rpow t α := by
        simpa using (Real.mul_rpow (z := α) htwo_nonneg ht_nonneg : (2 * t) ^ α = 2 ^ α * t ^ α)
      _ = c * u := by
        rw [ht_rpow]
  have hcu_nonneg : 0 ≤ c * u := by positivity
  have hcu_le : c * u ≤ 1 := by
    -- This explicit `u` keeps the large-frequency defect within the radius where the quadratic
    -- lower bound for the exponential remainder is valid.
    dsimp [u]
    field_simp [hc0.ne']
    nlinarith
  have hUpper : 1 - Real.exp (-u) ≤ u := by
    linarith [Real.one_sub_le_exp_neg u]
  have hLower :
      c * u - (c * u) ^ 2 ≤ 1 - Real.exp (-(c * u)) := by
    -- The second-order remainder estimate supplies the lower bound at frequency `2 * t`.
    have hApprox : |Real.exp (-(c * u)) - 1 + c * u| ≤ (-(c * u)) ^ 2 := by
      have hAbs : |-(c * u)| ≤ 1 := by
        simpa [abs_of_nonneg hcu_nonneg] using hcu_le
      simpa using Real.abs_exp_sub_one_sub_id_le (x := -(c * u)) hAbs
    have hRight := (abs_le.mp hApprox).2
    nlinarith
  have hGap : 4 * u < c * u - (c * u) ^ 2 := by
    -- The chosen `u` makes the defect ratio exceed `4`.
    dsimp [u]
    field_simp [hc0.ne']
    nlinarith
  refine ⟨t, ?_⟩
  rw [phiAlphaRealPart, phiAlphaRealPart]
  rw [habs_t_pow, habs_two_t_pow]
  have hUpper4 : 4 * (1 - Real.exp (-u)) ≤ 4 * u := by
    gcongr
  linarith

-- Proof sketch: assume `charFun μ = phi_alpha α`, use the second-order expansion of
-- characteristic functions with finite second moment to identify the quadratic coefficient with the
-- variance, then compare with the flatter-than-quadratic behavior of `exp (-|t|^α)` at `0` when
-- `α > 2` to deduce zero variance and hence degeneracy, contradicting the nontrivial expansion.
/-- Exercise 15.4.3: for `α > 2`, the function `φ_α(t) = exp (-|t|^α)` is not the characteristic
function of a probability measure on `ℝ`. -/
theorem not_exists_probabilityMeasure_charFun_eq_phi_alpha (α : ℝ) (hα : 2 < α) :
    ¬ ∃ μ : ProbabilityMeasure ℝ, charFun (μ : Measure ℝ) = phi_alpha α := by
  -- Route correction: instead of the second-moment route, use the universal doubling inequality
  -- for characteristic functions and an explicit small-frequency violation for `phi_alpha`.
  rintro ⟨μ, hμ⟩
  obtain ⟨t, ht⟩ := exists_phiAlphaDoublingCounterexample α hα
  have hdouble :
      1 - Complex.re (charFun (μ : Measure ℝ) (2 * t)) ≤
        4 * (1 - Complex.re (charFun (μ : Measure ℝ) t)) :=
    oneSubReCharFun_double_le_four_mul (μ := (μ : Measure ℝ)) t
  rw [show charFun (μ : Measure ℝ) (2 * t) = phi_alpha α (2 * t) from congrFun hμ (2 * t),
    show charFun (μ : Measure ℝ) t = phi_alpha α t from congrFun hμ t] at hdouble
  exact not_lt_of_ge hdouble ht
