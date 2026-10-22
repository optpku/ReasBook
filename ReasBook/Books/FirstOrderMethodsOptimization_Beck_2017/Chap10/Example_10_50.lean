/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_45
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_46

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)

noncomputable section

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/- Example 10.50 is `source-facing`: the textbook gives the scalar two-term log-sum-exp smoothing
of `|x|`. The chapter owner for this construction is already Example 10.45's
`shifted_log_sum_exp_smoothing` on coordinatewise maxima, and the corresponding `log 2`
error-parameter owner is its canonical cardinality parameter `log_cardinality_posreal`
specialized to `n = 2`. This file therefore keeps only the scalar specialization and its
source-facing parameter statements, rather than a second independent log-sum-exp owner or a local
duplicate of the `log 2` package. The intrinsic target function is the canonical absolute value
`abs : ℝ → ℝ`, not a local wrapper. -/

/-- The two-term shifted log-sum-exp smoothing
`x ↦ μ log (e^{x / μ} + e^{-x / μ}) - μ log 2` of the absolute value. -/
def absolute_value_log_sum_exp_smoothing (μ : PosReal) : ℝ → ℝ :=
  fun x ↦ shifted_log_sum_exp_smoothing μ (toLp 2 ![x, -x] : E₂)

/-- Evaluating `absolute_value_log_sum_exp_smoothing μ` at `x` gives the shifted two-term
log-sum-exp formula from Example 10.50. -/
@[simp] theorem absolute_value_log_sum_exp_smoothing_apply (μ : PosReal) (x : ℝ) :
    absolute_value_log_sum_exp_smoothing μ x =
      (μ : ℝ) * Real.log (Real.exp (x / (μ : ℝ)) + Real.exp (-x / (μ : ℝ))) -
        (μ : ℝ) * Real.log 2 := by
  simpa [absolute_value_log_sum_exp_smoothing] using
    shifted_log_sum_exp_smoothing_apply μ (toLp 2 ![x, -x] : E₂)

/-- Helper for Example 10.50: the coordinatewise maximum of the pair `(x, -x)` is `|x|`. -/
lemma coordinatewiseMax_pair_eq_abs (x : ℝ) :
    coordinatewiseMax (toLp 2 ![x, -x] : E₂) = abs x := by
  -- For two coordinates, the supremum is exactly the maximum of `x` and `-x`.
  rw [coordinatewiseMax, ← Finset.sup'_univ_eq_ciSup]
  change ({0, 1} : Finset (Fin 2)).sup' (by simp)
      (fun i : Fin 2 ↦ (toLp 2 ![x, -x] : E₂) i) = abs x
  simpa [abs_eq_max_neg]

/-- Helper for Example 10.50: the scalar smoothing rewrites as `μ log(cosh (x / μ))`. -/
lemma absolute_value_log_sum_exp_smoothing_eq_mul_log_cosh
    (μ : PosReal) (x : ℝ) :
    absolute_value_log_sum_exp_smoothing μ x =
      (μ : ℝ) * Real.log (Real.cosh (x / (μ : ℝ))) := by
  -- Rewrite the two exponentials as `2 * cosh`, then cancel the `log 2` shift.
  rw [absolute_value_log_sum_exp_smoothing_apply]
  have hcosh :
      Real.exp (x / (μ : ℝ)) + Real.exp (-x / (μ : ℝ)) =
        2 * Real.cosh (x / (μ : ℝ)) := by
    rw [Real.cosh_eq]
    ring
  rw [hcosh, Real.log_mul (by norm_num) (Real.cosh_pos _).ne']
  ring

/-- Helper for Example 10.50: the derivative of the scalar smoothing is `tanh (x / μ)`. -/
lemma absolute_value_log_sum_exp_smoothing_hasDerivAt
    (μ : PosReal) (x : ℝ) :
    HasDerivAt
      (absolute_value_log_sum_exp_smoothing μ)
      (Real.tanh (x / (μ : ℝ)))
      x := by
  -- Differentiate the `μ log(cosh (x / μ))` representation.
  have harg :
      HasDerivAt
        (fun y : ℝ ↦ y / (μ : ℝ))
        ((μ : ℝ)⁻¹)
        x := by
    simpa [one_div] using (hasDerivAt_id x).div_const (μ : ℝ)
  have hlog :
      HasDerivAt
        (fun y : ℝ ↦ Real.log (Real.cosh (y / (μ : ℝ))))
        ((Real.sinh (x / (μ : ℝ)) * (μ : ℝ)⁻¹) / Real.cosh (x / (μ : ℝ)))
        x := by
    -- The inner `cosh` term stays positive, so the logarithm rule applies globally.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (harg.cosh.log (Real.cosh_pos _).ne')
  have hmul :
      HasDerivAt
        (fun y : ℝ ↦ (μ : ℝ) * Real.log (Real.cosh (y / (μ : ℝ))))
        ((μ : ℝ) * (((Real.sinh (x / (μ : ℝ)) * (μ : ℝ)⁻¹) / Real.cosh (x / (μ : ℝ)))))
        x := by
    exact hlog.const_mul (μ : ℝ)
  have hfun :
      absolute_value_log_sum_exp_smoothing μ =
        fun y : ℝ ↦ (μ : ℝ) * Real.log (Real.cosh (y / (μ : ℝ))) := by
    funext y
    exact absolute_value_log_sum_exp_smoothing_eq_mul_log_cosh μ y
  rw [hfun]
  convert hmul using 1
  simp [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, (PosReal.coe_pos μ).ne',
    mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 10.50: the derivative formula is the pointwise derivative of the smoothing. -/
lemma absolute_value_log_sum_exp_smoothing_deriv_eq
    (μ : PosReal) (x : ℝ) :
    deriv (absolute_value_log_sum_exp_smoothing μ) x =
      Real.tanh (x / (μ : ℝ)) := by
  -- Read off the derivative from the previously established `HasDerivAt` formula.
  exact (absolute_value_log_sum_exp_smoothing_hasDerivAt μ x).deriv

/-- Helper for Example 10.50: the derivative field itself has derivative `μ⁻¹ / cosh(x / μ)^2`. -/
lemma absolute_value_log_sum_exp_smoothing_deriv_hasDerivAt
    (μ : PosReal) (x : ℝ) :
    HasDerivAt
      (deriv (absolute_value_log_sum_exp_smoothing μ))
      ((μ : ℝ)⁻¹ / Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ))
      x := by
  -- Differentiate `tanh (x / μ)` through the quotient `sinh / cosh`.
  have harg :
      HasDerivAt
        (fun y : ℝ ↦ y / (μ : ℝ))
        ((μ : ℝ)⁻¹)
        x := by
    simpa [one_div] using (hasDerivAt_id x).div_const (μ : ℝ)
  have hsinh :
      HasDerivAt
        (fun y : ℝ ↦ Real.sinh (y / (μ : ℝ)))
        (Real.cosh (x / (μ : ℝ)) * (μ : ℝ)⁻¹)
        x :=
    harg.sinh
  have hcosh :
      HasDerivAt
        (fun y : ℝ ↦ Real.cosh (y / (μ : ℝ)))
        (Real.sinh (x / (μ : ℝ)) * (μ : ℝ)⁻¹)
        x :=
    harg.cosh
  have hquot :
      HasDerivAt
        (fun y : ℝ ↦ Real.sinh (y / (μ : ℝ)) / Real.cosh (y / (μ : ℝ)))
        (((Real.cosh (x / (μ : ℝ)) * (μ : ℝ)⁻¹) * Real.cosh (x / (μ : ℝ)) -
            Real.sinh (x / (μ : ℝ)) * (Real.sinh (x / (μ : ℝ)) * (μ : ℝ)⁻¹)) /
          Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ))
        x := by
    exact hsinh.div hcosh (Real.cosh_pos _).ne'
  have hfun :
      deriv (absolute_value_log_sum_exp_smoothing μ) =
        fun y : ℝ ↦ Real.sinh (y / (μ : ℝ)) / Real.cosh (y / (μ : ℝ)) := by
    funext y
    rw [absolute_value_log_sum_exp_smoothing_deriv_eq, Real.tanh_eq_sinh_div_cosh]
  rw [hfun]
  convert hquot using 1
  field_simp [pow_two, Real.cosh_sq_sub_sinh_sq, (PosReal.coe_pos μ).ne']
  simpa using (Real.cosh_sq_sub_sinh_sq (x / (μ : ℝ))).symm

/-- Helper for Example 10.50: the second derivative is `μ⁻¹ / cosh(x / μ)^2`. -/
lemma absolute_value_log_sum_exp_smoothing_second_deriv_eq
    (μ : PosReal) (x : ℝ) :
    deriv (deriv (absolute_value_log_sum_exp_smoothing μ)) x =
      (μ : ℝ)⁻¹ / Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ) := by
  -- Read off the second derivative from the `HasDerivAt` computation of the first derivative.
  exact (absolute_value_log_sum_exp_smoothing_deriv_hasDerivAt μ x).deriv

/-- Helper for Example 10.50: on the real line, an `L`-smooth function has an `L`-Lipschitz
ordinary derivative. -/
lemma lipschitzWith_deriv_of_is_l_smooth_on_real
    {f : ℝ → ℝ} {L : NNReal}
    (hs : is_l_smooth_on f Set.univ L) :
    LipschitzWith L (deriv f) := by
  -- Rewrite the Fréchet derivative as `toSpanSingleton (deriv f x)` and simplify the norm bound.
  rw [is_l_smooth_on_iff] at hs
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have hderiv := hs.2 x (by simp) y (by simp)
  have hfderiv_sub :
      fderiv ℝ f x - fderiv ℝ f y =
        ContinuousLinearMap.toSpanSingleton ℝ (deriv f x - deriv f y) := by
    ext z
    simp [sub_eq_add_neg, smul_sub]
  have hspan :
      ‖ContinuousLinearMap.toSpanSingleton ℝ (deriv f x - deriv f y)‖ ≤
        (L : ℝ) * ‖x - y‖ := by
    simpa [hfderiv_sub] using hderiv
  simpa using hspan

/-- Helper for Example 10.50: if the derivative is `L`-Lipschitz on `ℝ`, then the original
function is `L`-smooth in the Chapter 5 sense. -/
lemma is_l_smooth_on_of_lipschitzWith_deriv_real
    {f : ℝ → ℝ} {L : NNReal}
    (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (deriv f)) :
    is_l_smooth_on f Set.univ L := by
  -- Rewrite the scalar derivative as a one-dimensional Fréchet derivative via `toSpanSingleton`.
  rw [is_l_smooth_on_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hdiff x
  · intro x hx y hy
    have hscalar : ‖deriv f x - deriv f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa using hlip.norm_sub_le x y
    have hfderiv_sub :
        fderiv ℝ f x - fderiv ℝ f y =
          ContinuousLinearMap.toSpanSingleton ℝ (deriv f x - deriv f y) := by
      ext z
      simp [sub_eq_add_neg, smul_sub]
    have hspan :
        ‖ContinuousLinearMap.toSpanSingleton ℝ (deriv f x - deriv f y)‖ ≤
          (L : ℝ) * ‖x - y‖ := by
      simpa using hscalar
    simpa [hfderiv_sub] using hspan

/-- Helper for Example 10.50: the affine pair map `x ↦ (x, -x)` as a linear map into `ℝ²`. -/
lemma pair_linear_map_linear_map_add (x y : ℝ) :
    (toLp 2 ![x + y, -(x + y)] : E₂) =
      (toLp 2 ![x, -x] : E₂) + (toLp 2 ![y, -y] : E₂) := by
  -- Coordinatewise addition on the pair matches addition in `EuclideanSpace`.
  ext i
  fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Example 10.50: the pair map is homogeneous. -/
lemma pair_linear_map_linear_map_smul (c x : ℝ) :
    (toLp 2 ![c * x, -(c * x)] : E₂) = c • (toLp 2 ![x, -x] : E₂) := by
  -- Coordinatewise scalar multiplication on the pair matches scalar multiplication in `ℝ²`.
  ext i
  fin_cases i <;> simp [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 10.50: the squared norm of the pair map is `2 x²`. -/
lemma pair_linear_map_norm_sq (x : ℝ) :
    ‖(toLp 2 ![x, -x] : E₂)‖ ^ (2 : ℕ) = 2 * x ^ (2 : ℕ) := by
  -- Expand the Euclidean norm squared coordinatewise and simplify the two coordinates.
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num
  ring

/-- Helper for Example 10.50: the pair map is bounded by `√2`. -/
lemma pair_linear_map_bound (x : ℝ) :
    ‖(toLp 2 ![x, -x] : E₂)‖ ≤ Real.sqrt 2 * ‖x‖ := by
  -- Compare the squares of both sides; the exact squared norm is `2 x²`.
  have hsq :
      ‖(toLp 2 ![x, -x] : E₂)‖ ^ (2 : ℕ) =
        (Real.sqrt 2 * ‖x‖) ^ (2 : ℕ) := by
    rw [pair_linear_map_norm_sq]
    have hsqrt : (Real.sqrt 2) ^ (2 : ℕ) = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [pow_two, mul_pow, hsqrt]
    have hnorm_sq : ‖x‖ ^ (2 : ℕ) = x ^ (2 : ℕ) := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [hnorm_sq]
    ring
  have hleft_nonneg : 0 ≤ ‖(toLp 2 ![x, -x] : E₂)‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ Real.sqrt 2 * ‖x‖ := by positivity
  exact (sq_le_sq₀ hleft_nonneg hright_nonneg).1 hsq.le

/-- Helper for Example 10.50: the linear part of the affine pair map. -/
def pair_linear_map_linear : ℝ →ₗ[ℝ] E₂ where
  toFun := fun x ↦ toLp 2 ![x, -x]
  map_add' := pair_linear_map_linear_map_add
  map_smul' := pair_linear_map_linear_map_smul

/-- Helper for Example 10.50: the continuous linear pair map `x ↦ (x, -x)`. -/
def pair_linear_map : ℝ →L[ℝ] E₂ :=
  pair_linear_map_linear.mkContinuous (Real.sqrt 2) pair_linear_map_bound

/-- Helper for Example 10.50: evaluating the continuous pair map recovers `(x, -x)`. -/
@[simp] theorem pair_linear_map_apply (x : ℝ) :
    pair_linear_map x = (toLp 2 ![x, -x] : E₂) :=
  rfl

/-- Helper for Example 10.50: the pair map has operator norm squared equal to `2`. -/
lemma pair_linear_opNorm_sq :
    ‖pair_linear_map‖₊ ^ (2 : ℕ) = 2 := by
  -- The upper bound comes from the explicit `√2` estimate, and testing at `x = 1` gives equality.
  apply NNReal.eq
  have hop_le : ‖pair_linear_map‖ ≤ Real.sqrt 2 := by
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) pair_linear_map_bound
  have hunit : ‖(1 : ℝ)‖ ≤ 1 := by simp
  have hop_ge :
      Real.sqrt 2 ≤ ‖pair_linear_map‖ := by
    have htest : ‖pair_linear_map 1‖ = Real.sqrt 2 := by
      have hsq :
          ‖pair_linear_map 1‖ ^ (2 : ℕ) = (Real.sqrt 2) ^ (2 : ℕ) := by
        rw [pair_linear_map_apply, pair_linear_map_norm_sq]
        norm_num [pow_two]
      have hleft_nonneg : 0 ≤ ‖pair_linear_map 1‖ := norm_nonneg _
      have hright_nonneg : 0 ≤ Real.sqrt 2 := by positivity
      exact sq_eq_sq₀ hleft_nonneg hright_nonneg |>.1 hsq
    calc
      Real.sqrt 2 = ‖pair_linear_map 1‖ := htest.symm
      _ ≤ ‖pair_linear_map‖ := by
            simpa using pair_linear_map.unit_le_opNorm 1 hunit
  have hop_eq : ‖pair_linear_map‖ = Real.sqrt 2 := le_antisymm hop_le hop_ge
  rw [NNReal.coe_pow, show ((‖pair_linear_map‖₊ : NNReal) : ℝ) = ‖pair_linear_map‖ by rfl, hop_eq]
  simpa [pow_two] using Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

/-- Helper for Example 10.50: Theorem 10.46 applied to the pair map yields the looser nonnegative
pair `(2, log 2)`. -/
lemma absolute_value_log_sum_exp_smoothing_has_loose_nonneg_bound
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      (abs : ℝ → ℝ)
      (absolute_value_log_sum_exp_smoothing μ)
      2
      (log_cardinality_nonneg (show 0 < 2 by decide))
      μ := by
  -- Apply the affine-precomposition closure theorem to the two-coordinate log-sum-exp owner.
  have hmax :
      (fun x : ℝ ↦ coordinatewiseMax ![x, -x]) = abs := by
    -- After expanding the pair map, the max profile is the scalar absolute value.
    funext x
    simpa using coordinatewiseMax_pair_eq_abs x
  have hsmooth :
      (fun x : ℝ ↦
        (μ : ℝ) * Real.log (Real.exp (x / (μ : ℝ)) + Real.exp (-x / (μ : ℝ))) -
          (μ : ℝ) * Real.log 2) =
        absolute_value_log_sum_exp_smoothing μ := by
    -- The scalar owner is exactly the expanded two-term log-sum-exp formula.
    funext x
    symm
    exact absolute_value_log_sum_exp_smoothing_apply μ x
  simpa [hmax, hsmooth, pair_linear_opNorm_sq] using
    IsSmoothApproximationNonneg.precompose_linearMap_add
      (coordinatewise_max_shifted_log_sum_exp_is_smooth_approximation_nonneg
        (by decide) μ)
      pair_linear_map
      (0 : E₂)

/-- Helper for Example 10.50: the direct one-dimensional second-derivative computation improves
the loose affine-precomposition bound to the exact nonnegative pair `(1, log 2)`. -/
lemma absolute_value_log_sum_exp_smoothing_has_exact_nonneg_bound
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      (abs : ℝ → ℝ)
      (absolute_value_log_sum_exp_smoothing μ)
      1
      (log_cardinality_nonneg (show 0 < 2 by decide))
      μ := by
  -- Keep convexity and the pointwise approximation bounds from the affine-precomposition route,
  -- and replace only the smoothness field by the sharp scalar estimate.
  let hloose := absolute_value_log_sum_exp_smoothing_has_loose_nonneg_bound μ
  have hdiff :
      Differentiable ℝ (absolute_value_log_sum_exp_smoothing μ) := by
    intro x
    exact (absolute_value_log_sum_exp_smoothing_hasDerivAt μ x).differentiableAt
  have hderiv_diff :
      Differentiable ℝ (deriv (absolute_value_log_sum_exp_smoothing μ)) := by
    intro x
    exact (absolute_value_log_sum_exp_smoothing_deriv_hasDerivAt μ x).differentiableAt
  have hderiv_lip :
      LipschitzWith (1 / PosReal.toNNReal μ) (deriv (absolute_value_log_sum_exp_smoothing μ)) := by
    -- The second derivative is nonnegative and bounded above by `1 / μ`.
    refine lipschitzWith_of_nnnorm_deriv_le hderiv_diff ?_
    intro x
    have hμinv_nonneg : 0 ≤ (μ : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (PosReal.coe_pos μ))
    have hcosh_sq_ge_one : 1 ≤ Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ) := by
      nlinarith [Real.one_le_cosh (x / (μ : ℝ))]
    have hsecond_nonneg :
        0 ≤ (μ : ℝ)⁻¹ / Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ) := by
      have hcosh_sq_nonneg : 0 ≤ Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ) := by positivity
      exact div_nonneg hμinv_nonneg hcosh_sq_nonneg
    have hbound :
        (μ : ℝ)⁻¹ / Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ) ≤ (μ : ℝ)⁻¹ := by
      exact div_le_self hμinv_nonneg hcosh_sq_ge_one
    have hbound_real :
        (((‖deriv (deriv (absolute_value_log_sum_exp_smoothing μ)) x‖₊ : NNReal) : ℝ)) ≤
          ((((1 : NNReal) / PosReal.toNNReal μ : NNReal) : ℝ)) := by
      rw [absolute_value_log_sum_exp_smoothing_second_deriv_eq, Real.nnnorm_of_nonneg hsecond_nonneg]
      calc
        (μ : ℝ)⁻¹ / Real.cosh (x / (μ : ℝ)) ^ (2 : ℕ) ≤ (μ : ℝ)⁻¹ := hbound
        _ = ((((1 : NNReal) / PosReal.toNNReal μ : NNReal) : ℝ)) := by
              simp [PosReal.coe_toNNReal, div_eq_mul_inv]
    exact_mod_cast hbound_real
  have hsmooth :
      is_l_smooth_on
        (absolute_value_log_sum_exp_smoothing μ)
        Set.univ
        (1 / PosReal.toNNReal μ) :=
    is_l_smooth_on_of_lipschitzWith_deriv_real hdiff hderiv_lip
  refine ⟨hloose.convex, hloose.lower_le, hloose.upper_le, ?_⟩
  simpa using hsmooth

/-- Helper for Example 10.50: every admissible error parameter dominates the exact scaled gap at
the nonnegative point `x = μ t`. -/
lemma absolute_value_log_sum_exp_beta_lower_at_scale
    {μ α β : PosReal}
    (happrox :
      IsSmoothApproximation
        (abs : ℝ → ℝ)
        (absolute_value_log_sum_exp_smoothing μ)
        α
        β
        μ)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.log 2 - Real.log (1 + Real.exp (-2 * t)) ≤ (β : ℝ) := by
  -- Evaluate the upper approximation inequality at the nonnegative point `x = μ t`.
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_ne : (μ : ℝ) ≠ 0 := hμ_pos.ne'
  have hupper := happrox.upper_le ((μ : ℝ) * t)
  have habs : abs ((μ : ℝ) * t) = (μ : ℝ) * t := by
    rw [abs_of_nonneg]
    positivity
  have hdiv : ((μ : ℝ) * t) / (μ : ℝ) = t := by
    field_simp [hμ_ne]
  have hnegdiv : -(((μ : ℝ) * t) / (μ : ℝ)) = -t := by
    rw [hdiv]
  have hneg_num_div : (-( (μ : ℝ) * t)) / (μ : ℝ) = -t := by
    field_simp [hμ_ne]
  have hlog_split :
      Real.log (Real.exp t + Real.exp (-t)) =
        t + Real.log (1 + Real.exp (-2 * t)) := by
    have hfact :
        Real.exp t * (1 + Real.exp (-2 * t)) =
          Real.exp t + Real.exp (-t) := by
      calc
        Real.exp t * (1 + Real.exp (-2 * t))
            = Real.exp t + Real.exp t * Real.exp (-2 * t) := by ring
        _ = Real.exp t + Real.exp (t + (-2 * t)) := by rw [Real.exp_add]
        _ = Real.exp t + Real.exp (-t) := by congr 1; ring
    rw [← hfact, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  rw [habs, absolute_value_log_sum_exp_smoothing_apply, hdiv, hneg_num_div, hlog_split] at hupper
  have hscaled :
      (μ : ℝ) * t ≤
        (μ : ℝ) * (t + Real.log (1 + Real.exp (-2 * t)) - Real.log 2 + (β : ℝ)) := by
    simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using hupper
  have hplain :
      t ≤ t + Real.log (1 + Real.exp (-2 * t)) - Real.log 2 + (β : ℝ) :=
    le_of_mul_le_mul_left hscaled hμ_pos
  nlinarith

-- Proof sketch: write `|x| = max {x, -x}` and compare with the two-term log-sum-exp smoothing.
-- The lower and upper approximation bounds are the standard log-sum-exp estimates for a maximum,
-- and the smoothness constant comes from the exact second-derivative bound
-- `q_μ''(x) = (1 / μ) * 4 / (e^{x / μ} + e^{-x / μ})^2`, whose supremum is `1 / μ`.
/-- Example 10.50 (1): the shifted two-term log-sum-exp smoothing of `|x|` is a
`1 / μ`-smooth approximation with parameters `(1, log 2)`, encoded by the canonical chapter
owner `log_cardinality_posreal` at `n = 2`. -/
theorem absolute_value_log_sum_exp_smoothing_is_smooth_approximation
    (μ : PosReal) :
    IsSmoothApproximation
      (abs : ℝ → ℝ)
      (absolute_value_log_sum_exp_smoothing μ)
      1
      (log_cardinality_posreal (show 1 < 2 by decide))
      μ := by
  -- Upgrade the exact nonnegative theorem by observing that `log 2` is strictly positive.
  simpa [IsSmoothApproximation, log_cardinality_nonneg, log_cardinality_posreal] using
    absolute_value_log_sum_exp_smoothing_has_exact_nonneg_bound μ

-- Proof sketch: the lower bound `β ≥ log 2` follows from the asymptotic gap
-- `|x| - q_μ(x) → μ log 2`, while `α ≥ 1` follows from the exact second-derivative formula for
-- the smoothing and the resulting optimal Lipschitz constant of the gradient.
/-- Example 10.50 (2): any positive parameter pair yielding this same chapter-level smooth
approximation must satisfy `α ≥ 1` and `β ≥ log 2`. -/
theorem absolute_value_log_sum_exp_smoothing_parameter_lower_bounds
    (μ α β : PosReal)
    (happrox :
      IsSmoothApproximation
        (abs : ℝ → ℝ)
        (absolute_value_log_sum_exp_smoothing μ)
        α
        β
        μ) :
    (1 : ℝ) ≤ (α : ℝ) ∧ Real.log 2 ≤ (β : ℝ) := by
  constructor
  · -- The smoothness field makes the derivative `α / μ`-Lipschitz, so the second derivative at
    -- `0` cannot exceed `α / μ`.
    have hderiv_lip :
        LipschitzWith (PosReal.toNNReal α / PosReal.toNNReal μ)
          (deriv (absolute_value_log_sum_exp_smoothing μ)) :=
      lipschitzWith_deriv_of_is_l_smooth_on_real happrox.smooth
    have hbound :
        ‖deriv (deriv (absolute_value_log_sum_exp_smoothing μ)) 0‖ ≤
          ((PosReal.toNNReal α / PosReal.toNNReal μ : NNReal) : ℝ) := by
      simpa using
        (norm_deriv_le_of_lipschitz hderiv_lip)
    have hsecond :
        ‖deriv (deriv (absolute_value_log_sum_exp_smoothing μ)) 0‖ = (μ : ℝ)⁻¹ := by
      rw [absolute_value_log_sum_exp_smoothing_second_deriv_eq]
      simp [show 0 ≤ (μ : ℝ) by exact le_of_lt (PosReal.coe_pos μ)]
    rw [hsecond, NNReal.coe_div, PosReal.coe_toNNReal, PosReal.coe_toNNReal] at hbound
    have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
    have hmul :
        (μ : ℝ) * (μ : ℝ)⁻¹ ≤ (μ : ℝ) * ((α : ℝ) / (μ : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbound (le_of_lt hμ_pos)
    have hleft : (μ : ℝ) * (μ : ℝ)⁻¹ = 1 := by
      field_simp [(PosReal.coe_pos μ).ne']
    have hright : (μ : ℝ) * ((α : ℝ) / (μ : ℝ)) = (α : ℝ) := by
      field_simp [(PosReal.coe_pos μ).ne']
    rw [hleft, hright] at hmul
    exact hmul
  · -- The exact scaled gap tends to `log 2`, so any valid error parameter must dominate `log 2`.
    let g : ℝ → ℝ := fun t ↦ Real.log 2 - Real.log (1 + Real.exp (-2 * t))
    have hmem :
        ∀ᶠ t : ℝ in Filter.atTop, g t ≤ (β : ℝ) := by
      filter_upwards [Filter.Ici_mem_atTop (0 : ℝ)] with t ht
      exact absolute_value_log_sum_exp_beta_lower_at_scale happrox ht
    have hexp :
        Filter.Tendsto (fun t : ℝ ↦ Real.exp (-2 * t)) Filter.atTop (nhds 0) := by
      have hneg_two :
          Filter.Tendsto (fun t : ℝ ↦ -2 * t) Filter.atTop Filter.atBot := by
        simpa using Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0)
      convert Real.tendsto_exp_atBot.comp hneg_two using 1
    have hlog :
        Filter.Tendsto (fun t : ℝ ↦ Real.log (1 + Real.exp (-2 * t))) Filter.atTop (nhds 0) := by
      have hcont :
          ContinuousAt (fun s : ℝ ↦ Real.log (1 + s)) 0 := by
        simpa using
          (Real.continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)).comp
            (continuousAt_const.add continuousAt_id)
      simpa using hcont.tendsto.comp hexp
    have hlim : Filter.Tendsto g Filter.atTop (nhds (Real.log 2)) := by
      simpa [g] using tendsto_const_nhds.sub hlog
    have hclosed : IsClosed {r : ℝ | r ≤ (β : ℝ)} :=
      isClosed_le continuous_id continuous_const
    have hmem_set :
        ∀ᶠ t : ℝ in Filter.atTop, g t ∈ {r : ℝ | r ≤ (β : ℝ)} := by
      simpa using hmem
    exact hclosed.mem_of_tendsto hlim hmem_set

-- Proof sketch: write `|x| = max {x, -x}` as the maximum of two affine functions and apply the
-- affine-precomposition closure theorem from Theorem 10.46(b). For the map `x ↦ (x, -x)`, the
-- operator-norm square is `2`, so the theorem yields the looser parameter pair `(2, log 2)`,
-- recorded through the chapter owner `log_cardinality_nonneg` specialized at `n = 2`.
/-- The affine-precomposition bound from Theorem 10.46(b) yields the looser nonnegative parameter
pair `(2, log 2)`, encoded by `log_cardinality_nonneg` at `n = 2`, for the same smoothing family. -/
theorem absolute_value_log_sum_exp_smoothing_has_loose_two_log_two_bound
    (μ : PosReal) :
    IsSmoothApproximationNonneg
      (abs : ℝ → ℝ)
      (absolute_value_log_sum_exp_smoothing μ)
      2
      (log_cardinality_nonneg (show 0 < 2 by decide))
      μ := by
  -- This is exactly the affine-precomposition theorem specialized to the pair map.
  exact absolute_value_log_sum_exp_smoothing_has_loose_nonneg_bound μ
