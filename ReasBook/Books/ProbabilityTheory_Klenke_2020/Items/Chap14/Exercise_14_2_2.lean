/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped ENNReal
open MeasureTheory MeasureTheory.Lp ContinuousLinearMap

attribute [local instance] Classical.propDecidable

noncomputable section

universe u₁ u₂

variable {Ω₁ : Type u₁} {Ω₂ : Type u₂}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
variable [SFinite μ₁] [SFinite μ₂]

/-- Helper for Exercise 14.2.2: the squared `L²(μ₁)` norm of the column `a(·, t₂)`. -/
private def columnSquareIntegral (a : Ω₁ × Ω₂ → ℝ) (t₂ : Ω₂) : ℝ :=
  ∫ t₁, a (t₁, t₂) ^ 2 ∂μ₁

/-- Helper for Exercise 14.2.2: the `L²(μ₁)` norm of the column `a(·, t₂)`. -/
private def columnRoot (a : Ω₁ × Ω₂ → ℝ) (t₂ : Ω₂) : ℝ :=
  Real.sqrt (columnSquareIntegral μ₁ a t₂)

-- Proof step: Fubini for `a^2` gives square-integrable columns, and the product-space
-- almost-every strong measurability gives the corresponding columnwise `MemLp` statement.
/-- Helper for Exercise 14.2.2: almost every column of an `L²(μ₁ × μ₂)` kernel belongs to
`L²(μ₁)`. -/
private theorem columnsMemLpAe (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂)) :
    ∀ᵐ t₂ ∂μ₂, MemLp (fun t₁ ↦ a (t₁, t₂)) 2 μ₁ := by
  have h_col_sq : ∀ᵐ t₂ ∂μ₂, Integrable (fun t₁ ↦ a (t₁, t₂) ^ 2) μ₁ :=
    ha.integrable_sq.prod_left_ae
  have h_col_meas : ∀ᵐ t₂ ∂μ₂, AEStronglyMeasurable (fun t₁ ↦ a (t₁, t₂)) μ₁ :=
    ha.aestronglyMeasurable.prodMk_right
  filter_upwards [h_col_sq, h_col_meas] with t₂ hsq hmeas
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 hsq

-- Proof step: integrate the squared kernel on the swapped product space to obtain an
-- almost-every measurable columnwise square integral.
/-- Helper for Exercise 14.2.2: the columnwise square integral is almost everywhere strongly
measurable. -/
private theorem columnSquareIntegral_aestronglyMeasurable (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    AEStronglyMeasurable (columnSquareIntegral μ₁ a) μ₂ := by
  have hswap : AEStronglyMeasurable (fun z : Ω₂ × Ω₁ ↦ a z.swap) (μ₂.prod μ₁) :=
    ha.aestronglyMeasurable.prod_swap
  have hsq : AEStronglyMeasurable (fun z : Ω₂ × Ω₁ ↦ a z.swap ^ 2) (μ₂.prod μ₁) := by
    simpa [sq] using hswap.mul hswap
  simpa [columnSquareIntegral] using hsq.integral_prod_right'

-- Proof step: composing the columnwise square integral with `Real.sqrt` keeps the output
-- almost everywhere strongly measurable.
/-- Helper for Exercise 14.2.2: the columnwise `L²(μ₁)` norm is almost everywhere strongly
measurable on `Ω₂`. -/
private theorem columnRoot_aestronglyMeasurable (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    AEStronglyMeasurable (columnRoot μ₁ a) μ₂ := by
  exact
    (columnSquareIntegral_aestronglyMeasurable μ₁ μ₂ a ha).aemeasurable.sqrt.aestronglyMeasurable

/-- Helper for Exercise 14.2.2: the columnwise `L²(μ₁)` norm is nonnegative. -/
private theorem columnRoot_nonneg (a : Ω₁ × Ω₂ → ℝ) (t₂ : Ω₂) :
    0 ≤ columnRoot μ₁ a t₂ := by
  -- Proof step: `columnRoot` is a square root, so it is automatically nonnegative.
  simp [columnRoot]

/-- Helper for Exercise 14.2.2: squaring the column norm recovers the columnwise square integral. -/
private theorem columnRoot_sq (a : Ω₁ × Ω₂ → ℝ) (t₂ : Ω₂) :
    columnRoot μ₁ a t₂ ^ 2 = columnSquareIntegral μ₁ a t₂ := by
  have hnonneg : 0 ≤ columnSquareIntegral μ₁ a t₂ :=
    integral_nonneg fun _ ↦ by positivity
  -- Proof step: rewrite the square of the square root using the nonnegativity of the integral.
  rw [columnRoot, Real.sq_sqrt hnonneg]

/-- Helper for Exercise 14.2.2: the absolute value of the nonnegative column norm is redundant. -/
private theorem columnRoot_norm (a : Ω₁ × Ω₂ → ℝ) (t₂ : Ω₂) :
    ‖columnRoot μ₁ a t₂‖ = columnRoot μ₁ a t₂ := by
  -- Proof step: the norm of a nonnegative real equals the number itself.
  exact Real.norm_of_nonneg (columnRoot_nonneg μ₁ a t₂)

-- Proof step: Fubini shows that the columnwise square integrals are integrable, and the previous
-- identity turns this into an `L²(μ₂)` statement for the dominating column norm.
/-- Helper for Exercise 14.2.2: the columnwise `L²(μ₁)` norm of an `L²(μ₁ × μ₂)` kernel belongs to
`L²(μ₂)`. -/
private theorem columnRoot_memLp (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂)) :
    MemLp (columnRoot μ₁ a) 2 μ₂ := by
  have h_integral : Integrable (columnSquareIntegral μ₁ a) μ₂ := by
    simpa [columnSquareIntegral, Real.norm_of_nonneg (sq_nonneg _)] using
      ha.integrable_sq.integral_norm_prod_right
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (columnRoot_aestronglyMeasurable μ₁ μ₂ a ha)).2 ?_
  refine h_integral.congr ?_
  filter_upwards with t₂
  rw [← columnRoot_sq μ₁ a t₂]

/-- Helper for Exercise 14.2.2: the raw kernel integral defining the Hilbert--Schmidt operator. -/
private def hilbertSchmidtApply (a : Ω₁ × Ω₂ → ℝ) (f : Ω₁ →₂[μ₁] ℝ) (t₂ : Ω₂) : ℝ :=
  ∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁

-- Route correction: the old rowwise `Ω₁ → L²(μ₂)` route was blocked on measurability of the
-- chosen representative. Integrating directly in the column variable lets product-measure
-- measurability handle the output function.
-- Proof step: work on the swapped product space so that `t₂ ↦ ∫ t₁, ...` is exactly an
-- `integral_prod_right'` output.
/-- Helper for Exercise 14.2.2: the kernel integral output is almost everywhere strongly
measurable. -/
private theorem hilbertSchmidtApply_aestronglyMeasurable (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) (f : Ω₁ →₂[μ₁] ℝ) :
    AEStronglyMeasurable (hilbertSchmidtApply μ₁ a f) μ₂ := by
  have hkernel : AEStronglyMeasurable (fun z : Ω₂ × Ω₁ ↦ a z.swap) (μ₂.prod μ₁) :=
    ha.aestronglyMeasurable.prod_swap
  have hinput : AEStronglyMeasurable (fun z : Ω₂ × Ω₁ ↦ f z.2) (μ₂.prod μ₁) :=
    (Lp.aestronglyMeasurable f).comp_snd
  have hmul : AEStronglyMeasurable (fun z : Ω₂ × Ω₁ ↦ a z.swap * f z.2) (μ₂.prod μ₁) :=
    hkernel.mul hinput
  simpa [hilbertSchmidtApply] using hmul.integral_prod_right'

-- Proof step: on almost every column, apply Cauchy--Schwarz/Hölder to the integrable product
-- `a(·, t₂) * f`.
/-- Helper for Exercise 14.2.2: almost every output value is bounded by the `L²(μ₁)` norm of the
input times the columnwise `L²(μ₁)` norm of the kernel. -/
private theorem operatorApply_bound_ae (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂))
    (f : Ω₁ →₂[μ₁] ℝ) :
    ∀ᵐ t₂ ∂μ₂, ‖hilbertSchmidtApply μ₁ a f t₂‖ ≤ ‖f‖ * columnRoot μ₁ a t₂ := by
  filter_upwards [columnsMemLpAe μ₁ μ₂ a ha] with t₂ hcol
  have hcolReal : MemLp (fun t₁ ↦ a (t₁, t₂)) (ENNReal.ofReal (2 : ℝ)) μ₁ := by
    simpa using hcol
  have hfReal : MemLp (fun t₁ ↦ f t₁) (ENNReal.ofReal (2 : ℝ)) μ₁ := by
    simpa using (Lp.memLp f)
  have hcol_sq :
      ∫ t₁, ‖a (t₁, t₂)‖ ^ (2 : ℝ) ∂μ₁ = ∫ t₁, a (t₁, t₂) ^ 2 ∂μ₁ := by
    refine integral_congr_ae ?_
    filter_upwards with t₁
    simp [sq]
  have hf_norm :
      (∫ t₁, ‖f t₁‖ ^ (2 : ℝ) ∂μ₁) ^ (1 / (2 : ℝ)) = ‖f‖ := by
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal]
    · norm_num
    · positivity
  calc
    ‖hilbertSchmidtApply μ₁ a f t₂‖ = ‖∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁‖ := rfl
    _ ≤ ∫ t₁, ‖a (t₁, t₂) * f t₁‖ ∂μ₁ := norm_integral_le_integral_norm _
    _ = ∫ t₁, ‖a (t₁, t₂)‖ * ‖f t₁‖ ∂μ₁ := by
      simp [norm_mul]
    _ ≤ (∫ t₁, ‖a (t₁, t₂)‖ ^ (2 : ℝ) ∂μ₁) ^ (1 / (2 : ℝ)) *
          (∫ t₁, ‖f t₁‖ ^ (2 : ℝ) ∂μ₁) ^ (1 / (2 : ℝ)) := by
            simpa using MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
              (μ := μ₁) (f := fun t₁ ↦ a (t₁, t₂)) (g := fun t₁ ↦ f t₁)
              (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two hcolReal hfReal
    _ = ‖f‖ * columnRoot μ₁ a t₂ := by
      rw [hcol_sq, hf_norm, mul_comm]
      -- Proof step: rewrite the remaining square root as the `1 / 2` power of the column norm.
      change ‖f‖ * (columnSquareIntegral μ₁ a t₂) ^ (1 / (2 : ℝ)) =
        ‖f‖ * Real.sqrt (columnSquareIntegral μ₁ a t₂)
      rw [Real.sqrt_eq_rpow]

-- Proof step: combine the output measurability with the previous pointwise bound and the
-- dominating `L²(μ₂)` function `columnRoot`.
/-- Helper for Exercise 14.2.2: the raw kernel integral belongs to `L²(μ₂)`. -/
private theorem hilbertSchmidtApply_memLp (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂))
    (f : Ω₁ →₂[μ₁] ℝ) :
    MemLp (hilbertSchmidtApply μ₁ a f) 2 μ₂ := by
  -- Proof step: `MemLp.of_le_mul` expects the dominating function under a norm.
  exact MemLp.of_le_mul (columnRoot_memLp μ₁ μ₂ a ha)
    (hilbertSchmidtApply_aestronglyMeasurable μ₁ μ₂ a ha f)
    (by
      filter_upwards [operatorApply_bound_ae μ₁ μ₂ a ha f] with t₂ hbound
      simpa [columnRoot_norm μ₁ a t₂] using hbound)

/-- Helper for Exercise 14.2.2: the columnwise dominating function packaged as an element of
`L²(μ₂)`. -/
private def columnRootLp (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂)) :
    Ω₂ →₂[μ₂] ℝ :=
  (columnRoot_memLp μ₁ μ₂ a ha).toLp (columnRoot μ₁ a)

/-- Helper for Exercise 14.2.2: the Hilbert--Schmidt output packaged as an element of `L²(μ₂)`. -/
private def hilbertSchmidtOutput (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂))
    (f : Ω₁ →₂[μ₁] ℝ) : Ω₂ →₂[μ₂] ℝ :=
  (hilbertSchmidtApply_memLp μ₁ μ₂ a ha f).toLp (hilbertSchmidtApply μ₁ a f)

-- Proof step: `hilbertSchmidtOutput` is defined by `MemLp.toLp`, so its coercion is exactly the
-- raw integral formula almost everywhere.
/-- Helper for Exercise 14.2.2: the packaged output agrees almost everywhere with the raw kernel
integral. -/
private theorem hilbertSchmidtOutput_ae_eq (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) (f : Ω₁ →₂[μ₁] ℝ) :
    hilbertSchmidtOutput μ₁ μ₂ a ha f =ᵐ[μ₂] hilbertSchmidtApply μ₁ a f := by
  simpa [hilbertSchmidtOutput] using
    (MemLp.coeFn_toLp (hilbertSchmidtApply_memLp μ₁ μ₂ a ha f))

-- Proof step: compare both `L²(μ₂)` outputs through their almost-everywhere representatives and
-- use linearity of the integral on almost every good column.
/-- Helper for Exercise 14.2.2: the packaged kernel output is additive in the input function. -/
private theorem hilbertSchmidtOutput_add (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂))
    (f g : Ω₁ →₂[μ₁] ℝ) :
    hilbertSchmidtOutput μ₁ μ₂ a ha (f + g)
      = hilbertSchmidtOutput μ₁ μ₂ a ha f + hilbertSchmidtOutput μ₁ μ₂ a ha g := by
  have h_apply_add :
      hilbertSchmidtApply μ₁ a (f + g) =ᵐ[μ₂]
        fun t₂ ↦ hilbertSchmidtApply μ₁ a f t₂ + hilbertSchmidtApply μ₁ a g t₂ := by
    filter_upwards [columnsMemLpAe μ₁ μ₂ a ha] with t₂ hcol
    have hf_int : Integrable (fun t₁ ↦ a (t₁, t₂) * f t₁) μ₁ :=
      hcol.integrable_mul (Lp.memLp f)
    have hg_int : Integrable (fun t₁ ↦ a (t₁, t₂) * g t₁) μ₁ :=
      hcol.integrable_mul (Lp.memLp g)
    have hfg : (fun t₁ ↦ a (t₁, t₂) * (f + g) t₁) =ᵐ[μ₁]
        fun t₁ ↦ a (t₁, t₂) * (f t₁ + g t₁) := by
      filter_upwards [Lp.coeFn_add f g] with t₁ ht
      -- Proof step: rewrite the `Lp` representative pointwise before distributing the kernel.
      simpa [Pi.add_apply] using congrArg (fun x : ℝ => a (t₁, t₂) * x) ht
    calc
      hilbertSchmidtApply μ₁ a (f + g) t₂
          = ∫ t₁, a (t₁, t₂) * (f t₁ + g t₁) ∂μ₁ := by
              rw [hilbertSchmidtApply]
              exact integral_congr_ae hfg
      _ = ∫ t₁, (a (t₁, t₂) * f t₁) + (a (t₁, t₂) * g t₁) ∂μ₁ := by
            congr with t₁
            rw [mul_add]
      _ = ∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁ + ∫ t₁, a (t₁, t₂) * g t₁ ∂μ₁ := by
            rw [integral_add hf_int hg_int]
      _ = hilbertSchmidtApply μ₁ a f t₂ + hilbertSchmidtApply μ₁ a g t₂ := by
            simp [hilbertSchmidtApply]
  apply Lp.ext
  refine (hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha (f + g)).trans ?_
  refine h_apply_add.trans ?_
  filter_upwards [hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha f,
    hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha g,
    Lp.coeFn_add (hilbertSchmidtOutput μ₁ μ₂ a ha f) (hilbertSchmidtOutput μ₁ μ₂ a ha g)]
      with t₂ hf hg hadd
  simpa [hf, hg] using hadd.symm

-- Proof step: compare representatives and pull the scalar through the integral on almost every
-- good column.
/-- Helper for Exercise 14.2.2: the packaged kernel output is homogeneous in the input function. -/
private theorem hilbertSchmidtOutput_smul (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂))
    (c : ℝ) (f : Ω₁ →₂[μ₁] ℝ) :
    hilbertSchmidtOutput μ₁ μ₂ a ha (c • f) = c • hilbertSchmidtOutput μ₁ μ₂ a ha f := by
  have h_apply_smul :
      hilbertSchmidtApply μ₁ a (c • f) =ᵐ[μ₂]
        fun t₂ ↦ c • hilbertSchmidtApply μ₁ a f t₂ := by
    filter_upwards [columnsMemLpAe μ₁ μ₂ a ha] with t₂ hcol
    have hsmul :
        (fun t₁ ↦ a (t₁, t₂) * (c • f) t₁) =ᵐ[μ₁]
          fun t₁ ↦ c * (a (t₁, t₂) * f t₁) := by
      filter_upwards [Lp.coeFn_smul c f] with t₁ ht
      -- Proof step: rewrite the scalar multiple pointwise, then commute the scalar to the front.
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun x : ℝ => a (t₁, t₂) * x) ht
    calc
      hilbertSchmidtApply μ₁ a (c • f) t₂
          = ∫ t₁, c * (a (t₁, t₂) * f t₁) ∂μ₁ := by
              rw [hilbertSchmidtApply]
              exact integral_congr_ae hsmul
      _ = c * ∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁ := by
            rw [integral_const_mul]
      _ = c • hilbertSchmidtApply μ₁ a f t₂ := by
            simp [hilbertSchmidtApply, smul_eq_mul]
  apply Lp.ext
  refine (hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha (c • f)).trans ?_
  refine h_apply_smul.trans ?_
  filter_upwards [hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha f,
    Lp.coeFn_smul c (hilbertSchmidtOutput μ₁ μ₂ a ha f)] with t₂ hf hsmul
  simpa [hf] using hsmul.symm

-- Proof step: transfer the almost-everywhere pointwise Cauchy--Schwarz bound to an `L²` norm
-- bound using the packaged dominating function `columnRootLp`.
/-- Helper for Exercise 14.2.2: the packaged kernel output satisfies the expected operator norm
bound. -/
private theorem hilbertSchmidtOutput_norm_le (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂))
    (f : Ω₁ →₂[μ₁] ℝ) :
    ‖hilbertSchmidtOutput μ₁ μ₂ a ha f‖ ≤ ‖columnRootLp μ₁ μ₂ a ha‖ * ‖f‖ := by
  have hpointwise :
      ∀ᵐ t₂ ∂μ₂, ‖hilbertSchmidtOutput μ₁ μ₂ a ha f t₂‖
        ≤ ‖f‖ * ‖columnRootLp μ₁ μ₂ a ha t₂‖ := by
    filter_upwards [hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha f,
      MemLp.coeFn_toLp (columnRoot_memLp μ₁ μ₂ a ha),
      operatorApply_bound_ae μ₁ μ₂ a ha f] with t₂ hout hroot hbound
    -- Proof step: rewrite the packaged dominating function back to the raw nonnegative column norm.
    simpa [columnRootLp, hout, hroot, columnRoot_norm μ₁ a t₂] using hbound
  simpa [mul_comm] using Lp.norm_le_mul_norm_of_ae_le_mul hpointwise

/-- Helper for Exercise 14.2.2: the linear map underlying the Hilbert--Schmidt operator. -/
private def hilbertSchmidtOperatorLinear (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    (Ω₁ →₂[μ₁] ℝ) →ₗ[ℝ] (Ω₂ →₂[μ₂] ℝ) :=
  { toFun := hilbertSchmidtOutput μ₁ μ₂ a ha
    map_add' := hilbertSchmidtOutput_add μ₁ μ₂ a ha
    map_smul' := hilbertSchmidtOutput_smul μ₁ μ₂ a ha }

/-- The continuous linear operator associated with an `L²` kernel, defined directly from the
columnwise integral formula and the `L²(μ₂)` bound on the column norms. -/
def hilbertSchmidtOperator (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    (Ω₁ →₂[μ₁] ℝ) →L[ℝ] (Ω₂ →₂[μ₂] ℝ) :=
  LinearMap.mkContinuous (hilbertSchmidtOperatorLinear μ₁ μ₂ a ha)
    ‖columnRootLp μ₁ μ₂ a ha‖ (hilbertSchmidtOutput_norm_le μ₁ μ₂ a ha)

-- Proof step: the continuous linear map was defined from the `toLp` class of the raw kernel
-- integral, so the claimed almost-everywhere formula is immediate from `MemLp.coeFn_toLp`.
/-- Exercise 14.2.2: a square-integrable measurable kernel defines a continuous linear operator
from `L²(μ₁)` to `L²(μ₂)` by the usual integral formula. -/
theorem hilbertSchmidtOperator_ae_eq (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) (f : Ω₁ →₂[μ₁] ℝ) :
    hilbertSchmidtOperator μ₁ μ₂ a ha f =ᵐ[μ₂]
      fun t₂ ↦ ∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁ := by
  simpa [hilbertSchmidtOperator, hilbertSchmidtOperatorLinear] using
    (hilbertSchmidtOutput_ae_eq μ₁ μ₂ a ha f)
