/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.SetAlgebra

public section

open scoped ENNReal

noncomputable section

namespace RealL2

variable {Ω : Type} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)
variable (k : Ω → Ω → ℝ)

/-- The pointwise Fredholm first-kind integral transform associated to the kernel `k`. -/
@[expose]
def kernelFunction (f : MeasureTheory.Lp ℝ 2 μ) : Ω → ℝ :=
  fun x ↦ ∫ y, k x y * f y ∂μ

/-- Pointwise formula for `kernelFunction`. -/
theorem kernelFunction_apply (f : MeasureTheory.Lp ℝ 2 μ) (x : Ω) :
    kernelFunction μ k f x = ∫ y, k x y * f y ∂μ :=
  rfl

/-- A bounded operator on real `L²(Ω)` realizes the Fredholm kernel `k` when it agrees almost
everywhere with the pointwise integral transform on every input. -/
def IsKernelOperator
    (K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ) : Prop :=
  ∀ f : MeasureTheory.Lp ℝ 2 μ, K f =ᵐ[μ] kernelFunction μ k f

/-- The defining almost-everywhere formula of a Fredholm kernel operator realization. -/
theorem IsKernelOperator.ae_eq_kernelFunction
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) (f : MeasureTheory.Lp ℝ 2 μ) :
    K f =ᵐ[μ] kernelFunction μ k f :=
  hK f

/-- A Fredholm kernel operator realization is unique. -/
theorem kernelOperator_ext
    {K K' : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) (hK' : IsKernelOperator μ k K') :
    K = K' := by
  -- Two realizations coincide because they agree a.e. with the same kernel formula on every input.
  ext f
  exact (hK f).trans (hK' f).symm

section

variable [MeasureTheory.SFinite μ]

/-- Helper for Example 2.4: an `L²(μ × μ)` kernel has `L²(μ)` sections in the second variable for
almost every first coordinate. -/
theorem kernelSection_memLp_ae
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    ∀ᵐ x ∂μ, MeasureTheory.MemLp (fun y ↦ k x y) 2 μ := by
  -- Rewrite the product `L²` hypothesis as integrability of the squared kernel on `Ω × Ω`.
  have hk_sq : MeasureTheory.Integrable (fun z : Ω × Ω ↦ (k z.1 z.2) ^ (2 : ℕ))
      (MeasureTheory.Measure.prod μ μ) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq h_kernel.aestronglyMeasurable] at h_kernel
    exact h_kernel
  -- Fubini gives square-integrable sections for almost every first coordinate.
  have h_section_sq : ∀ᵐ x ∂μ, MeasureTheory.Integrable (fun y ↦ (k x y) ^ (2 : ℕ)) μ := by
    simpa using MeasureTheory.Integrable.prod_right_ae hk_sq
  -- The product `AEStronglyMeasurable` hypothesis also descends to almost every section.
  have h_section_ae : ∀ᵐ x ∂μ, MeasureTheory.AEStronglyMeasurable (fun y ↦ k x y) μ := by
    simpa using MeasureTheory.AEStronglyMeasurable.prodMk_left (μ := μ) (ν := μ) h_kernel.1
  filter_upwards [h_section_sq, h_section_ae] with x hx_sq hx_ae
  rw [MeasureTheory.memLp_two_iff_integrable_sq hx_ae]
  exact hx_sq

/-- Helper for Example 2.4: almost every section satisfies the pointwise `L²` Cauchy-Schwarz bound
for the Fredholm transform. -/
theorem kernelFunction_sq_le_ae
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f : MeasureTheory.Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ,
      (kernelFunction μ k f x) ^ (2 : ℕ) ≤
        ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ := by
  -- For almost every `x`, package the section `y ↦ k x y` as an `L²` vector and compare with `f`.
  filter_upwards [kernelSection_memLp_ae (μ := μ) (k := k) h_kernel] with x hx
  let sx : MeasureTheory.Lp ℝ 2 μ := hx.toLp (fun y ↦ k x y)
  have hsx_ae : sx =ᵐ[μ] fun y ↦ k x y := hx.coeFn_toLp
  have h_inner_eq : inner ℝ sx f = kernelFunction μ k f x := by
    calc
      inner ℝ sx f = ∫ y, sx y * f y ∂μ := by
        rw [MeasureTheory.L2.inner_def]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        simp [mul_comm]
      _ = ∫ y, k x y * f y ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hsx_ae] with y hy
        simp [hy]
      _ = kernelFunction μ k f x := by
        rw [kernelFunction_apply]
  have h_abs :
      |kernelFunction μ k f x| ≤ ‖sx‖ * ‖f‖ := by
    calc
      |kernelFunction μ k f x| = |inner ℝ sx f| := by rw [← h_inner_eq]
      _ ≤ ‖sx‖ * ‖f‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) sx f
  have hsx_norm_sq :
      ‖sx‖ ^ (2 : ℕ) = ∫ y, (k x y) ^ (2 : ℕ) ∂μ := by
    calc
      ‖sx‖ ^ (2 : ℕ) = inner ℝ sx sx := by
        exact (real_inner_self_eq_norm_sq sx).symm
      _ = ∫ y, sx y * sx y ∂μ := by
        rw [MeasureTheory.L2.inner_def]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        simp [pow_two]
      _ = ∫ y, (sx y) ^ (2 : ℕ) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        symm
        rw [pow_two]
      _ = ∫ y, (k x y) ^ (2 : ℕ) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hsx_ae] with y hy
        simp [hy]
  have h_sq_abs :
      |kernelFunction μ k f x| ^ (2 : ℕ) ≤ (‖sx‖ * ‖f‖) ^ (2 : ℕ) := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using h_abs)
  -- Replace the section norm by its integral formula to get the stated kernel-energy bound.
  calc
    (kernelFunction μ k f x) ^ (2 : ℕ) = |kernelFunction μ k f x| ^ (2 : ℕ) := by
      rw [sq_abs]
    _ ≤ (‖sx‖ * ‖f‖) ^ (2 : ℕ) := h_sq_abs
    _ = ‖sx‖ ^ (2 : ℕ) * ‖f‖ ^ (2 : ℕ) := by rw [mul_pow]
    _ = ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ := by
      rw [hsx_norm_sq, mul_comm]

/-- A square-integrable Fredholm kernel maps real `L²(Ω)` back into `L²(Ω)`. -/
theorem kernelFunction_memLp
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f : MeasureTheory.Lp ℝ 2 μ) :
    MeasureTheory.MemLp (kernelFunction μ k f) 2 μ := by
  -- The product kernel and the second-coordinate copy of `f` make the pointwise integral
  -- transform a.e.-strongly measurable in the first coordinate.
  have h_integrand_ae :
      MeasureTheory.AEStronglyMeasurable
        (fun z : Ω × Ω ↦ k z.1 z.2 * f z.2) (MeasureTheory.Measure.prod μ μ) := by
    exact h_kernel.1.mul ((MeasureTheory.Lp.memLp f).1.comp_snd)
  have h_kernelFunction_ae :
      MeasureTheory.AEStronglyMeasurable (kernelFunction μ k f) μ := by
    change MeasureTheory.AEStronglyMeasurable (fun x ↦ ∫ y, k x y * f y ∂μ) μ
    simpa using
      MeasureTheory.AEStronglyMeasurable.integral_prod_right' (μ := μ) (ν := μ) h_integrand_ae
  -- Integrating the squared-kernel sections gives the integrable majorant from the pointwise bound.
  have hk_sq : MeasureTheory.Integrable (fun z : Ω × Ω ↦ (k z.1 z.2) ^ (2 : ℕ))
      (MeasureTheory.Measure.prod μ μ) := by
    exact (MeasureTheory.memLp_two_iff_integrable_sq h_kernel.1).1 h_kernel
  have h_section_energy :
      MeasureTheory.Integrable (fun x ↦ ∫ y, (k x y) ^ (2 : ℕ) ∂μ) μ := by
    simpa using MeasureTheory.Integrable.integral_prod_left hk_sq
  have h_majorant :
      MeasureTheory.Integrable
        (fun x ↦ ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ) μ := by
    exact h_section_energy.const_mul (‖f‖ ^ (2 : ℕ))
  -- The sectionwise Cauchy-Schwarz estimate upgrades the pointwise transform to an `L²` function.
  rw [MeasureTheory.memLp_two_iff_integrable_sq h_kernelFunction_ae]
  refine MeasureTheory.Integrable.mono_nonneg h_majorant (h_kernelFunction_ae.pow 2) ?_ ?_
  · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  · exact kernelFunction_sq_le_ae (μ := μ) (k := k) h_kernel f

/-- Helper for Example 2.4: the raw Fredholm transform is almost everywhere additive in the
input `L²` datum. -/
theorem kernelFunction_add_ae
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f g : MeasureTheory.Lp ℝ 2 μ) :
    kernelFunction μ k (f + g) =ᵐ[μ]
      fun x ↦ kernelFunction μ k f x + kernelFunction μ k g x := by
  -- For almost every section, `integral_add` turns the raw kernel integral into the sum of the
  -- two sectionwise integrals.
  filter_upwards [kernelSection_memLp_ae (μ := μ) (k := k) h_kernel] with x hx
  have hf_int : MeasureTheory.Integrable (fun y ↦ k x y * f y) μ :=
    hx.integrable_mul (MeasureTheory.Lp.memLp f)
  have hg_int : MeasureTheory.Integrable (fun y ↦ k x y * g y) μ :=
    hx.integrable_mul (MeasureTheory.Lp.memLp g)
  have hfg_int : MeasureTheory.Integrable (fun y ↦ k x y * (f + g) y) μ :=
    hx.integrable_mul (MeasureTheory.Lp.memLp (f + g))
  have h_integrand :
      (fun y ↦ k x y * (f + g) y) =ᵐ[μ]
        fun y ↦ k x y * f y + k x y * g y := by
    filter_upwards [MeasureTheory.Lp.coeFn_add f g] with y hy
    simpa [Pi.add_apply, mul_add] using congrArg (fun t : ℝ ↦ k x y * t) hy
  calc
    kernelFunction μ k (f + g) x = ∫ y, k x y * (f + g) y ∂μ := by
      rfl
    _ = ∫ y, (k x y * f y + k x y * g y) ∂μ := by
      exact MeasureTheory.integral_congr_ae h_integrand
    _ = ∫ y, k x y * f y ∂μ + ∫ y, k x y * g y ∂μ := by
      exact MeasureTheory.integral_add hf_int hg_int
    _ = kernelFunction μ k f x + kernelFunction μ k g x := by
      rfl

/-- Helper for Example 2.4: the raw Fredholm transform is almost everywhere scalar-linear in the
input `L²` datum. -/
theorem kernelFunction_smul_ae
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (c : ℝ) (f : MeasureTheory.Lp ℝ 2 μ) :
    kernelFunction μ k (c • f) =ᵐ[μ] fun x ↦ c * kernelFunction μ k f x := by
  -- For almost every section, `integral_smul` moves the scalar outside the raw kernel integral.
  filter_upwards [kernelSection_memLp_ae (μ := μ) (k := k) h_kernel] with x hx
  have hf_int : MeasureTheory.Integrable (fun y ↦ k x y * f y) μ :=
    hx.integrable_mul (MeasureTheory.Lp.memLp f)
  have hcf_int : MeasureTheory.Integrable (fun y ↦ k x y * (c • f) y) μ :=
    hx.integrable_mul (MeasureTheory.Lp.memLp (c • f))
  have h_integrand :
      (fun y ↦ k x y * (c • f) y) =ᵐ[μ] fun y ↦ c * (k x y * f y) := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul c f] with y hy
    simpa [Pi.smul_apply, mul_assoc, mul_left_comm] using congrArg (fun t : ℝ ↦ k x y * t) hy
  calc
    kernelFunction μ k (c • f) x = ∫ y, k x y * (c • f) y ∂μ := by
      rfl
    _ = ∫ y, c * (k x y * f y) ∂μ := by
      exact MeasureTheory.integral_congr_ae h_integrand
    _ = c * ∫ y, k x y * f y ∂μ := by
      simpa using MeasureTheory.integral_const_mul c (fun y ↦ k x y * f y)
    _ = c * kernelFunction μ k f x := by
      rfl

/-- Helper for Example 2.4: the `toLp`-packaged Fredholm output is additive in the input datum. -/
theorem kernelFunction_toLp_add
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f g : MeasureTheory.Lp ℝ 2 μ) :
    (kernelFunction_memLp μ k h_kernel (f + g)).toLp (kernelFunction μ k (f + g)) =
      (kernelFunction_memLp μ k h_kernel f).toLp (kernelFunction μ k f) +
        (kernelFunction_memLp μ k h_kernel g).toLp (kernelFunction μ k g) := by
  -- Transport the a.e. additive raw formula through the quotient map into `L²(Ω)`.
  rw [← MeasureTheory.MemLp.toLp_add
    (hf := kernelFunction_memLp μ k h_kernel f)
    (hg := kernelFunction_memLp μ k h_kernel g)]
  exact MeasureTheory.MemLp.toLp_congr
    (kernelFunction_memLp μ k h_kernel (f + g))
    ((kernelFunction_memLp μ k h_kernel f).add (kernelFunction_memLp μ k h_kernel g))
    (kernelFunction_add_ae (μ := μ) (k := k) h_kernel f g)

/-- Helper for Example 2.4: the `toLp`-packaged Fredholm output is scalar-linear in the input
datum. -/
theorem kernelFunction_toLp_smul
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (c : ℝ) (f : MeasureTheory.Lp ℝ 2 μ) :
    (kernelFunction_memLp μ k h_kernel (c • f)).toLp (kernelFunction μ k (c • f)) =
      c • (kernelFunction_memLp μ k h_kernel f).toLp (kernelFunction μ k f) := by
  -- Transport the a.e. scalar-linearity of the raw formula through `MemLp.toLp`.
  rw [← MeasureTheory.MemLp.toLp_const_smul c
    (hf := kernelFunction_memLp μ k h_kernel f)]
  exact MeasureTheory.MemLp.toLp_congr
    (kernelFunction_memLp μ k h_kernel (c • f))
    ((kernelFunction_memLp μ k h_kernel f).const_smul c)
    (kernelFunction_smul_ae (μ := μ) (k := k) h_kernel c f)

/-- Helper for Example 2.4: the canonical `L²` Fredholm output obeys the expected operator-norm
bound. -/
theorem kernelFunction_toLp_norm_le
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f : MeasureTheory.Lp ℝ 2 μ) :
    ‖(kernelFunction_memLp μ k h_kernel f).toLp (kernelFunction μ k f)‖ ≤
      Real.sqrt
          (∫ z : Ω × Ω, (k z.1 z.2) ^ (2 : ℕ) ∂(MeasureTheory.Measure.prod μ μ)) * ‖f‖ := by
  -- Package the raw integral transform as an `L²` vector and compare its squared norm with the
  -- integrated sectionwise Cauchy-Schwarz bound.
  let Tf : MeasureTheory.Lp ℝ 2 μ :=
    (kernelFunction_memLp μ k h_kernel f).toLp (kernelFunction μ k f)
  let energy : ℝ :=
    ∫ z : Ω × Ω, (k z.1 z.2) ^ (2 : ℕ) ∂(MeasureTheory.Measure.prod μ μ)
  have hk_sq : MeasureTheory.Integrable (fun z : Ω × Ω ↦ (k z.1 z.2) ^ (2 : ℕ))
      (MeasureTheory.Measure.prod μ μ) := by
    exact (MeasureTheory.memLp_two_iff_integrable_sq h_kernel.1).1 h_kernel
  have hTf_sq_int : MeasureTheory.Integrable (fun x ↦ (Tf x) ^ (2 : ℕ)) μ := by
    have hTf_memLp : MeasureTheory.MemLp (fun x ↦ Tf x) 2 μ := MeasureTheory.Lp.memLp Tf
    rw [MeasureTheory.memLp_two_iff_integrable_sq (MeasureTheory.Lp.aestronglyMeasurable Tf)]
      at hTf_memLp
    exact hTf_memLp
  have h_section_energy : MeasureTheory.Integrable (fun x ↦ ∫ y, (k x y) ^ (2 : ℕ) ∂μ) μ := by
    simpa using MeasureTheory.Integrable.integral_prod_left hk_sq
  have h_majorant :
      MeasureTheory.Integrable
        (fun x ↦ ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ) μ := by
    exact h_section_energy.const_mul (‖f‖ ^ (2 : ℕ))
  have hpoint :
      ∀ᵐ x ∂μ, (Tf x) ^ (2 : ℕ) ≤ ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ := by
    filter_upwards
      [MeasureTheory.MemLp.coeFn_toLp (kernelFunction_memLp μ k h_kernel f),
        kernelFunction_sq_le_ae (μ := μ) (k := k) h_kernel f] with x hTf hx
    simpa [Tf, hTf] using hx
  have h_integral_le :
      ∫ x, (Tf x) ^ (2 : ℕ) ∂μ ≤
        ∫ x, ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ ∂μ := by
    exact MeasureTheory.integral_mono_ae hTf_sq_int h_majorant hpoint
  have hTf_norm_sq : ‖Tf‖ ^ (2 : ℕ) = ∫ x, (Tf x) ^ (2 : ℕ) ∂μ := by
    calc
      ‖Tf‖ ^ (2 : ℕ) = inner ℝ Tf Tf := by
        exact (real_inner_self_eq_norm_sq Tf).symm
      _ = ∫ x, inner ℝ (Tf x) (Tf x) ∂μ := by
        rw [MeasureTheory.L2.inner_def]
      _ = ∫ x, (Tf x) ^ (2 : ℕ) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [Real.norm_eq_abs, sq_abs]
  have h_energy_nonneg : 0 ≤ energy := by
    dsimp [energy]
    exact MeasureTheory.integral_nonneg fun _ ↦ sq_nonneg _
  have hsq :
      ‖Tf‖ ^ (2 : ℕ) ≤ energy * ‖f‖ ^ (2 : ℕ) := by
    calc
      ‖Tf‖ ^ (2 : ℕ) = ∫ x, (Tf x) ^ (2 : ℕ) ∂μ := hTf_norm_sq
      _ ≤ ∫ x, ‖f‖ ^ (2 : ℕ) * ∫ y, (k x y) ^ (2 : ℕ) ∂μ ∂μ := h_integral_le
      _ = ‖f‖ ^ (2 : ℕ) * energy := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_integral hk_sq]
      _ = energy * ‖f‖ ^ (2 : ℕ) := by ring
  have hsq_target :
      ‖Tf‖ ^ (2 : ℕ) ≤ (Real.sqrt energy * ‖f‖) ^ (2 : ℕ) := by
    simpa [energy, mul_pow, Real.sq_sqrt h_energy_nonneg] using hsq
  have hTf_nonneg : 0 ≤ ‖Tf‖ := norm_nonneg _
  have htarget_nonneg : 0 ≤ Real.sqrt energy * ‖f‖ := by
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hfinal : ‖Tf‖ ≤ Real.sqrt energy * ‖f‖ := by
    nlinarith
  simpa [Tf, energy] using hfinal

/-- Helper for Example 2.4: the raw `toLp` Fredholm transform defines a linear map on `L²(Ω)`. -/
def canonicalKernelLinear
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    MeasureTheory.Lp ℝ 2 μ →ₗ[ℝ] MeasureTheory.Lp ℝ 2 μ where
  toFun := fun f ↦ (kernelFunction_memLp μ k h_kernel f).toLp (kernelFunction μ k f)
  map_add' := kernelFunction_toLp_add (μ := μ) (k := k) h_kernel
  map_smul' := kernelFunction_toLp_smul (μ := μ) (k := k) h_kernel

/-- Helper for Example 2.4: the canonical `L²` Fredholm realization obtained from
`kernelFunction_memLp`. -/
def canonicalKernelOperator
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
  (canonicalKernelLinear μ k h_kernel).mkContinuous
    (Real.sqrt
      (∫ z : Ω × Ω, (k z.1 z.2) ^ (2 : ℕ) ∂(MeasureTheory.Measure.prod μ μ)))
    (kernelFunction_toLp_norm_le (μ := μ) (k := k) h_kernel)

/-- Helper for Example 2.4: the canonical `toLp` realization satisfies the Fredholm kernel formula
almost everywhere. -/
theorem canonicalKernelOperator_isKernelOperator
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    IsKernelOperator μ k (canonicalKernelOperator μ k h_kernel) := by
  -- The canonical realization is represented by the same raw kernel integral function.
  intro f
  simpa [canonicalKernelOperator, canonicalKernelLinear] using
    (MeasureTheory.MemLp.coeFn_toLp (kernelFunction_memLp μ k h_kernel f))

/-- Helper for Example 2.4: the canonical `toLp` realization inherits the explicit operator-norm
bound from the `mkContinuous` constructor. -/
theorem canonicalKernelOperator_norm_le
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    ‖canonicalKernelOperator μ k h_kernel‖ ≤
      Real.sqrt
        (∫ z : Ω × Ω, (k z.1 z.2) ^ (2 : ℕ) ∂(MeasureTheory.Measure.prod μ μ)) := by
  -- The continuous linear realization uses exactly the proven `toLp` operator estimate.
  exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) <|
    kernelFunction_toLp_norm_le (μ := μ) (k := k) h_kernel

/-- A square-integrable kernel on `Ω × Ω` determines a unique bounded operator on real `L²(Ω)`
with the Fredholm integral formula. -/
theorem existsUnique_kernelOperator
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    ∃! K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ,
      IsKernelOperator μ k K := by
  -- Route correction: build the canonical `MemLp.toLp` realization first, then uniqueness is
  -- exactly `kernelOperator_ext`.
  refine ⟨canonicalKernelOperator μ k h_kernel, canonicalKernelOperator_isKernelOperator
    (μ := μ) (k := k) h_kernel, ?_⟩
  intro K hK
  exact kernelOperator_ext (μ := μ) (k := k) hK
    (canonicalKernelOperator_isKernelOperator (μ := μ) (k := k) h_kernel)

/-- Any Fredholm kernel operator realization has norm bounded by the square root of the kernel
energy on `Ω × Ω`. -/
theorem kernelOperator_norm_le
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) :
    ‖K‖ ≤
      Real.sqrt (∫ z : Ω × Ω, (k z.1 z.2) ^ (2 : ℕ) ∂(MeasureTheory.Measure.prod μ μ)) := by
  -- Compare `K` with the canonical realization and transfer the explicit norm bound.
  have h_eq :
      K = canonicalKernelOperator μ k h_kernel := by
    exact kernelOperator_ext (μ := μ) (k := k) hK
      (canonicalKernelOperator_isKernelOperator (μ := μ) (k := k) h_kernel)
  rw [h_eq]
  exact canonicalKernelOperator_norm_le (μ := μ) (k := k) h_kernel

/-- Helper for Example 2.4: a bounded operator with finite-dimensional range is compact. -/
private theorem isCompactOperator_of_finiteDimensionalRange
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [NormedSpace ℝ H₁]
    [NormedAddCommGroup H₂] [NormedSpace ℝ H₂]
    (K : H₁ →L[ℝ] H₂) (h_range_fin : FiniteDimensional ℝ K.range) :
    IsCompactOperator K := by
  let Kr : H₁ →L[ℝ] K.range := K.rangeRestrict
  have hSubtype : IsCompactOperator K.range.subtypeL := by
    -- The subtype inclusion is compact because the finite-dimensional range is locally compact.
    have hLoc : LocallyCompactSpace K.range :=
      @LocallyCompactSpace.of_finiteDimensional_of_complete ℝ K.range
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance h_range_fin
    have hId : IsCompactOperator (id : K.range → K.range) := by
      exact @isCompactOperator_id K.range inferInstance inferInstance inferInstance hLoc
    simpa using hId.clm_comp K.range.subtypeL
  have hKr : Subtype.val ∘ Kr = K := by
    funext x
    rfl
  -- Factor `K` through its finite-dimensional range and compose with the compact subtype map.
  have hComp : IsCompactOperator (Subtype.val ∘ Kr) := by
    simpa using hSubtype.comp_clm Kr
  simpa [hKr] using hComp

/-- Helper for Example 2.4: an `L²(μ; L²(μ))` section field defines a bounded operator on
real `L²(Ω)`. -/
theorem sectionFieldOperator_add_apply
    (u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ)
    (f g : MeasureTheory.Lp ℝ 2 μ) :
    (innerSL ℝ (f + g)).compLp u =
      (innerSL ℝ f).compLp u + (innerSL ℝ g).compLp u := by
  -- The section-field operator is linear in the test vector through `innerSL`.
  rw [(innerSL ℝ).map_add, ContinuousLinearMap.add_compLp]

/-- Helper for Example 2.4: the section-field operator is scalar-linear in the test vector. -/
theorem sectionFieldOperator_smul_apply
    (u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ)
    (c : ℝ) (f : MeasureTheory.Lp ℝ 2 μ) :
    (innerSL ℝ (c • f)).compLp u = c • (innerSL ℝ f).compLp u := by
  -- Scalar multiplication passes through both the inner-product functional and `compLp`.
  rw [(innerSL ℝ).map_smul, ContinuousLinearMap.smul_compLp]

/-- Helper for Example 2.4: the section-field operator has operator norm at most the section-field
`L²` norm. -/
theorem sectionFieldOperator_norm_apply_le
    (u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    ‖(innerSL ℝ f).compLp u‖ ≤ ‖u‖ * ‖f‖ := by
  -- First bound `compLp` by the operator norm of `innerSL`, then identify that norm with `‖f‖`.
  calc
    ‖(innerSL ℝ f).compLp u‖ ≤ ‖innerSL ℝ f‖ * ‖u‖ := ContinuousLinearMap.norm_compLp_le _ _
    _ = ‖f‖ * ‖u‖ := by rw [innerSL_apply_norm]
    _ = ‖u‖ * ‖f‖ := by ring

/-- Helper for Example 2.4: package an `L²(μ; L²(μ))` section field as a bounded operator on
real `L²(Ω)`. -/
def sectionFieldOperator
    (u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
    MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (innerSL ℝ f).compLp u
      map_add' := sectionFieldOperator_add_apply (μ := μ) u
      map_smul' := sectionFieldOperator_smul_apply (μ := μ) u }
    ‖u‖
    (sectionFieldOperator_norm_apply_le (μ := μ) u)

/-- Helper for Example 2.4: the section-field operator is additive in the section datum. -/
theorem sectionFieldOperator_add
    (u v : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
    sectionFieldOperator μ (u + v) =
      sectionFieldOperator μ u + sectionFieldOperator μ v := by
  -- Evaluating both operators on a test vector reduces to additivity of `compLp`.
  ext f
  filter_upwards
      [ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f) (u + v),
        ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f) u,
        ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f) v,
        MeasureTheory.Lp.coeFn_add u v,
        MeasureTheory.Lp.coeFn_add ((innerSL ℝ f).compLp u) ((innerSL ℝ f).compLp v)] with x hsum hu hv huv hadd
  calc
    ((sectionFieldOperator μ (u + v)) f : Ω →ₘ[μ] ℝ) x =
        inner ℝ f (((u + v : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) : Ω →ₘ[μ] _) x) := by
      simpa [sectionFieldOperator] using hsum
    _ = inner ℝ f ((u : Ω →ₘ[μ] _) x) + inner ℝ f ((v : Ω →ₘ[μ] _) x) := by
      rw [huv]
      simp [Pi.add_apply, inner_add_right]
    _ = (((sectionFieldOperator μ u + sectionFieldOperator μ v) f : MeasureTheory.Lp ℝ 2 μ) :
        Ω →ₘ[μ] ℝ) x := by
      simpa [sectionFieldOperator, hu, hv] using hadd.symm

/-- Helper for Example 2.4: the section-field operator is scalar-linear in the section datum. -/
theorem sectionFieldOperator_smul
    (c : ℝ) (u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
    sectionFieldOperator μ (c • u) = c • sectionFieldOperator μ u := by
  -- Evaluating both operators on a test vector reduces to scalar-linearity of `compLp`.
  ext f
  filter_upwards
      [ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f) (c • u),
        ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f) u,
        MeasureTheory.Lp.coeFn_smul c u,
        MeasureTheory.Lp.coeFn_smul c ((innerSL ℝ f).compLp u)] with x hsmul hu huu hcu
  calc
    ((sectionFieldOperator μ (c • u)) f : Ω →ₘ[μ] ℝ) x =
        inner ℝ f (((c • u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) : Ω →ₘ[μ] _) x) := by
      simpa [sectionFieldOperator] using hsmul
    _ = c * inner ℝ f ((u : Ω →ₘ[μ] _) x) := by
      rw [huu]
      simp [Pi.smul_apply, inner_smul_right]
    _ = ((c • sectionFieldOperator μ u) f : MeasureTheory.Lp ℝ 2 μ) x := by
      simpa [sectionFieldOperator, hu, Pi.smul_apply] using hcu.symm

/-- Helper for Example 2.4: package the section-field construction as a bounded linear map in the
section datum. -/
def sectionFieldOperatorLinear :
    MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ →L[ℝ]
      (MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := sectionFieldOperator μ
      map_add' := sectionFieldOperator_add (μ := μ)
      map_smul' := sectionFieldOperator_smul (μ := μ) }
    1
    (by
      intro u
      -- The operator norm bound comes from the pointwise `‖Tf‖ ≤ ‖u‖ * ‖f‖` estimate.
      calc
        ‖sectionFieldOperator μ u‖ ≤ ‖u‖ := by
          refine (sectionFieldOperator μ u).opNorm_le_bound (norm_nonneg _) ?_
          intro f
          simpa [sectionFieldOperator, mul_comm] using
            sectionFieldOperator_norm_apply_le (μ := μ) u f
        _ = 1 * ‖u‖ := by ring)

/-- Helper for Example 2.4: rank-one operators on `L²(Ω)` are compact. -/
theorem rankOne_isCompactOperator
    (u v : MeasureTheory.Lp ℝ 2 μ) :
    IsCompactOperator (InnerProductSpace.rankOne ℝ u v) := by
  -- The range is contained in the one-dimensional span of `u`.
  let S : Submodule ℝ (MeasureTheory.Lp ℝ 2 μ) := Submodule.span ℝ ({u} : Set (MeasureTheory.Lp ℝ 2 μ))
  have hS : FiniteDimensional ℝ S := by
    exact
      FiniteDimensional.span_of_finite
        (K := ℝ) (V := MeasureTheory.Lp ℝ 2 μ)
        (A := ({u} : Set (MeasureTheory.Lp ℝ 2 μ))) (Set.finite_singleton u)
  have hle : (InnerProductSpace.rankOne ℝ u v).range ≤ S := by
    rintro _ ⟨x, rfl⟩
    change inner ℝ v x • u ∈ S
    exact Submodule.smul_mem S _ (Submodule.subset_span (by simp))
  -- Transport finite dimensionality from the enclosing span to the actual operator range.
  letI : FiniteDimensional ℝ S := hS
  have hInclusion :
      Function.Injective
        (Submodule.inclusion hle :
          (InnerProductSpace.rankOne ℝ u v).range →ₗ[ℝ] S) := by
    intro x y hxy
    cases x
    cases y
    cases hxy
    rfl
  have h_range_fin :
      FiniteDimensional ℝ (InnerProductSpace.rankOne ℝ u v).range := by
    exact FiniteDimensional.of_injective (Submodule.inclusion hle) hInclusion
  exact isCompactOperator_of_finiteDimensionalRange
    (K := InnerProductSpace.rankOne ℝ u v) h_range_fin

/-- Helper for Example 2.4: the indicator simple section operator is the expected rank-one map. -/
theorem sectionFieldOperator_indicator_eq_rankOne
    (v : MeasureTheory.Lp ℝ 2 μ)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s < ∞) :
    sectionFieldOperator μ
        (MeasureTheory.Lp.simpleFunc.indicatorConst 2 hs hμs.ne v :
          MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) =
      InnerProductSpace.rankOne ℝ
        (MeasureTheory.indicatorConstLp 2 hs hμs.ne (1 : ℝ)) v := by
  have hcoe :
      (MeasureTheory.Lp.simpleFunc.indicatorConst 2 hs hμs.ne v :
        MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) =
        MeasureTheory.indicatorConstLp 2 hs hμs.ne v := by
    simpa using
      (MeasureTheory.Lp.simpleFunc.coe_indicatorConst
        (p := (2 : ℝ≥0∞)) (μ := μ) (hs := hs) (hμs := hμs.ne) (c := v))
  rw [hcoe]
  -- Compare both operators pointwise on each test vector.
  ext f
  filter_upwards
      [ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f)
        (MeasureTheory.indicatorConstLp 2 hs hμs.ne v :
          MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ),
        MeasureTheory.indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
          (hs := hs) (hμs := hμs.ne) (c := v),
        MeasureTheory.indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
          (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ)),
        MeasureTheory.Lp.coeFn_smul (inner ℝ v f)
          (MeasureTheory.indicatorConstLp 2 hs hμs.ne (1 : ℝ))] with x hxComp hxv hx1 hxSmul
  by_cases hx : x ∈ s
  · simpa [sectionFieldOperator, InnerProductSpace.rankOne_apply, hx, hs, real_inner_comm, hxComp, hxv, hx1,
      hxSmul]
  · simpa [sectionFieldOperator, InnerProductSpace.rankOne_apply, hx, hs, real_inner_comm, hxComp, hxv, hx1,
      hxSmul]

/-- Helper for Example 2.4: simple `L²(μ)`-valued section fields induce compact operators. -/
theorem sectionFieldOperator_simple_isCompact
    (s : MeasureTheory.Lp.simpleFunc (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
    IsCompactOperator
      (sectionFieldOperator μ (s : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ)) := by
  -- Induct on simple sections: indicators give rank-one maps, and compactness is stable under
  -- operator addition.
  refine
    MeasureTheory.Lp.simpleFunc.induction
      (α := Ω) (E := MeasureTheory.Lp ℝ 2 μ) (p := (2 : ℝ≥0∞)) (μ := μ)
      (by norm_num) (by norm_num) ?_ ?_ s
  · intro v t ht hμt
    rw [sectionFieldOperator_indicator_eq_rankOne (μ := μ) (v := v) t ht hμt]
    exact rankOne_isCompactOperator (μ := μ) _ _
  · intro f g hf hg hdis hf_comp hg_comp
    -- The sum step matches the additive structure of `sectionFieldOperator`.
    simpa using
      (sectionFieldOperator_add (μ := μ)
        (u := ((MeasureTheory.SimpleFunc.toLp f hf : MeasureTheory.Lp.simpleFunc
          (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
            MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ))
        (v := ((MeasureTheory.SimpleFunc.toLp g hg : MeasureTheory.Lp.simpleFunc
          (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
            MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ))).symm ▸
        hf_comp.add hg_comp

/-- Helper for Example 2.4: every `L²(μ; L²(μ))` section field induces a compact operator. -/
theorem sectionFieldOperator_isCompact
    (u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ) :
    IsCompactOperator (sectionFieldOperator μ u) := by
  -- Compact operators form a closed set, so density of simple sections upgrades the simple-case
  -- compactness result to all section fields.
  have hclosed :
      IsClosed
        {u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ |
          IsCompactOperator ((sectionFieldOperatorLinear μ) u)} := by
    simpa using
      isClosed_setOf_isCompactOperator.preimage (sectionFieldOperatorLinear (μ := μ)).continuous
  refine
    (MeasureTheory.Lp.simpleFunc.denseRange
      (E := MeasureTheory.Lp ℝ 2 μ) (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num)).induction_on
      u hclosed ?_
  intro s
  -- On the dense simple subset this is exactly the previously proved induction result.
  simpa [sectionFieldOperatorLinear] using sectionFieldOperator_simple_isCompact (μ := μ) s

/-- Helper for Example 2.4: sectionwise kernel equality identifies the section-field operator with
the raw Fredholm transform. -/
private theorem sectionFieldOperator_eq_kernelFunction_of_ae_sections
    {u : MeasureTheory.Lp (MeasureTheory.Lp ℝ 2 μ) 2 μ}
    (hu : ∀ᵐ x ∂μ, (u x : Ω → ℝ) =ᵐ[μ] fun y ↦ k x y)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    sectionFieldOperator μ u f =ᵐ[μ] kernelFunction μ k f := by
  -- Evaluate the section-field operator pointwise and rewrite its inner product against the
  -- section `u x` into the textbook kernel integral.
  filter_upwards [ContinuousLinearMap.coeFn_compLp' (innerSL ℝ f) u, hu] with x hxComp hxSection
  calc
    ((sectionFieldOperator μ u) f : Ω → ℝ) x =
        inner ℝ f (((u : Ω →ₘ[μ] MeasureTheory.Lp ℝ 2 μ) : Ω → MeasureTheory.Lp ℝ 2 μ) x) := by
      simpa [sectionFieldOperator] using hxComp
    _ = ∫ y,
          inner ℝ (f y) ((((u : Ω →ₘ[μ] MeasureTheory.Lp ℝ 2 μ) :
            Ω → MeasureTheory.Lp ℝ 2 μ) x) y) ∂μ := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ y, f y * (((u : Ω →ₘ[μ] MeasureTheory.Lp ℝ 2 μ) : Ω → MeasureTheory.Lp ℝ 2 μ) x) y
          ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      simp [RCLike.inner_apply, mul_comm]
    _ = ∫ y, f y * k x y ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hxSection] with y hy
      simp [hy]
    _ = ∫ y, k x y * f y ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [mul_comm]
    _ = kernelFunction μ k f x := by
      rw [kernelFunction_apply]

/-- Helper for Example 2.4: the separated rectangle kernel attached to measurable sets `s` and `t`.
-/
private def rectangleKernel (s t : Set Ω) (c : ℝ) : Ω → Ω → ℝ :=
  fun x y ↦ c * s.indicator (fun _ ↦ (1 : ℝ)) x * t.indicator (fun _ ↦ (1 : ℝ)) y

/-- Helper for Example 2.4: a measurable finite-measure rectangle defines a product `L²` kernel. -/
private theorem rectangleKernel_memLp
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hμt : μ t < ∞) (c : ℝ) :
    MeasureTheory.MemLp (fun z : Ω × Ω ↦ rectangleKernel (Ω := Ω) s t c z.1 z.2) 2
      (MeasureTheory.Measure.prod μ μ) := by
  have h_rect :
      (MeasureTheory.Measure.prod μ μ) (s ×ˢ t) < ∞ := by
    simpa [MeasureTheory.Measure.prod_prod] using ENNReal.mul_lt_top hμs hμt
  have h_eq :
      (fun z : Ω × Ω ↦ rectangleKernel (Ω := Ω) s t c z.1 z.2) =
        (s ×ˢ t).indicator (fun _ ↦ c) := by
    funext z
    by_cases hx : z.1 ∈ s <;> by_cases hy : z.2 ∈ t <;> simp [rectangleKernel, hx, hy]
  -- Rewrite the rectangle kernel as the indicator of the rectangle in product space.
  rw [h_eq]
  exact MeasureTheory.memLp_indicator_const 2 (hs.prod ht) c (Or.inr h_rect.ne)

/-- Helper for Example 2.4: subtracting kernels subtracts the raw Fredholm transforms a.e. -/
private theorem kernelFunction_sub_ae
    {φ ψ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hψ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f : MeasureTheory.Lp ℝ 2 μ) :
    kernelFunction μ (fun x y ↦ φ x y - ψ x y) f =ᵐ[μ]
      fun x ↦ kernelFunction μ φ f x - kernelFunction μ ψ f x := by
  -- For almost every section, linearity of the Bochner integral gives the pointwise subtraction
  -- rule for the Fredholm transform.
  filter_upwards
      [kernelSection_memLp_ae (μ := μ) (k := φ) hφ,
        kernelSection_memLp_ae (μ := μ) (k := ψ) hψ] with x hxφ hxψ
  have hφ_int : MeasureTheory.Integrable (fun y ↦ φ x y * f y) μ :=
    hxφ.integrable_mul (MeasureTheory.Lp.memLp f)
  have hψ_int : MeasureTheory.Integrable (fun y ↦ ψ x y * f y) μ :=
    hxψ.integrable_mul (MeasureTheory.Lp.memLp f)
  calc
    kernelFunction μ (fun x y ↦ φ x y - ψ x y) f x = ∫ y, (φ x y - ψ x y) * f y ∂μ := by
      rfl
    _ = ∫ y, (φ x y * f y - ψ x y * f y) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y, φ x y * f y ∂μ - ∫ y, ψ x y * f y ∂μ := by
      exact MeasureTheory.integral_sub hφ_int hψ_int
    _ = kernelFunction μ φ f x - kernelFunction μ ψ f x := by
      rfl

/-- Helper for Example 2.4: a rectangle kernel realizes the expected rank-one operator. -/
private theorem rectangleKernelOperator_eq_rankOne
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hμt : μ t < ∞) (c : ℝ) :
    canonicalKernelOperator μ (rectangleKernel (Ω := Ω) s t c)
        (rectangleKernel_memLp (μ := μ) s t hs ht hμs hμt c) =
      InnerProductSpace.rankOne ℝ
        (c • MeasureTheory.indicatorConstLp 2 hs hμs.ne (1 : ℝ))
        (MeasureTheory.indicatorConstLp 2 ht hμt.ne (1 : ℝ)) := by
  let u : MeasureTheory.Lp ℝ 2 μ := c • MeasureTheory.indicatorConstLp 2 hs hμs.ne (1 : ℝ)
  let v : MeasureTheory.Lp ℝ 2 μ := MeasureTheory.indicatorConstLp 2 ht hμt.ne (1 : ℝ)
  apply kernelOperator_ext (μ := μ) (k := rectangleKernel (Ω := Ω) s t c)
  · exact
      canonicalKernelOperator_isKernelOperator (μ := μ)
        (k := rectangleKernel (Ω := Ω) s t c)
        (rectangleKernel_memLp (μ := μ) s t hs ht hμs hμt c)
  · intro f
    have h_indicator_integral :
        ∫ y, t.indicator (fun _ ↦ (1 : ℝ)) y * f y ∂μ = inner ℝ v f := by
      -- Replace the raw indicator by the `indicatorConstLp` representative before using the `L²`
      -- inner-product formula.
      calc
        ∫ y, t.indicator (fun _ ↦ (1 : ℝ)) y * f y ∂μ = ∫ y, v y * f y ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
              [MeasureTheory.indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
                (hs := ht) (hμs := hμt.ne) (c := (1 : ℝ))] with y hy
          simp [v, hy]
        _ = inner ℝ v f := by
          rw [MeasureTheory.L2.inner_def]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          simp [mul_comm]
    -- Compare the rank-one formula and the raw Fredholm integral pointwise.
    filter_upwards
        [MeasureTheory.indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
          (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ)),
          MeasureTheory.Lp.coeFn_smul c (MeasureTheory.indicatorConstLp 2 hs hμs.ne (1 : ℝ)),
          MeasureTheory.Lp.coeFn_smul (inner ℝ v f) u] with x hxInd hxU hxRank
    have hu :
        u x = c * s.indicator (fun _ ↦ (1 : ℝ)) x := by
      simpa [u, Pi.smul_apply, hxInd] using hxU
    by_cases hx : x ∈ s
    · calc
        (InnerProductSpace.rankOne ℝ u v f) x = (inner ℝ v f) * c := by
          calc
            (InnerProductSpace.rankOne ℝ u v f) x = (inner ℝ v f) * u x := by
              rw [InnerProductSpace.rankOne_apply, hxRank]
              simp [Pi.smul_apply]
            _ = (inner ℝ v f) * c := by
              simp [hu, hx]
        _ = c * inner ℝ v f := by ring
        _ = c * ∫ y, t.indicator (fun _ ↦ (1 : ℝ)) y * f y ∂μ := by
          rw [← h_indicator_integral]
        _ = ∫ y, c * (t.indicator (fun _ ↦ (1 : ℝ)) y * f y) ∂μ := by
          rw [← MeasureTheory.integral_const_mul]
        _ = ∫ y, rectangleKernel (Ω := Ω) s t c x y * f y ∂μ := by
          simp [rectangleKernel, hx, mul_assoc]
        _ = kernelFunction μ (rectangleKernel (Ω := Ω) s t c) f x := by
          rw [kernelFunction_apply]
    · calc
        (InnerProductSpace.rankOne ℝ u v f) x = 0 := by
          calc
            (InnerProductSpace.rankOne ℝ u v f) x = (inner ℝ v f) * u x := by
              rw [InnerProductSpace.rankOne_apply, hxRank]
              simp [Pi.smul_apply]
            _ = 0 := by
              simp [hu, hx]
        _ = ∫ y, rectangleKernel (Ω := Ω) s t c x y * f y ∂μ := by
          simp [rectangleKernel, hx]
        _ = kernelFunction μ (rectangleKernel (Ω := Ω) s t c) f x := by
          rw [kernelFunction_apply]

/-- Helper for Example 2.4: every rectangle kernel induces a compact operator. -/
private theorem rectangleKernelOperator_isCompact
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hμt : μ t < ∞) (c : ℝ) :
    IsCompactOperator
      (canonicalKernelOperator μ (rectangleKernel (Ω := Ω) s t c)
        (rectangleKernel_memLp (μ := μ) s t hs ht hμs hμt c)) := by
  -- The rectangle model is exactly a rank-one operator on `L²(Ω)`.
  rw [rectangleKernelOperator_eq_rankOne (μ := μ) s t hs ht hμs hμt c]
  exact rankOne_isCompactOperator (μ := μ) _ _

/-- Helper for Example 2.4: adding two product kernels adds the raw Fredholm transforms a.e. -/
private theorem kernelFunction_kernelAdd_ae
    {φ ψ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hψ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (f : MeasureTheory.Lp ℝ 2 μ) :
    kernelFunction μ (fun x y ↦ φ x y + ψ x y) f =ᵐ[μ]
      fun x ↦ kernelFunction μ φ f x + kernelFunction μ ψ f x := by
  -- For almost every section, linearity of the Bochner integral gives the pointwise addition rule.
  filter_upwards
      [kernelSection_memLp_ae (μ := μ) (k := φ) hφ,
        kernelSection_memLp_ae (μ := μ) (k := ψ) hψ] with x hxφ hxψ
  have hφ_int : MeasureTheory.Integrable (fun y ↦ φ x y * f y) μ :=
    hxφ.integrable_mul (MeasureTheory.Lp.memLp f)
  have hψ_int : MeasureTheory.Integrable (fun y ↦ ψ x y * f y) μ :=
    hxψ.integrable_mul (MeasureTheory.Lp.memLp f)
  calc
    kernelFunction μ (fun x y ↦ φ x y + ψ x y) f x = ∫ y, (φ x y + ψ x y) * f y ∂μ := by
      rfl
    _ = ∫ y, (φ x y * f y + ψ x y * f y) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y, φ x y * f y ∂μ + ∫ y, ψ x y * f y ∂μ := by
      exact MeasureTheory.integral_add hφ_int hψ_int
    _ = kernelFunction μ φ f x + kernelFunction μ ψ f x := by
      rfl

/-- Helper for Example 2.4: the zero kernel realizes the zero operator. -/
private theorem canonicalKernelOperator_zero :
    canonicalKernelOperator μ (fun _ _ ↦ 0)
        (MeasureTheory.MemLp.zero' (μ := MeasureTheory.Measure.prod μ μ)
          (p := (2 : ℝ≥0∞))) =
      0 := by
  -- The zero kernel and the zero operator satisfy the same defining Fredholm formula.
  apply kernelOperator_ext (μ := μ) (k := fun _ _ ↦ 0)
  · exact canonicalKernelOperator_isKernelOperator (μ := μ) (k := fun _ _ ↦ 0)
      (MeasureTheory.MemLp.zero' (μ := MeasureTheory.Measure.prod μ μ)
        (p := (2 : ℝ≥0∞)))
  · intro f
    filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ (2 : ℝ≥0∞) μ] with x hxZero
    change ((0 : MeasureTheory.Lp ℝ 2 μ) : Ω → ℝ) x =
      kernelFunction μ (fun _ _ ↦ 0) f x
    have hxZero' : (((0 : MeasureTheory.Lp ℝ 2 μ) : Ω → ℝ) x) = 0 := by
      simpa using hxZero
    rw [hxZero']
    simp [kernelFunction]

/-- Helper for Example 2.4: pointwise-equal kernels define the same canonical Fredholm operator. -/
private theorem canonicalKernelOperator_congr
    {φ ψ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hψ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hEq : ∀ x y, φ x y = ψ x y) :
    canonicalKernelOperator μ φ hφ = canonicalKernelOperator μ ψ hψ := by
  -- Identify both operators by comparing their almost-everywhere kernel formulas.
  apply kernelOperator_ext (μ := μ) (k := φ)
  · exact canonicalKernelOperator_isKernelOperator (μ := μ) (k := φ) hφ
  · intro f
    filter_upwards
        [canonicalKernelOperator_isKernelOperator (μ := μ) (k := ψ) hψ f] with x hx
    rw [hx, kernelFunction_apply, kernelFunction_apply]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [hEq]

/-- Helper for Example 2.4: the canonical realization of a sum kernel is the sum of the canonical
realizations. -/
private theorem canonicalKernelOperator_add
    {φ ψ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hψ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hsum :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2 + ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    canonicalKernelOperator μ (fun x y ↦ φ x y + ψ x y) hsum =
      canonicalKernelOperator μ φ hφ + canonicalKernelOperator μ ψ hψ := by
  -- Compare both operators through the defining kernel formula of the sum kernel.
  apply kernelOperator_ext (μ := μ) (k := fun x y ↦ φ x y + ψ x y)
  · exact canonicalKernelOperator_isKernelOperator (μ := μ) (k := fun x y ↦ φ x y + ψ x y) hsum
  · intro f
    filter_upwards
        [MeasureTheory.Lp.coeFn_add (canonicalKernelOperator μ φ hφ f)
          (canonicalKernelOperator μ ψ hψ f),
          canonicalKernelOperator_isKernelOperator (μ := μ) (k := φ) hφ f,
          canonicalKernelOperator_isKernelOperator (μ := μ) (k := ψ) hψ f,
          kernelFunction_kernelAdd_ae (μ := μ) (φ := φ) (ψ := ψ) hφ hψ f] with
        x hxAdd hxφ hxψ hKernel
    calc
      ((canonicalKernelOperator μ φ hφ + canonicalKernelOperator μ ψ hψ) f) x =
          (canonicalKernelOperator μ φ hφ f) x + (canonicalKernelOperator μ ψ hψ f) x := by
            simpa using hxAdd
      _ = kernelFunction μ φ f x + kernelFunction μ ψ f x := by
            rw [hxφ, hxψ]
      _ = kernelFunction μ (fun x y ↦ φ x y + ψ x y) f x := by
            symm
            exact hKernel

/-- Helper for Example 2.4: finite sums of rectangle kernels are square-integrable on
`Ω × Ω`. -/
private theorem finiteRectKernel_memLp
    {ι : Type*} (A : Finset ι) (c : ι → ℝ) (s t : ι → Set Ω)
    (hs : ∀ i ∈ A, MeasurableSet (s i))
    (ht : ∀ i ∈ A, MeasurableSet (t i))
    (hμs : ∀ i ∈ A, μ (s i) < ∞)
    (hμt : ∀ i ∈ A, μ (t i) < ∞) :
    MeasureTheory.MemLp
      (fun z : Ω × Ω ↦
        ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) z.1 z.2)
      2 (MeasureTheory.Measure.prod μ μ) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simpa using
        (MeasureTheory.MemLp.zero' (μ := MeasureTheory.Measure.prod μ μ)
          (p := (2 : ℝ≥0∞)))
  | @insert a A ha ih =>
      -- Add one rectangle summand to the already square-integrable finite rectangle family.
      have hRect :
          MeasureTheory.MemLp
            (fun z : Ω × Ω ↦ rectangleKernel (Ω := Ω) (s a) (t a) (c a) z.1 z.2)
            2 (MeasureTheory.Measure.prod μ μ) :=
        rectangleKernel_memLp (μ := μ) (s a) (t a) (hs a (Finset.mem_insert_self a A))
          (ht a (Finset.mem_insert_self a A)) (hμs a (Finset.mem_insert_self a A))
          (hμt a (Finset.mem_insert_self a A)) (c a)
      have hRest :
          MeasureTheory.MemLp
            (fun z : Ω × Ω ↦
              ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) z.1 z.2)
            2 (MeasureTheory.Measure.prod μ μ) :=
        ih
          (fun i hi ↦ hs i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hμs i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hμt i (Finset.mem_insert_of_mem hi))
      have hAdd :
          MeasureTheory.MemLp
            (fun z : Ω × Ω ↦
              rectangleKernel (Ω := Ω) (s a) (t a) (c a) z.1 z.2 +
                ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) z.1 z.2)
            2 (MeasureTheory.Measure.prod μ μ) := by
        convert hRect.add hRest using 1
        funext z
        simp [Pi.add_apply]
      simpa [Finset.sum_insert, ha] using hAdd

/-- Helper for Example 2.4: finite sums of rectangle kernels induce compact operators. -/
private theorem finiteRectKernelOperator_isCompact
    {ι : Type*} (A : Finset ι) (c : ι → ℝ) (s t : ι → Set Ω)
    (hs : ∀ i ∈ A, MeasurableSet (s i))
    (ht : ∀ i ∈ A, MeasurableSet (t i))
    (hμs : ∀ i ∈ A, μ (s i) < ∞)
    (hμt : ∀ i ∈ A, μ (t i) < ∞) :
    IsCompactOperator
      (canonicalKernelOperator μ
        (fun x y ↦ ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)
        (finiteRectKernel_memLp (μ := μ) A c s t hs ht hμs hμt)) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      -- The empty sum is the zero kernel, so the resulting operator is the zero compact operator.
      have hEmptyEq :
          canonicalKernelOperator μ
              (fun x y ↦ ∑ i ∈ (∅ : Finset ι), rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)
              (finiteRectKernel_memLp (μ := μ) (∅ : Finset ι) c s t hs ht hμs hμt) =
            0 := by
        calc
          canonicalKernelOperator μ
              (fun x y ↦ ∑ i ∈ (∅ : Finset ι), rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)
              (finiteRectKernel_memLp (μ := μ) (∅ : Finset ι) c s t hs ht hμs hμt) =
            canonicalKernelOperator μ (fun _ _ ↦ 0)
              (MeasureTheory.MemLp.zero' (μ := MeasureTheory.Measure.prod μ μ)
                (p := (2 : ℝ≥0∞))) := by
                  apply canonicalKernelOperator_congr (μ := μ)
                    (hφ := finiteRectKernel_memLp (μ := μ) (∅ : Finset ι) c s t hs ht hμs hμt)
                    (hψ := MeasureTheory.MemLp.zero' (μ := MeasureTheory.Measure.prod μ μ)
                      (p := (2 : ℝ≥0∞)))
                  intro x y
                  simp
          _ = 0 := canonicalKernelOperator_zero (μ := μ)
      rw [hEmptyEq]
      change IsCompactOperator (0 : MeasureTheory.Lp ℝ 2 μ → MeasureTheory.Lp ℝ 2 μ)
      exact isCompactOperator_zero
  | @insert a A ha ih =>
      -- Split the finite sum into the new rectangle plus the previous finite rectangle operator.
      have hRectCompact :
          IsCompactOperator
            (canonicalKernelOperator μ
              (rectangleKernel (Ω := Ω) (s a) (t a) (c a))
              (rectangleKernel_memLp (μ := μ) (s a) (t a)
                (hs a (Finset.mem_insert_self a A))
                (ht a (Finset.mem_insert_self a A))
                (hμs a (Finset.mem_insert_self a A))
                (hμt a (Finset.mem_insert_self a A)) (c a))) :=
        rectangleKernelOperator_isCompact (μ := μ) (s a) (t a)
          (hs a (Finset.mem_insert_self a A))
          (ht a (Finset.mem_insert_self a A))
          (hμs a (Finset.mem_insert_self a A))
          (hμt a (Finset.mem_insert_self a A)) (c a)
      have hRestCompact :
          IsCompactOperator
            (canonicalKernelOperator μ
              (fun x y ↦ ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)
              (finiteRectKernel_memLp (μ := μ) A c s t
                (fun i hi ↦ hs i (Finset.mem_insert_of_mem hi))
                (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi))
                (fun i hi ↦ hμs i (Finset.mem_insert_of_mem hi))
                (fun i hi ↦ hμt i (Finset.mem_insert_of_mem hi)))) :=
        ih
          (fun i hi ↦ hs i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hμs i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hμt i (Finset.mem_insert_of_mem hi))
      have hRect :
          MeasureTheory.MemLp
            (fun z : Ω × Ω ↦ rectangleKernel (Ω := Ω) (s a) (t a) (c a) z.1 z.2)
            2 (MeasureTheory.Measure.prod μ μ) :=
        rectangleKernel_memLp (μ := μ) (s a) (t a)
          (hs a (Finset.mem_insert_self a A))
          (ht a (Finset.mem_insert_self a A))
          (hμs a (Finset.mem_insert_self a A))
          (hμt a (Finset.mem_insert_self a A)) (c a)
      have hRest :
          MeasureTheory.MemLp
            (fun z : Ω × Ω ↦
              ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) z.1 z.2)
            2 (MeasureTheory.Measure.prod μ μ) :=
        finiteRectKernel_memLp (μ := μ) A c s t
          (fun i hi ↦ hs i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hμs i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hμt i (Finset.mem_insert_of_mem hi))
      have hAdd :
          MeasureTheory.MemLp
            (fun z : Ω × Ω ↦
              rectangleKernel (Ω := Ω) (s a) (t a) (c a) z.1 z.2 +
                ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) z.1 z.2)
            2 (MeasureTheory.Measure.prod μ μ) := by
        convert hRect.add hRest using 1
        funext z
        simp [Pi.add_apply]
      have hInsertEq :
          canonicalKernelOperator μ
              (fun x y ↦ ∑ i ∈ insert a A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)
              (finiteRectKernel_memLp (μ := μ) (insert a A) c s t hs ht hμs hμt) =
            canonicalKernelOperator μ
              (fun x y ↦ rectangleKernel (Ω := Ω) (s a) (t a) (c a) x y +
                ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)
              hAdd := by
        apply canonicalKernelOperator_congr (μ := μ)
          (hφ := finiteRectKernel_memLp (μ := μ) (insert a A) c s t hs ht hμs hμt)
          (hψ := hAdd)
        intro x y
        simp [Finset.sum_insert, ha]
      rw [hInsertEq, canonicalKernelOperator_add (μ := μ) (hφ := hRect) (hψ := hRest)
        (hsum := hAdd)]
      change
        IsCompactOperator
          (⇑(canonicalKernelOperator μ (rectangleKernel (Ω := Ω) (s a) (t a) (c a)) hRect) +
            ⇑(canonicalKernelOperator μ
              (fun x y ↦ ∑ i ∈ A, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y) hRest))
      exact hRectCompact.add hRestCompact

/-- Helper for Example 2.4: measurable rectangles generate a measure-dense set algebra for the
product measure. -/
private theorem measurableRectangleAlgebraMeasureDense [MeasureTheory.SigmaFinite μ] :
    (MeasureTheory.Measure.prod μ μ).MeasureDense
      (MeasureTheory.generateSetAlgebra
        (Set.image2 (fun s t => s ×ˢ t)
          {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) := by
  let 𝒜 : Set (Set (Ω × Ω)) :=
    Set.image2 (fun s t => s ×ˢ t)
      {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t}
  have h_span :
      (MeasureTheory.Measure.prod μ μ).FiniteSpanningSetsIn 𝒜 := by
    -- The product finite spanning sets already live in measurable rectangles.
    simpa [𝒜] using (μ.toFiniteSpanningSetsIn.prod μ.toFiniteSpanningSetsIn)
  have h_span_alg :
      (MeasureTheory.Measure.prod μ μ).FiniteSpanningSetsIn
        (MeasureTheory.generateSetAlgebra 𝒜) :=
    h_span.mono MeasureTheory.self_subset_generateSetAlgebra
  have h_generate :
      Prod.instMeasurableSpace =
        MeasurableSpace.generateFrom (MeasureTheory.generateSetAlgebra 𝒜) := by
    -- Passing from rectangles to the generated set algebra does not change the product σ-algebra.
    rw [MeasureTheory.generateFrom_generateSetAlgebra_eq, generateFrom_prod]
  exact
    MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite
      MeasureTheory.isSetAlgebra_generateSetAlgebra h_span_alg h_generate

/-- Helper for Example 2.4: the indicator of a measurable rectangle is exactly a one-term rectangle
kernel. -/
private theorem rectangleIndicator_eq_rectangleKernel
    (s t : Set Ω) (c : ℝ) :
    (fun z : Ω × Ω ↦ (s ×ˢ t).indicator (fun _ ↦ c) z) =
      fun z : Ω × Ω ↦ rectangleKernel (Ω := Ω) s t c z.1 z.2 := by
  -- Expand membership in the rectangle and simplify each of the four pointwise cases.
  funext z
  by_cases hx : z.1 ∈ s <;> by_cases hy : z.2 ∈ t <;>
    simp [rectangleKernel, hx, hy]

/-- Helper for Example 2.4: a product kernel is a finite sum of measurable finite-measure
rectangles. -/
private def IsFiniteRectKernel (φ : Ω → Ω → ℝ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℝ) (s t : Fin n → Set Ω),
    (∀ i, MeasurableSet (s i)) ∧
    (∀ i, MeasurableSet (t i)) ∧
    (∀ i, μ (s i) < ∞) ∧
    (∀ i, μ (t i) < ∞) ∧
    φ = fun x y ↦ ∑ i : Fin n, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y

/-- Helper for Example 2.4: every finite rectangle kernel family is square-integrable on the
product space. -/
private theorem IsFiniteRectKernel.memLp
    {φ : Ω → Ω → ℝ}
    (hφ : IsFiniteRectKernel (μ := μ) φ) :
    MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
      (MeasureTheory.Measure.prod μ μ) := by
  classical
  rcases hφ with ⟨n, c, s, t, hs, ht, hμs, hμt, rfl⟩
  simpa using
    finiteRectKernel_memLp (μ := μ) (A := Finset.univ) c s t
      (fun i _ ↦ hs i) (fun i _ ↦ ht i) (fun i _ ↦ hμs i) (fun i _ ↦ hμt i)

/-- Helper for Example 2.4: every finite rectangle kernel induces a compact canonical Fredholm
operator. -/
private theorem IsFiniteRectKernel.isCompactOperator
    {φ : Ω → Ω → ℝ}
    (hφ : IsFiniteRectKernel (μ := μ) φ) :
    IsCompactOperator (canonicalKernelOperator μ φ (hφ.memLp (μ := μ))) := by
  classical
  rcases hφ with ⟨n, c, s, t, hs, ht, hμs, hμt, rfl⟩
  simpa using
    finiteRectKernelOperator_isCompact (μ := μ) (A := Finset.univ) c s t
      (fun i _ ↦ hs i) (fun i _ ↦ ht i) (fun i _ ↦ hμs i) (fun i _ ↦ hμt i)

/-- Helper for Example 2.4: multiplying two rectangle kernels multiplies their coefficients and
intersects their sides. -/
private theorem rectangleKernel_mul
    (s t u v : Set Ω) (c d : ℝ) (x y : Ω) :
    rectangleKernel (Ω := Ω) s t c x y * rectangleKernel (Ω := Ω) u v d x y =
      rectangleKernel (Ω := Ω) (s ∩ u) (t ∩ v) (c * d) x y := by
  -- Expand the four indicators pointwise and simplify the resulting cases.
  by_cases hs : x ∈ s <;> by_cases hu : x ∈ u <;>
      by_cases ht : y ∈ t <;> by_cases hv : y ∈ v <;>
    simp [rectangleKernel, hs, hu, ht, hv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 2.4: a single measurable finite-measure rectangle is a finite rectangle
kernel. -/
private theorem isFiniteRectKernel_rectangle
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hμt : μ t < ∞) (c : ℝ) :
    IsFiniteRectKernel (μ := μ) (rectangleKernel (Ω := Ω) s t c) := by
  refine ⟨1, fun _ ↦ c, fun _ ↦ s, fun _ ↦ t, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa using hs
  · intro i
    simpa using ht
  · intro i
    simpa using hμs
  · intro i
    simpa using hμt
  · funext x y
    simp

/-- Helper for Example 2.4: the zero kernel is a finite rectangle kernel. -/
private theorem isFiniteRectKernel_zero :
    IsFiniteRectKernel (μ := μ) (fun _ _ ↦ 0) := by
  refine ⟨0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · funext x y
    simp

/-- Helper for Example 2.4: a finite family of rectangle kernels indexed by any finite type can be
repackaged into the `Fin n` witness used by `IsFiniteRectKernel`. -/
private theorem isFiniteRectKernel_ofFintype
    {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (s t : ι → Set Ω)
    (hs : ∀ i, MeasurableSet (s i))
    (ht : ∀ i, MeasurableSet (t i))
    (hμs : ∀ i, μ (s i) < ∞)
    (hμt : ∀ i, μ (t i) < ∞) :
    IsFiniteRectKernel (μ := μ)
      (fun x y ↦ ∑ i, rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, c ∘ e.symm, s ∘ e.symm, t ∘ e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [e, Function.comp] using hs (e.symm i)
  · intro i
    simpa [e, Function.comp] using ht (e.symm i)
  · intro i
    simpa [e, Function.comp] using hμs (e.symm i)
  · intro i
    simpa [e, Function.comp] using hμt (e.symm i)
  · -- Reindex the finite sum along `Fintype.equivFin` to match the packaged `Fin n` witness.
    funext x y
    simpa [e, Function.comp] using
      (e.symm.sum_comp
        (fun i : ι ↦ rectangleKernel (Ω := Ω) (s i) (t i) (c i) x y)).symm

/-- Helper for Example 2.4: scalar multiplication preserves the finite rectangle kernel class. -/
private theorem IsFiniteRectKernel.smul
    {φ : Ω → Ω → ℝ}
    (a : ℝ) (hφ : IsFiniteRectKernel (μ := μ) φ) :
    IsFiniteRectKernel (μ := μ) (fun x y ↦ a * φ x y) := by
  classical
  rcases hφ with ⟨n, c, s, t, hs, ht, hμs, hμt, rfl⟩
  refine ⟨n, fun i ↦ a * c i, s, t, hs, ht, hμs, hμt, ?_⟩
  -- Rescaling the coefficients rescales the whole finite rectangle sum pointwise.
  funext x y
  simp [rectangleKernel, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 2.4: finite rectangle kernels are closed under pointwise addition. -/
private theorem IsFiniteRectKernel.add
    {φ ψ : Ω → Ω → ℝ}
    (hφ : IsFiniteRectKernel (μ := μ) φ)
    (hψ : IsFiniteRectKernel (μ := μ) ψ) :
    IsFiniteRectKernel (μ := μ) (fun x y ↦ φ x y + ψ x y) := by
  classical
  rcases hφ with ⟨n, cφ, sφ, tφ, hsφ, htφ, hμsφ, hμtφ, rfl⟩
  rcases hψ with ⟨m, cψ, sψ, tψ, hsψ, htψ, hμsψ, hμtψ, rfl⟩
  -- Reindex the two finite witnesses along a disjoint sum type.
  simpa [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using
    (isFiniteRectKernel_ofFintype
      (μ := μ)
      (c := Sum.elim cφ cψ)
      (s := Sum.elim sφ sψ)
      (t := Sum.elim tφ tψ)
      (hs := fun i ↦ by cases i <;> simp [hsφ, hsψ])
      (ht := fun i ↦ by cases i <;> simp [htφ, htψ])
      (hμs := fun i ↦ by cases i <;> simp [hμsφ, hμsψ])
      (hμt := fun i ↦ by cases i <;> simp [hμtφ, hμtψ]))

/-- Helper for Example 2.4: finite rectangle kernels are closed under pointwise multiplication. -/
private theorem IsFiniteRectKernel.mul
    {φ ψ : Ω → Ω → ℝ}
    (hφ : IsFiniteRectKernel (μ := μ) φ)
    (hψ : IsFiniteRectKernel (μ := μ) ψ) :
    IsFiniteRectKernel (μ := μ) (fun x y ↦ φ x y * ψ x y) := by
  classical
  rcases hφ with ⟨n, cφ, sφ, tφ, hsφ, htφ, hμsφ, hμtφ, rfl⟩
  rcases hψ with ⟨m, cψ, sψ, tψ, hsψ, htψ, hμsψ, hμtψ, rfl⟩
  -- Multiply the two finite witnesses termwise over the finite product index.
  simpa [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, rectangleKernel_mul] using
    (isFiniteRectKernel_ofFintype
      (μ := μ)
      (c := fun ij : Fin m × Fin n ↦ cφ ij.2 * cψ ij.1)
      (s := fun ij : Fin m × Fin n ↦ sφ ij.2 ∩ sψ ij.1)
      (t := fun ij : Fin m × Fin n ↦ tφ ij.2 ∩ tψ ij.1)
      (hs := fun ij ↦ (hsφ ij.2).inter (hsψ ij.1))
      (ht := fun ij ↦ (htφ ij.2).inter (htψ ij.1))
      (hμs := fun ij ↦ lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) (hμsφ ij.2))
      (hμt := fun ij ↦ lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) (hμtφ ij.2)))

/-- Helper for Example 2.4: intersecting a global rectangle-algebra set with a finite box keeps it
inside the corresponding box-local rectangle algebra. -/
private theorem rectAlgebraInterFiniteBox_memGenerateSetAlgebra
    (U V : Set Ω) (a : Set (Ω × Ω))
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (ha :
      a ∈ MeasureTheory.generateSetAlgebra
        (Set.image2 (fun s t : Set Ω ↦ s ×ˢ t)
          {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :
    a ∩ (U ×ˢ V) ∈
      MeasureTheory.generateSetAlgebra
        (Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
          {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t}) := by
  classical
  let localRectangles : Set (Set (Ω × Ω)) :=
    Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
      {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t}
  let box : Set (Ω × Ω) := U ×ˢ V
  have hbox : box ∈ MeasureTheory.generateSetAlgebra localRectangles := by
    -- The whole finite box is itself one generator of the local rectangle algebra.
    refine MeasureTheory.generateSetAlgebra.base box ?_
    refine ⟨Set.univ, MeasurableSet.univ, Set.univ, MeasurableSet.univ, ?_⟩
    ext z
    simp [box]
  induction ha with
  | base a ha =>
      rcases ha with ⟨s, hs, t, ht, rfl⟩
      have h_eq : (s ×ˢ t : Set (Ω × Ω)) ∩ box = (s ∩ U) ×ˢ (t ∩ V) := by
        -- Intersecting a rectangle with the ambient box just intersects each factor.
        ext z
        simp [box, and_assoc, and_left_comm, and_comm]
      have hbase : (s ∩ U) ×ˢ (t ∩ V) ∈ MeasureTheory.generateSetAlgebra localRectangles := by
        exact MeasureTheory.generateSetAlgebra.base _ ⟨s, hs, t, ht, rfl⟩
      simpa [box, h_eq] using hbase
  | empty =>
      -- Intersecting the empty set with the box stays empty.
      have hempty : (∅ : Set (Ω × Ω)) ∈ MeasureTheory.generateSetAlgebra localRectangles :=
        MeasureTheory.generateSetAlgebra.empty
      simpa [box] using hempty
  | compl a ha ih =>
      have hcompl :
          (a ∩ box)ᶜ ∈ MeasureTheory.generateSetAlgebra localRectangles :=
        MeasureTheory.generateSetAlgebra.compl _ ih
      -- Inside the fixed box, complement is implemented by intersecting with the complement of
      -- the already-boxed set.
      have hinter :
          box ∩ (a ∩ box)ᶜ ∈ MeasureTheory.generateSetAlgebra localRectangles :=
        MeasureTheory.isSetAlgebra_generateSetAlgebra.inter_mem hbox hcompl
      have h_eq : aᶜ ∩ box = box ∩ (a ∩ box)ᶜ := by
        ext z
        by_cases hz_box : z ∈ box <;> by_cases hz_a : z ∈ a <;> simp [box, hz_box, hz_a]
      simpa [box, h_eq] using hinter
  | union a b ha hb ihA ihB =>
      -- Intersection with the fixed box distributes over union.
      have hunion :
          (a ∩ box) ∪ (b ∩ box) ∈ MeasureTheory.generateSetAlgebra localRectangles :=
        MeasureTheory.generateSetAlgebra.union _ _ ihA ihB
      have h_eq : (a ∪ b) ∩ box = (a ∩ box) ∪ (b ∩ box) := by
        ext z
        constructor
        · intro hz
          rcases hz with ⟨hzab, hzbox⟩
          rcases hzab with hza | hzb
          · exact Or.inl ⟨hza, hzbox⟩
          · exact Or.inr ⟨hzb, hzbox⟩
        · intro hz
          rcases hz with ⟨hza, hzbox⟩ | ⟨hzb, hzbox⟩
          · exact ⟨Or.inl hza, hzbox⟩
          · exact ⟨Or.inr hzb, hzbox⟩
      exact h_eq ▸ hunion

/-- Helper for Example 2.4: inside a finite product box, every set from the rectangle-generated
set algebra has an indicator kernel which is exactly a finite rectangle sum. -/
private theorem finiteBoxRectAlgebraIndicator_isFiniteRectKernel
    (U V : Set Ω) (a : Set (Ω × Ω))
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hμU : μ U < ∞) (hμV : μ V < ∞)
    (ha :
      a ∈ MeasureTheory.generateSetAlgebra
        (Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
          {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :
    IsFiniteRectKernel (μ := μ)
      (fun x y ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) (x, y))) := by
  classical
  let box : Set (Ω × Ω) := U ×ˢ V
  have hbox :
      IsFiniteRectKernel (μ := μ)
        (fun x y ↦ (box.indicator (fun _ ↦ (1 : ℝ)) (x, y))) := by
    have hrect :
        IsFiniteRectKernel (μ := μ) (rectangleKernel (Ω := Ω) U V 1) :=
      isFiniteRectKernel_rectangle (μ := μ) U V hU hV hμU hμV 1
    -- The indicator of the whole finite box is already a one-term rectangle kernel.
    have hbox_eq :
        (fun x y ↦ (box.indicator (fun _ ↦ (1 : ℝ)) (x, y))) =
          rectangleKernel (Ω := Ω) U V 1 := by
      funext x y
      by_cases hx : x ∈ U <;> by_cases hy : y ∈ V <;>
        simp [box, rectangleKernel, hx, hy]
    simpa [hbox_eq] using hrect
  induction ha with
  | base a ha =>
      rcases ha with ⟨s, hs, t, ht, rfl⟩
      have hs' : MeasurableSet (s ∩ U) := hs.inter hU
      have ht' : MeasurableSet (t ∩ V) := ht.inter hV
      have hμs' : μ (s ∩ U) < ∞ := lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hμU
      have hμt' : μ (t ∩ V) < ∞ := lt_of_le_of_lt
        (MeasureTheory.measure_mono Set.inter_subset_right) hμV
      have hrect :
          IsFiniteRectKernel (μ := μ)
            (rectangleKernel (Ω := Ω) (s ∩ U) (t ∩ V) 1) :=
        isFiniteRectKernel_rectangle (μ := μ) (s ∩ U) (t ∩ V) hs' ht' hμs' hμt' 1
      -- A generator already lies in the box, so its box-restricted indicator is exactly the
      -- corresponding one-term rectangle kernel.
      have hrect_eq :
          (fun x y ↦ (((s ∩ U) ×ˢ (t ∩ V) ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) =
            rectangleKernel (Ω := Ω) (s ∩ U) (t ∩ V) 1 := by
        funext x y
        by_cases hx : x ∈ s ∩ U
        · rcases hx with ⟨hxs, hxU⟩
          by_cases hy : y ∈ t ∩ V
          · rcases hy with ⟨hyt, hyV⟩
            simp [box, rectangleKernel, hxs, hxU, hyt, hyV]
          · simp [box, rectangleKernel, hxs, hxU, hy]
        · by_cases hy : y ∈ t ∩ V <;> simp [box, rectangleKernel, hx, hy]
      exact hrect_eq ▸ hrect
  | empty =>
      -- The empty indicator is the zero kernel.
      simpa [box] using (isFiniteRectKernel_zero (μ := μ))
  | compl a ha ih =>
      have hneg : IsFiniteRectKernel (μ := μ)
          (fun x y ↦ (-1 : ℝ) * ((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) :=
        IsFiniteRectKernel.smul (μ := μ) (-1) ih
      have hsum :
          IsFiniteRectKernel (μ := μ)
            (fun x y ↦
              (box.indicator (fun _ ↦ (1 : ℝ)) (x, y)) +
                (-1 : ℝ) * ((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) :=
        IsFiniteRectKernel.add (μ := μ) hbox hneg
      -- Inside the fixed box, complement becomes `1_box - 1_a`.
      have hcompl_eq :
          (fun x y ↦ (((aᶜ ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)))) =
            (fun x y ↦
              (box.indicator (fun _ ↦ (1 : ℝ)) (x, y)) +
                (-1 : ℝ) * ((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) := by
        funext x y
        by_cases hz_box : (x, y) ∈ box <;> by_cases hz_a : (x, y) ∈ a <;>
          simp [hz_box, hz_a, box, sub_eq_add_neg]
      exact hcompl_eq ▸ hsum
  | union a b ha hb ihA ihB =>
      have hmul :
          IsFiniteRectKernel (μ := μ)
            (fun x y ↦
              ((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) *
                ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) :=
        IsFiniteRectKernel.mul (μ := μ) ihA ihB
      have hsum :
          IsFiniteRectKernel (μ := μ)
            (fun x y ↦
              ((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) +
                ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) :=
        IsFiniteRectKernel.add (μ := μ) ihA ihB
      have hnegMul :
          IsFiniteRectKernel (μ := μ)
            (fun x y ↦
              (-1 : ℝ) *
                (((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) *
                  ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)))) :=
        IsFiniteRectKernel.smul (μ := μ) (-1) hmul
      have hfinal :
          IsFiniteRectKernel (μ := μ)
            (fun x y ↦
              (((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) +
                  ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) +
                (-1 : ℝ) *
                  (((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) *
                    ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)))) :=
        IsFiniteRectKernel.add (μ := μ) hsum hnegMul
      -- On `{0,1}`-valued indicators inside the box, union is `1_a + 1_b - 1_a * 1_b`.
      have hunion_eq :
          (fun x y ↦ ((((a ∪ b) ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)))) =
            (fun x y ↦
              (((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) +
                  ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y))) +
                (-1 : ℝ) *
                  (((a ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)) *
                    ((b ∩ box).indicator (fun _ ↦ (1 : ℝ)) (x, y)))) := by
        funext x y
        by_cases hz_box : (x, y) ∈ box <;>
            by_cases hz_a : (x, y) ∈ a <;> by_cases hz_b : (x, y) ∈ b <;>
          simp [hz_box, hz_a, hz_b, box, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm]
      exact hunion_eq ▸ hfinal

/-- Helper for Example 2.4: a box-local rectangle algebra indicator is square-integrable on the
product space. -/
private theorem finiteBoxRectAlgebraIndicator_memLp
    (U V : Set Ω) (a : Set (Ω × Ω))
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hμU : μ U < ∞) (hμV : μ V < ∞)
    (ha :
      a ∈ MeasureTheory.generateSetAlgebra
        (Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
          {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :
    MeasureTheory.MemLp
      (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z))
      2 (MeasureTheory.Measure.prod μ μ) := by
  simpa using
    (IsFiniteRectKernel.memLp
      (μ := μ)
      (φ := fun x y ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) (x, y)))
      (finiteBoxRectAlgebraIndicator_isFiniteRectKernel (μ := μ) U V a hU hV hμU hμV ha))

/-- Helper for Example 2.4: the canonical operator of a box-local rectangle algebra indicator is
compact. -/
private theorem finiteBoxRectAlgebraIndicator_isCompactOperator
    (U V : Set Ω) (a : Set (Ω × Ω))
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hμU : μ U < ∞) (hμV : μ V < ∞)
    (ha :
      a ∈ MeasureTheory.generateSetAlgebra
        (Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
          {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :
    IsCompactOperator
      (canonicalKernelOperator μ
        (fun x y ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) (x, y)))
        (finiteBoxRectAlgebraIndicator_memLp (μ := μ) U V a hU hV hμU hμV ha)) := by
  simpa using
    (IsFiniteRectKernel.isCompactOperator
      (μ := μ)
      (φ := fun x y ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) (x, y)))
      (finiteBoxRectAlgebraIndicator_isFiniteRectKernel (μ := μ) U V a hU hV hμU hμV ha))

/-- Helper for Example 2.4: kernel differences control operator differences in norm. -/
private theorem canonicalKernelOperator_sub_norm_le
    {φ ψ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hψ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hsub :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2 - ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    ‖canonicalKernelOperator μ φ hφ - canonicalKernelOperator μ ψ hψ‖ ≤
      Real.sqrt
        (∫ z : Ω × Ω, (φ z.1 z.2 - ψ z.1 z.2) ^ (2 : ℕ)
          ∂(MeasureTheory.Measure.prod μ μ)) := by
  have hdiff :
      IsKernelOperator μ (fun x y ↦ φ x y - ψ x y)
        (canonicalKernelOperator μ φ hφ - canonicalKernelOperator μ ψ hψ) := by
    intro f
    -- Evaluate the operator difference pointwise and use the subtraction rule for kernel
    -- functions to identify the resulting kernel.
    filter_upwards
        [MeasureTheory.Lp.coeFn_sub (canonicalKernelOperator μ φ hφ f)
          (canonicalKernelOperator μ ψ hψ f),
          canonicalKernelOperator_isKernelOperator (μ := μ) (k := φ) hφ f,
          canonicalKernelOperator_isKernelOperator (μ := μ) (k := ψ) hψ f,
          kernelFunction_sub_ae (μ := μ) (φ := φ) (ψ := ψ) hφ hψ f] with x hxSub hxφ hxψ hxKernel
    calc
      ((canonicalKernelOperator μ φ hφ - canonicalKernelOperator μ ψ hψ) f) x =
          (canonicalKernelOperator μ φ hφ f) x - (canonicalKernelOperator μ ψ hψ f) x := by
            simpa using hxSub
      _ = kernelFunction μ φ f x - kernelFunction μ ψ f x := by
            rw [hxφ, hxψ]
      _ = kernelFunction μ (fun x y ↦ φ x y - ψ x y) f x := by
            symm
            exact hxKernel
  -- Once the difference operator is recognized as a kernel operator, the standard Hilbert-Schmidt
  -- norm bound finishes the comparison.
  exact kernelOperator_norm_le (μ := μ) (k := fun x y ↦ φ x y - ψ x y) hsub hdiff

/-- Helper for Example 2.4: the `L²(μ × μ)` norm of a kernel equals the square root of its
squared energy integral. -/
private theorem kernelLpNorm_eq_sqrt_integral_sq
    {φ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    ‖hφ.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ =
      Real.sqrt
        (∫ z : Ω × Ω, (φ z.1 z.2) ^ (2 : ℕ)
          ∂(MeasureTheory.Measure.prod μ μ)) := by
  let f : MeasureTheory.Lp ℝ 2 (MeasureTheory.Measure.prod μ μ) :=
    hφ.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)
  -- Rewrite the `L²` norm through the real inner product and then replace the quotient
  -- representative by the original kernel function.
  calc
    ‖f‖ = Real.sqrt (inner ℝ f f) := norm_eq_sqrt_real_inner f
    _ = Real.sqrt (∫ z : Ω × Ω, inner ℝ (f z) (f z) ∂(MeasureTheory.Measure.prod μ μ)) := by
      rw [MeasureTheory.L2.inner_def]
    _ = Real.sqrt (∫ z : Ω × Ω, f z * f z ∂(MeasureTheory.Measure.prod μ μ)) := by
      simp [pow_two]
    _ = Real.sqrt
          (∫ z : Ω × Ω, (φ z.1 z.2) ^ (2 : ℕ)
            ∂(MeasureTheory.Measure.prod μ μ)) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.MemLp.coeFn_toLp hφ] with z hz
      simp [f, hz, pow_two]

/-- Helper for Example 2.4: a sigma-finite restriction of `μ.restrict μ.sigmaFiniteSetᶜ`
must vanish because that complement only carries zero-or-infinite mass. -/
private theorem restrictComplSigmaFiniteSetRestrict_eq_zero
    (t : Set Ω)
    [MeasureTheory.SigmaFinite ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t)] :
    (μ.restrict μ.sigmaFiniteSetᶜ).restrict t = 0 := by
  ext s hs
  have h_univ :
      ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) Set.univ = 0 := by
    -- The sigma-finite spanning pieces are finite, so the zero-or-top dichotomy forces each one
    -- to have zero mass.
    rw [← MeasureTheory.iUnion_spanningSets ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t)]
    refine MeasureTheory.measure_iUnion_null fun n ↦ ?_
    have hfinite :
        ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t)
            (MeasureTheory.spanningSets ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) n) < ∞ := by
      simpa using
        MeasureTheory.measure_spanningSets_lt_top
          (((μ.restrict μ.sigmaFiniteSetᶜ).restrict t)) n
    have hmeas :
        MeasurableSet (MeasureTheory.spanningSets ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) n) :=
      MeasureTheory.measurableSet_spanningSets (((μ.restrict μ.sigmaFiniteSetᶜ).restrict t)) n
    rcases
        MeasureTheory.restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ := μ)
          (MeasureTheory.spanningSets ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) n ∩ t) with
      hzero | htop
    · simpa [MeasureTheory.Measure.restrict_apply hmeas, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_comm] using hzero
    · have :
          ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t)
              (MeasureTheory.spanningSets ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) n) = ∞ := by
        simpa [MeasureTheory.Measure.restrict_apply hmeas, Set.inter_assoc, Set.inter_left_comm,
          Set.inter_comm] using htop
      exact (ne_of_lt hfinite this).elim
  -- Once the restricted measure vanishes on `univ`, it vanishes on every measurable set.
  have hle :
      ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) s ≤
        ((μ.restrict μ.sigmaFiniteSetᶜ).restrict t) Set.univ :=
    MeasureTheory.measure_mono (Set.subset_univ s)
  exact le_antisymm (by simpa [h_univ] using hle) (by simp)

/-- Helper for Example 2.4: every `L²(μ)` function is almost everywhere zero off the sigma-finite
core of an s-finite measure. -/
private theorem memLp_aeEq_zero_compl_sigmaFiniteSet
    {f : Ω → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) :
    f =ᵐ[μ.restrict μ.sigmaFiniteSetᶜ] 0 := by
  let ν : MeasureTheory.Measure Ω := μ.restrict μ.sigmaFiniteSetᶜ
  have hf_restrict : MeasureTheory.MemLp f 2 ν := by
    -- Restrict the `L²` function to the off-core measure before applying the
    -- `AEFinStronglyMeasurable` support package.
    simpa [ν] using hf.restrict μ.sigmaFiniteSetᶜ
  have hf_ae_fin : MeasureTheory.AEFinStronglyMeasurable f ν := by
    exact hf_restrict.aefinStronglyMeasurable (by norm_num) (by norm_num)
  let t : Set Ω := hf_ae_fin.sigmaFiniteSet
  have hνt_zero : ν.restrict t = 0 := by
    simpa [ν, t] using
      (restrictComplSigmaFiniteSetRestrict_eq_zero (μ := μ) t)
  have ht : ∀ᵐ x ∂ν.restrict t, f x = 0 := by
    -- On the sigma-finite support chosen by `AEFinStronglyMeasurable`, the off-core measure
    -- itself is zero.
    simp [hνt_zero]
  have htc : ∀ᵐ x ∂ν.restrict tᶜ, f x = 0 := hf_ae_fin.ae_eq_zero_compl
  -- Glue the zero statements on `t` and `tᶜ` back into the whole off-core restriction.
  exact MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl t ht htc

/-- Helper for Example 2.4: if almost every second-variable section vanishes off the sigma-finite
core, then the whole kernel vanishes on the right strip `Ω × μ.sigmaFiniteSetᶜ`. -/
private theorem kernel_aeEq_zero_right_sigmaFiniteStrip
    {φ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hsection :
      ∀ᵐ x ∂μ, (fun y ↦ φ x y) =ᵐ[μ.restrict μ.sigmaFiniteSetᶜ] 0) :
    (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[MeasureTheory.Measure.prod μ (μ.restrict μ.sigmaFiniteSetᶜ)] 0 := by
  let νc : MeasureTheory.Measure Ω := μ.restrict μ.sigmaFiniteSetᶜ
  let g : Ω × Ω → ℝ := hφ.1.mk (fun z : Ω × Ω ↦ φ z.1 z.2)
  have hφ_eq_g' :
      (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[MeasureTheory.Measure.prod μ νc] g := by
    -- Restrict the ambient a.e. measurable representative to the right strip.
    have hrestrict :
        (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
          (Set.univ ×ˢ μ.sigmaFiniteSetᶜ)] g := by
      simpa [g] using hφ.1.ae_eq_mk.restrict
    have hmeasure :
        MeasureTheory.Measure.prod μ (μ.restrict μ.sigmaFiniteSetᶜ) =
          (MeasureTheory.Measure.prod μ μ).restrict (Set.univ ×ˢ μ.sigmaFiniteSetᶜ) := by
      simpa [MeasureTheory.Measure.restrict_univ] using
        (MeasureTheory.Measure.prod_restrict
          (μ := μ) (ν := μ) Set.univ μ.sigmaFiniteSetᶜ)
    rw [hmeasure]
    exact hrestrict
  have hsection_eq_g :
      ∀ᵐ x ∂μ, (fun y ↦ φ x y) =ᵐ[νc] fun y ↦ g (x, y) := by
    -- The stripwise representative is obtained by currying the restricted product a.e. equality.
    change ∀ᵐ x ∂μ,
      Function.curry (fun z : Ω × Ω ↦ φ z.1 z.2) x =ᵐ[νc] Function.curry g x
    simpa [νc] using
      (MeasureTheory.Measure.ae_ae_eq_curry_of_prod
        (μ := μ) (ν := μ.restrict μ.sigmaFiniteSetᶜ) hφ_eq_g')
  have hsection_g_zero :
      ∀ᵐ x ∂μ, (fun y ↦ g (x, y)) =ᵐ[νc] 0 := by
    -- Replace the raw section by the measurable representative before using the off-core vanishing.
    filter_upwards [hsection, hsection_eq_g] with x hx_zero hx_eq
    exact hx_eq.symm.trans hx_zero
  have hg_zero_meas : MeasurableSet {z : Ω × Ω | g z = 0} := by
    -- The zero set is measurable because `g` is the measurable representative.
    change MeasurableSet (g ⁻¹' ({0} : Set ℝ))
    exact hφ.1.measurable_mk (measurableSet_singleton (0 : ℝ))
  have hsection_g_zero' :
      ∀ᵐ x ∂μ, ∀ᵐ y ∂νc, g (x, y) = 0 := by
    filter_upwards [hsection_g_zero] with x hx
    simpa [Filter.EventuallyEq] using hx
  have hg_zero :
      ∀ᵐ z ∂MeasureTheory.Measure.prod μ νc, g z = 0 := by
    -- Fubini upgrades the sectionwise zero statement to the whole right strip.
    exact
      (MeasureTheory.Measure.ae_prod_iff_ae_ae
        (μ := μ) (ν := νc) hg_zero_meas).2 hsection_g_zero'
  -- Transfer the right-strip vanishing from the measurable representative back to the raw kernel.
  exact hφ_eq_g'.trans (by simpa [Filter.EventuallyEq] using hg_zero)

/-- Helper for Example 2.4: if almost every first-variable section vanishes off the sigma-finite
core, then the whole kernel vanishes on the left strip `μ.sigmaFiniteSetᶜ × Ω`. -/
private theorem kernel_aeEq_zero_left_sigmaFiniteStrip
    {φ : Ω → Ω → ℝ}
    (hφ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (hsection :
      ∀ᵐ y ∂μ, (fun x ↦ φ x y) =ᵐ[μ.restrict μ.sigmaFiniteSetᶜ] 0) :
    (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(μ.restrict μ.sigmaFiniteSetᶜ).prod μ] 0 := by
  let ψ : Ω → Ω → ℝ := fun x y ↦ φ y x
  have hψ :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ ψ z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ) := by
    -- Swapping the two coordinates turns first-variable sections into the right-strip situation.
    convert
      (hφ.comp_measurePreserving
        (MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := μ)) :
          MeasureTheory.MemLp (((fun z : Ω × Ω ↦ φ z.1 z.2) ∘ Prod.swap)) 2
            (MeasureTheory.Measure.prod μ μ)) using 1
    funext z
    rfl
  have hψ_right :
      (fun z : Ω × Ω ↦ ψ z.1 z.2) =ᵐ[MeasureTheory.Measure.prod μ (μ.restrict μ.sigmaFiniteSetᶜ)]
        0 := by
    -- After swapping the kernel, the first-variable off-core vanishing becomes a right-strip
    -- statement.
    simpa [ψ] using
      kernel_aeEq_zero_right_sigmaFiniteStrip (μ := μ) (φ := ψ) hψ hsection
  -- Pull the swapped right-strip statement back along `Prod.swap` to recover the left strip for
  -- the original kernel.
  change ((fun z : Ω × Ω ↦ φ z.2 z.1) ∘ Prod.swap) =ᵐ[(μ.restrict μ.sigmaFiniteSetᶜ).prod μ] 0
  exact
    hψ_right.comp_tendsto
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := μ.restrict μ.sigmaFiniteSetᶜ) (ν := μ)).quasiMeasurePreserving.tendsto_ae

/-- Helper for Example 2.4: once the Fredholm kernel vanishes on both sigma-finite complement
strips, it vanishes off the sigma-finite box `μ.sigmaFiniteSet ×ˢ μ.sigmaFiniteSet`. -/
private theorem kernel_aeEq_zero_compl_sigmaFiniteBox
    {φ : Ω → Ω → ℝ}
    (h_right :
      (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[MeasureTheory.Measure.prod μ
        (μ.restrict μ.sigmaFiniteSetᶜ)] 0)
    (h_left :
      (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(μ.restrict μ.sigmaFiniteSetᶜ).prod μ] 0) :
    (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
      ((μ.sigmaFiniteSet ×ˢ μ.sigmaFiniteSet)ᶜ)] 0 := by
  let S : Set Ω := μ.sigmaFiniteSet
  have h_right_restrict :
      (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
        (Set.univ ×ˢ Sᶜ)] 0 := by
    -- The right strip is exactly the ambient product restricted to `univ ×ˢ Sᶜ`.
    rw [← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]
    exact h_right
  have h_left_restrict :
      (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
        (Sᶜ ×ˢ Set.univ)] 0 := by
    -- The left strip is exactly the ambient product restricted to `Sᶜ ×ˢ univ`.
    rw [← MeasureTheory.Measure.restrict_prod_eq_prod_univ]
    exact h_left
  have h_union :
      (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
        ((Sᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Sᶜ))] 0 := by
    -- The complement of the sigma-finite box is the union of the left and right strips.
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_union_iff]
    exact ⟨h_left_restrict, h_right_restrict⟩
  simpa [S, Set.compl_prod_eq_union] using h_union

/-- Helper for Example 2.4: an `L²(μ × μ)` approximation by finite rectangle kernels upgrades to
an operator-norm convergent sequence of compact canonical kernel operators. -/
private theorem exists_compactApprox_tendsto_of_lpApprox
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (happrox :
      ∀ ε > 0, ∃ φ : Ω → Ω → ℝ, ∃ hφ : IsFiniteRectKernel (μ := μ) φ,
        ‖h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
            (hφ.memLp (μ := μ)).toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ < ε) :
    ∃ T : ℕ → (MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ),
      (∀ n, IsCompactOperator (T n)) ∧
        Filter.Tendsto
          (fun n ↦ ‖T n - canonicalKernelOperator μ k h_kernel‖) Filter.atTop
            (nhds 0) := by
  have honeDivPos : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := by
    intro n
    positivity
  choose φ hφ hclose using fun n : ℕ ↦ happrox ((1 : ℝ) / (n + 1)) (honeDivPos n)
  let T : ℕ → (MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :=
    fun n ↦ canonicalKernelOperator μ (φ n) ((hφ n).memLp (μ := μ))
  refine ⟨T, ?_, ?_⟩
  · intro n
    -- Each approximant comes from a finite rectangle kernel, hence it is compact.
    simpa [T] using (hφ n).isCompactOperator (μ := μ)
  · have h_upper :
        ∀ n, ‖T n - canonicalKernelOperator μ k h_kernel‖ ≤ (1 : ℝ) / (n + 1) := by
        intro n
        let hφMemLp :
            MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ n z.1 z.2) 2
              (MeasureTheory.Measure.prod μ μ) :=
          (hφ n).memLp (μ := μ)
        have hsub :
            MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ n z.1 z.2 - k z.1 z.2) 2
              (MeasureTheory.Measure.prod μ μ) :=
          hφMemLp.sub h_kernel
        have h_operator_bound :
            ‖T n - canonicalKernelOperator μ k h_kernel‖ ≤
              ‖hφMemLp.toLp (fun z : Ω × Ω ↦ φ n z.1 z.2) -
                  h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2)‖ := by
          calc
            ‖T n - canonicalKernelOperator μ k h_kernel‖ ≤
                Real.sqrt
                  (∫ z : Ω × Ω, (φ n z.1 z.2 - k z.1 z.2) ^ (2 : ℕ)
                    ∂(MeasureTheory.Measure.prod μ μ)) := by
                  simpa [T] using
                    (canonicalKernelOperator_sub_norm_le
                      (μ := μ) (φ := φ n) (ψ := k) hφMemLp h_kernel hsub)
            _ = ‖hsub.toLp (fun z : Ω × Ω ↦ φ n z.1 z.2 - k z.1 z.2)‖ := by
                  symm
                  exact
                    kernelLpNorm_eq_sqrt_integral_sq
                      (μ := μ) (φ := fun x y ↦ φ n x y - k x y) hsub
            _ = ‖hφMemLp.toLp (fun z : Ω × Ω ↦ φ n z.1 z.2) -
                    h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2)‖ := by
                  have htoLp_sub :
                      hsub.toLp (fun z : Ω × Ω ↦ φ n z.1 z.2 - k z.1 z.2) =
                        hφMemLp.toLp (fun z : Ω × Ω ↦ φ n z.1 z.2) -
                          h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) := by
                    exact MeasureTheory.MemLp.toLp_sub hφMemLp h_kernel
                  rw [htoLp_sub]
        have hclose_rev :
            ‖hφMemLp.toLp (fun z : Ω × Ω ↦ φ n z.1 z.2) -
                h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2)‖ <
              (1 : ℝ) / (n + 1) := by
          simpa [hφMemLp, norm_sub_rev] using hclose n
        exact le_of_lt (lt_of_le_of_lt h_operator_bound hclose_rev)
    have honeDiv_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
      have hInv :
          Filter.Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) : ℝ)⁻¹) Filter.atTop (nhds 0) := by
        convert
          ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
            (Filter.tendsto_add_atTop_nat 1)) using 1
        ext n
        simp [Function.comp]
      simpa [one_div] using hInv
    -- The operator-norm error is squeezed between `0` and the chosen `1 / (n + 1)` kernel error.
    exact squeeze_zero (fun n ↦ norm_nonneg _) h_upper honeDiv_tendsto

/-- Helper for Example 2.4: the compactness proof can be expressed through a norm-convergent
approximating sequence built from finite rectangle kernels. -/
private theorem exists_rectKernelApprox_tendsto
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    ∃ T : ℕ → (MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ),
      (∀ n, IsCompactOperator (T n)) ∧
        Filter.Tendsto
          (fun n ↦ ‖T n - canonicalKernelOperator μ k h_kernel‖) Filter.atTop
            (nhds 0) := by
  -- Route correction: the repeated section-field packaging route was removed. The live frontier is
  -- now genuinely product-space: approximate the kernel in `L²(μ × μ)` by finite rectangle
  -- kernels using `measurableRectangleAlgebraMeasureDense`, convert those kernels to compact
  -- operators with `finiteRectKernelOperator_isCompact`, and then use
  -- `canonicalKernelOperator_sub_norm_le` to transfer the convergence to operator norm.
  let S : Set Ω := μ.sigmaFiniteSet
  have h_section_off_core :
      ∀ᵐ x ∂μ, (fun y ↦ k x y) =ᵐ[μ.restrict Sᶜ] 0 := by
    -- The second-variable sections already lie in `L²(μ)` almost everywhere, so the new
    -- sigma-finite-core helper kills them on `Sᶜ`.
    filter_upwards [kernelSection_memLp_ae (μ := μ) (k := k) h_kernel] with x hx
    simpa [S] using memLp_aeEq_zero_compl_sigmaFiniteSet (μ := μ) hx
  have h_kernel_swap :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.2 z.1) 2
        (MeasureTheory.Measure.prod μ μ) := by
    -- Swapping the two coordinates preserves the product measure.
    convert
      (h_kernel.comp_measurePreserving
        (MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := μ)) :
          MeasureTheory.MemLp (((fun z : Ω × Ω ↦ k z.1 z.2) ∘ Prod.swap)) 2
            (MeasureTheory.Measure.prod μ μ)) using 1
    rfl
  have h_swapped_section_off_core :
      ∀ᵐ y ∂μ, (fun x ↦ k x y) =ᵐ[μ.restrict Sᶜ] 0 := by
    -- The same off-core vanishing holds in the first variable after swapping the kernel.
    filter_upwards
        [kernelSection_memLp_ae (μ := μ) (k := fun x y ↦ k y x) h_kernel_swap] with y hy
    simpa [S] using memLp_aeEq_zero_compl_sigmaFiniteSet (μ := μ) hy
  have h_right_strip_off_core :
      (fun z : Ω × Ω ↦ k z.1 z.2) =ᵐ[MeasureTheory.Measure.prod μ (μ.restrict Sᶜ)] 0 := by
    -- The original kernel vanishes on the full right strip by the new stripwise support lemma.
    simpa [S] using
      kernel_aeEq_zero_right_sigmaFiniteStrip (μ := μ) (φ := k) h_kernel h_section_off_core
  have h_left_strip_off_core :
      (fun z : Ω × Ω ↦ k z.1 z.2) =ᵐ[(μ.restrict Sᶜ).prod μ] 0 := by
    -- Swapping the kernel turns the first-variable off-core statement into the proved
    -- right-strip lemma, which we then transport back.
    simpa [S] using
      kernel_aeEq_zero_left_sigmaFiniteStrip
        (μ := μ) (φ := k) h_kernel h_swapped_section_off_core
  have h_box_off_core :
      (fun z : Ω × Ω ↦ k z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
        ((S ×ˢ S)ᶜ)] 0 := by
    -- Combining the two stripwise vanishing statements confines the kernel to the sigma-finite
    -- box `S ×ˢ S`.
    simpa [S] using
      kernel_aeEq_zero_compl_sigmaFiniteBox
        (μ := μ) (φ := k) h_right_strip_off_core h_left_strip_off_core
  have happrox :
      ∀ ε > 0, ∃ φ : Ω → Ω → ℝ, ∃ hφ : IsFiniteRectKernel (μ := μ) φ,
        ‖h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
            (hφ.memLp (μ := μ)).toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ < ε := by
    let νS : MeasureTheory.Measure (Ω × Ω) := (μ.restrict S).prod (μ.restrict S)
    let coreBox : Set (Ω × Ω) := S ×ˢ S
    let Dcore : Set (MeasureTheory.Lp ℝ 2 νS) :=
      {f | ∃ φ : Ω → Ω → ℝ, ∃ hφ : IsFiniteRectKernel (μ := μ) φ,
          ∃ hφνS : MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2 νS,
          ∃ hφ_off :
              (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
                coreBoxᶜ] 0,
            f = hφνS.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)}
    have hνS_eq :
        νS = (MeasureTheory.Measure.prod μ μ).restrict coreBox := by
      -- The restricted core product measure is the ambient product restricted to the sigma-finite
      -- box.
      simpa [νS, coreBox] using
        (MeasureTheory.Measure.prod_restrict (μ := μ) (ν := μ) S S)
    have hfiniteRect_mem_Dcore {φ : Ω → Ω → ℝ}
        (hφ : IsFiniteRectKernel (μ := μ) φ)
        (hφ_off :
          (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
            coreBoxᶜ] 0) :
        ∃ hφνS : MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2 νS,
          hφνS.toLp (fun z : Ω × Ω ↦ φ z.1 z.2) ∈ Dcore := by
      -- Restrict any core-supported ambient finite rectangle kernel to the sigma-finite box and
      -- package the resulting `L²` class as an element of the local witness set.
      have hφνS :
          MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2 νS := by
        rw [hνS_eq]
        exact (hφ.memLp (μ := μ)).restrict coreBox
      exact ⟨hφνS, ⟨φ, hφ, hφνS, hφ_off, rfl⟩⟩
    have hDcore_add :
        ∀ ⦃f g : MeasureTheory.Lp ℝ 2 νS⦄, f ∈ Dcore → g ∈ Dcore → f + g ∈ Dcore := by
      intro f g hf hg
      rcases hf with ⟨φ, hφ, hφνS, hφ_off, rfl⟩
      rcases hg with ⟨ψ, hψ, hψνS, hψ_off, rfl⟩
      have hsum :
          IsFiniteRectKernel (μ := μ) (fun x y ↦ φ x y + ψ x y) := by
        -- Ambient finite rectangle kernels are stable under addition.
        exact IsFiniteRectKernel.add (μ := μ) hφ hψ
      have hsumνS :
          MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2 + ψ z.1 z.2) 2 νS :=
        hφνS.add hψνS
      have hsum_off :
          (fun z : Ω × Ω ↦ φ z.1 z.2 + ψ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
            coreBoxᶜ] 0 := by
        -- Core support is preserved when the ambient finite rectangle kernels are added.
        filter_upwards [hφ_off, hψ_off] with z hzφ hzψ
        simp [hzφ, hzψ]
      exact ⟨fun x y ↦ φ x y + ψ x y, hsum, hsumνS, hsum_off, by
        -- The quotient addition matches the pointwise addition of the ambient kernels.
        rw [← MeasureTheory.MemLp.toLp_add (hf := hφνS) (hg := hψνS)]
        exact MeasureTheory.MemLp.toLp_congr hsumνS (hφνS.add hψνS) (by
          filter_upwards with z
          rfl)⟩
    have hclosure_add :
        ∀ ⦃f g : MeasureTheory.Lp ℝ 2 νS⦄,
          f ∈ closure Dcore → g ∈ closure Dcore → f + g ∈ closure Dcore := by
      intro f g hf hg
      -- This is the closure-stability package needed later for the `Lp.induction` sum step.
      exact map_mem_closure₂ continuous_add hf hg (fun _ hx _ hy ↦ hDcore_add hx hy)
    have hboxIndicator_mem_closure_Dcore
        {U V : Set Ω} {a : Set (Ω × Ω)}
        (hU : MeasurableSet U) (hV : MeasurableSet V)
        (hUS : U ⊆ S) (hVS : V ⊆ S)
        (hμU : μ U < ∞) (hμV : μ V < ∞)
        (ha :
          a ∈ MeasureTheory.generateSetAlgebra
            (Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
              {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :
        ∃ hφνS :
            MeasureTheory.MemLp
              (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z)) 2 νS,
          hφνS.toLp
              (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z)) ∈ Dcore := by
      -- Each box-local rectangle-algebra indicator is already an ambient finite rectangle kernel,
      -- and the inclusion `U ×ˢ V ⊆ S ×ˢ S` makes it vanish off the sigma-finite core box.
      let φ : Ω → Ω → ℝ := fun x y ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) (x, y))
      have hφ :
          IsFiniteRectKernel (μ := μ) φ := by
        simpa [φ] using
          (finiteBoxRectAlgebraIndicator_isFiniteRectKernel
            (μ := μ) U V a hU hV hμU hμV ha)
      have hφ_off :
          (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
            coreBoxᶜ] 0 := by
        -- Outside `S ×ˢ S`, the smaller box-supported indicator is forced to vanish.
        filter_upwards [MeasureTheory.ae_restrict_mem
          (μ := MeasureTheory.Measure.prod μ μ) (s := coreBoxᶜ) (by
          simpa [coreBox] using
            (MeasureTheory.measurableSet_sigmaFiniteSet.prod
              MeasureTheory.measurableSet_sigmaFiniteSet).compl)] with z hz
        have hz_not_mem : z ∉ U ×ˢ V := by
          intro hzUV
          exact hz <| Set.mem_of_subset_of_mem (Set.prod_mono hUS hVS) hzUV
        simp [φ, hz_not_mem]
      rcases hfiniteRect_mem_Dcore hφ hφ_off with ⟨hφνS, hφD⟩
      exact ⟨hφνS, hφD⟩
    have hkνS :
        MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2 νS := by
      -- The ambient kernel restricts to the sigma-finite core product measure.
      rw [hνS_eq]
      exact h_kernel.restrict coreBox
    have hambient_of_coreApprox
        {ε : ℝ} {φ : Ω → Ω → ℝ}
        (hφ : IsFiniteRectKernel (μ := μ) φ)
        (hφνS : MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2 νS)
        (hφ_off :
          (fun z : Ω × Ω ↦ φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
            coreBoxᶜ] 0)
        (hclose :
          ‖hkνS.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
              hφνS.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ < ε) :
        ‖h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
            (hφ.memLp (μ := μ)).toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ < ε := by
      let ambient : MeasureTheory.Measure (Ω × Ω) := MeasureTheory.Measure.prod μ μ
      let hφμ :
          MeasureTheory.MemLp (fun z : Ω × Ω ↦ φ z.1 z.2) 2 ambient :=
        hφ.memLp (μ := μ)
      let hsubAmbient :
          MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) 2 ambient :=
        h_kernel.sub hφμ
      let hsubCore :
          MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) 2 νS :=
        hkνS.sub hφνS
      have hcoreBox_meas : MeasurableSet coreBox := by
        exact MeasureTheory.measurableSet_sigmaFiniteSet.prod
          MeasureTheory.measurableSet_sigmaFiniteSet
      have hsub_off :
          (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) =ᵐ[ambient.restrict coreBoxᶜ] 0 := by
        -- Both kernels vanish outside `S ×ˢ S`, so their difference does as well.
        filter_upwards [h_box_off_core, hφ_off] with z hzk hzφ
        simp [hzk, hzφ]
      have hsub_indicator :
          (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) =ᵐ[ambient]
            coreBox.indicator (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) := by
        -- Replace the ambient difference by its core-box indicator before comparing `Lp` norms.
        refine MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl coreBox ?_ ?_
        · exact (indicator_ae_eq_restrict
            (f := fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) hcoreBox_meas).symm
        · exact hsub_off.trans (indicator_ae_eq_restrict_compl
            (f := fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) hcoreBox_meas).symm
      have hsubAmbient_eq :
          MeasureTheory.MemLp.toLp
              ((fun z : Ω × Ω ↦ k z.1 z.2) - fun z ↦ φ z.1 z.2)
              (h_kernel.sub hφμ) =
            hsubAmbient.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) := by
        exact MeasureTheory.MemLp.toLp_congr (h_kernel.sub hφμ) hsubAmbient (by
          filter_upwards with z
          rfl)
      have hsubCore_eq :
          MeasureTheory.MemLp.toLp
              ((fun z : Ω × Ω ↦ k z.1 z.2) - fun z ↦ φ z.1 z.2)
              (hkνS.sub hφνS) =
            hsubCore.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) := by
        exact MeasureTheory.MemLp.toLp_congr (hkνS.sub hφνS) hsubCore (by
          filter_upwards with z
          rfl)
      have hambient_norm_eq :
          ‖h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
              hφμ.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ =
            ‖hsubCore.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2)‖ := by
        -- The ambient `L²` norm is the same as the restricted-core norm because the difference is
        -- supported inside `S ×ˢ S`.
        calc
          ‖h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
              hφμ.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ =
                ‖hsubAmbient.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2)‖ := by
                  rw [← MeasureTheory.MemLp.toLp_sub h_kernel hφμ, hsubAmbient_eq]
          _ = ENNReal.toReal
                (MeasureTheory.eLpNorm (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) 2 ambient) := by
                  simpa using
                    (MeasureTheory.Lp.norm_toLp
                      (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) hsubAmbient)
          _ = ENNReal.toReal
                (MeasureTheory.eLpNorm
                  (coreBox.indicator (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2)) 2 ambient) := by
                rw [MeasureTheory.eLpNorm_congr_ae hsub_indicator.symm]
          _ = ENNReal.toReal
                (MeasureTheory.eLpNorm (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) 2
                  (ambient.restrict coreBox)) := by
                rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hcoreBox_meas]
          _ = ENNReal.toReal
                (MeasureTheory.eLpNorm (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) 2 νS) := by
                rw [hνS_eq]
          _ = ‖hsubCore.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2)‖ := by
                simpa using
                  (MeasureTheory.Lp.norm_toLp
                    (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2) hsubCore).symm
      have hcore_norm_eq :
          ‖hkνS.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
              hφνS.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ =
            ‖hsubCore.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2)‖ := by
        rw [← MeasureTheory.MemLp.toLp_sub hkνS hφνS, hsubCore_eq]
      calc
        ‖h_kernel.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
            hφμ.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ =
          ‖hsubCore.toLp (fun z : Ω × Ω ↦ k z.1 z.2 - φ z.1 z.2)‖ := hambient_norm_eq
        _ = ‖hkνS.toLp (fun z : Ω × Ω ↦ k z.1 z.2) -
              hφνS.toLp (fun z : Ω × Ω ↦ φ z.1 z.2)‖ := hcore_norm_eq.symm
        _ < ε := hclose
    have hkνS_mem_closure :
        hkνS.toLp (fun z : Ω × Ω ↦ k z.1 z.2) ∈ closure Dcore := by
      let U : ℕ → Set Ω := fun n ↦ MeasureTheory.spanningSets (μ.restrict S) n ∩ S
      let box : ℕ → Set (Ω × Ω) := fun n ↦ U n ×ˢ U n
      have hU_meas : ∀ n, MeasurableSet (U n) := by
        intro n
        exact (MeasureTheory.measurableSet_spanningSets (μ.restrict S) n).inter
          MeasureTheory.measurableSet_sigmaFiniteSet
      have hU_subset : ∀ n, U n ⊆ S := by
        intro n x hx
        exact hx.2
      have hU_mono : Monotone U := by
        intro m n hmn x hx
        exact ⟨MeasureTheory.spanningSets_mono (μ := μ.restrict S) hmn hx.1, hx.2⟩
      have hU_finite : ∀ n, μ (U n) < ∞ := by
        intro n
        have hrestrict_lt :
            (μ.restrict S) (U n) < ∞ := by
          exact lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
            (MeasureTheory.measure_spanningSets_lt_top (μ.restrict S) n)
        have hrestrict_eq :
            (μ.restrict S) (U n) = μ (U n) := by
          rw [MeasureTheory.Measure.restrict_apply (hU_meas n), Set.inter_eq_left.2 (hU_subset n)]
        simpa [hrestrict_eq] using hrestrict_lt
      have hU_iUnion : ⋃ n, U n = S := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
          exact hn.2
        · intro hxS
          have hxspan : x ∈ ⋃ n, MeasureTheory.spanningSets (μ.restrict S) n := by
            rw [MeasureTheory.iUnion_spanningSets (μ.restrict S)]
            simp
          rcases Set.mem_iUnion.1 hxspan with ⟨n, hn⟩
          exact Set.mem_iUnion.2 ⟨n, ⟨hn, hxS⟩⟩
      have hbox_meas : ∀ n, MeasurableSet (box n) := by
        intro n
        exact (hU_meas n).prod (hU_meas n)
      have hbox_mono : Monotone box := by
        intro m n hmn
        exact Set.prod_mono (hU_mono hmn) (hU_mono hmn)
      have hbox_subset_core : ∀ n, box n ⊆ coreBox := by
        intro n
        exact Set.prod_mono (hU_subset n) (hU_subset n)
      have hbox_iUnion : ⋃ n, box n = coreBox := by
        ext z
        constructor
        · intro hz
          rcases Set.mem_iUnion.1 hz with ⟨n, hn⟩
          exact ⟨hU_subset n hn.1, hU_subset n hn.2⟩
        · intro hz
          have hz₁ : z.1 ∈ ⋃ n, U n := by
            rw [hU_iUnion]
            exact hz.1
          have hz₂ : z.2 ∈ ⋃ n, U n := by
            rw [hU_iUnion]
            exact hz.2
          rcases Set.mem_iUnion.1 hz₁ with ⟨n₁, hn₁⟩
          rcases Set.mem_iUnion.1 hz₂ with ⟨n₂, hn₂⟩
          refine Set.mem_iUnion.2 ⟨max n₁ n₂, ?_⟩
          exact ⟨hU_mono (le_max_left _ _) hn₁, hU_mono (le_max_right _ _) hn₂⟩
      have hDcore_smul :
          ∀ (c : ℝ) ⦃f : MeasureTheory.Lp ℝ 2 νS⦄, f ∈ Dcore → c • f ∈ Dcore := by
        intro c f hf
        rcases hf with ⟨φ, hφ, hφνS, hφ_off, rfl⟩
        have hsmul :
            IsFiniteRectKernel (μ := μ) (fun x y ↦ c * φ x y) := by
          exact IsFiniteRectKernel.smul (μ := μ) c hφ
        have hsmulνS :
            MeasureTheory.MemLp (fun z : Ω × Ω ↦ c * φ z.1 z.2) 2 νS := by
          convert
            (hφνS.const_smul c :
              MeasureTheory.MemLp (c • fun z : Ω × Ω ↦ φ z.1 z.2) 2 νS) using 1
          funext z
          simp [Pi.smul_apply, smul_eq_mul]
        have hsmul_off :
            (fun z : Ω × Ω ↦ c * φ z.1 z.2) =ᵐ[(MeasureTheory.Measure.prod μ μ).restrict
              coreBoxᶜ] 0 := by
          filter_upwards [hφ_off] with z hz
          simp [hz, smul_eq_mul]
        refine ⟨fun x y ↦ c * φ x y, hsmul, hsmulνS, hsmul_off, ?_⟩
        calc
          MeasureTheory.MemLp.toLp (fun z : Ω × Ω ↦ c * φ z.1 z.2) hsmulνS =
              MeasureTheory.MemLp.toLp (c • fun z : Ω × Ω ↦ φ z.1 z.2)
                (hφνS.const_smul c) := by
                  exact MeasureTheory.MemLp.toLp_congr hsmulνS (hφνS.const_smul c) (by
                    filter_upwards with z
                    simp [Pi.smul_apply, smul_eq_mul])
          _ = c • MeasureTheory.MemLp.toLp (fun z : Ω × Ω ↦ φ z.1 z.2) hφνS := by
                exact MeasureTheory.MemLp.toLp_const_smul c hφνS
      have hclosure_smul :
          ∀ (c : ℝ) ⦃f : MeasureTheory.Lp ℝ 2 νS⦄,
            f ∈ closure Dcore → c • f ∈ closure Dcore := by
        intro c f hf
        exact map_mem_closure (continuous_const_smul c) hf (fun _ hx ↦ hDcore_smul c hx)
      have hboxIndicatorConst_mem_closure_Dcore
          {U V : Set Ω} {a : Set (Ω × Ω)} (c : ℝ)
          (hU : MeasurableSet U) (hV : MeasurableSet V)
          (hUS : U ⊆ S) (hVS : V ⊆ S)
          (hμU : μ U < ∞) (hμV : μ V < ∞)
          (ha :
            a ∈ MeasureTheory.generateSetAlgebra
              (Set.image2 (fun s t : Set Ω ↦ (s ∩ U) ×ˢ (t ∩ V))
                {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :
          ∃ hφνS :
              MeasureTheory.MemLp
                (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ c) z)) 2 νS,
            hφνS.toLp
                (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ c) z)) ∈ Dcore := by
        rcases hboxIndicator_mem_closure_Dcore hU hV hUS hVS hμU hμV ha with ⟨h1, h1_D⟩
        have h1c :
            MeasureTheory.MemLp
              (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ c) z)) 2 νS := by
          convert
            (h1.const_smul c :
              MeasureTheory.MemLp
                (c • fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z)) 2 νS) using 1
          funext z
          by_cases hz : z ∈ a ∩ (U ×ˢ V) <;> simp [hz, Pi.smul_apply, smul_eq_mul]
        refine ⟨h1c, ?_⟩
        have hscaled :
            c • h1.toLp
              (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z)) ∈ Dcore :=
          hDcore_smul c h1_D
        have h1c_eq :
            h1c.toLp (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ c) z)) =
              c • h1.toLp
                (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z)) := by
          calc
            h1c.toLp (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ c) z)) =
                MeasureTheory.MemLp.toLp
                  (c • fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z))
                  (h1.const_smul c) := by
                    exact MeasureTheory.MemLp.toLp_congr h1c (h1.const_smul c) (by
                      filter_upwards with z
                      by_cases hz : z ∈ a ∩ (U ×ˢ V) <;> simp [hz, Pi.smul_apply, smul_eq_mul])
            _ = c • h1.toLp
                  (fun z : Ω × Ω ↦ ((a ∩ (U ×ˢ V)).indicator (fun _ ↦ (1 : ℝ)) z)) := by
                    exact MeasureTheory.MemLp.toLp_const_smul c h1
        exact h1c_eq.symm ▸ hscaled
      let νn : ℕ → MeasureTheory.Measure (Ω × Ω) :=
        fun n ↦ (μ.restrict (U n)).prod (μ.restrict (U n))
      have hνn_eq : ∀ n, νn n = νS.restrict (box n) := by
        intro n
        -- This is the only transport point between the finite-box product measure and `νS`.
        have hrestrict :
            μ.restrict (U n) = (μ.restrict S).restrict (U n) := by
          simpa [Set.inter_eq_left.2 (hU_subset n)] using
            (MeasureTheory.Measure.restrict_restrict_of_subset (μ := μ) (hU_subset n)).symm
        simpa [νn, νS, box, hrestrict] using
          (MeasureTheory.Measure.prod_restrict
            (μ := μ.restrict S) (ν := μ.restrict S) (U n) (U n))
      have hspanningBoxIndicator_mem_closure_Dcore
          (n : ℕ) {a : Set (Ω × Ω)} (ha : MeasurableSet a) (hfinite : νn n a ≠ ∞) :
          MeasureTheory.indicatorConstLp 2 (ha.inter (hbox_meas n))
              (by
                have hfinite' : (νS.restrict (box n)) a ≠ ∞ := by
                  rw [← hνn_eq n]
                  exact hfinite
                simpa [MeasureTheory.Measure.restrict_apply ha, Set.inter_comm] using hfinite')
              (1 : ℝ) ∈ closure Dcore := by
        -- Route correction: approximate inside the finite box using the restricted product measure,
        -- then rewrite the approximants back into `closure Dcore` only once.
        let h𝒜 :
            (νn n).MeasureDense
              (MeasureTheory.generateSetAlgebra
                (Set.image2 (fun s t : Set Ω ↦ s ×ˢ t)
                  {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t})) :=
          measurableRectangleAlgebraMeasureDense (μ := μ.restrict (U n))
        refine Metric.mem_closure_iff.2 ?_
        intro ε hε
        obtain ⟨η, hη_pos, hη⟩ :=
          MeasureTheory.exists_eLpNorm_indicator_le
            (μ := νS) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ))
            (ε := ENNReal.ofReal (ε / 2)) (by simp) (by positivity)
        obtain ⟨t, ht, hμt, hμat⟩ :=
          MeasureTheory.Measure.MeasureDense.fin_meas_approx h𝒜 ha hfinite η hη_pos
        have ht_meas : MeasurableSet t := h𝒜.measurable t ht
        have ht_local :
            t ∩ box n ∈ MeasureTheory.generateSetAlgebra
              (Set.image2 (fun s t : Set Ω ↦ (s ∩ U n) ×ˢ (t ∩ U n))
                {s : Set Ω | MeasurableSet s} {t : Set Ω | MeasurableSet t}) := by
          simpa [box] using
            rectAlgebraInterFiniteBox_memGenerateSetAlgebra
              (U n) (U n) t (hU_meas n) (hU_meas n) ht
        have hbox_t_mem :
            ∃ hφνS :
                MeasureTheory.MemLp (fun z : Ω × Ω ↦ ((t ∩ box n).indicator (fun _ ↦ (1 : ℝ)) z))
                  2 νS,
              hφνS.toLp
                  (fun z : Ω × Ω ↦ ((t ∩ box n).indicator (fun _ ↦ (1 : ℝ)) z)) ∈ Dcore := by
          simpa [box, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
            hboxIndicatorConst_mem_closure_Dcore
              (U := U n) (V := U n) (a := t ∩ box n) (1 : ℝ)
              (hU_meas n) (hU_meas n) (hU_subset n) (hU_subset n)
              (hU_finite n) (hU_finite n) ht_local
        rcases hbox_t_mem with
          ⟨htLp, ht_closure⟩
        have hμt_box : νS (t ∩ box n) ≠ ∞ := by
          have hμt' : (νS.restrict (box n)) t ≠ ∞ := by
            rw [← hνn_eq n]
            exact hμt
          simpa [MeasureTheory.Measure.restrict_apply ht_meas, Set.inter_comm] using hμt'
        have htLp_eq :
            htLp.toLp (fun z : Ω × Ω ↦ ((t ∩ box n).indicator (fun _ ↦ (1 : ℝ)) z)) =
              MeasureTheory.indicatorConstLp 2 (ht_meas.inter (hbox_meas n)) hμt_box (1 : ℝ) := by
          calc
            htLp.toLp (fun z : Ω × Ω ↦ ((t ∩ box n).indicator (fun _ ↦ (1 : ℝ)) z)) =
                MeasureTheory.MemLp.toLp
                  (fun z : Ω × Ω ↦ ((t ∩ box n).indicator (fun _ ↦ (1 : ℝ)) z))
                  (MeasureTheory.memLp_indicator_const
                    2 (ht_meas.inter (hbox_meas n)) (1 : ℝ) (Or.inr hμt_box)) := by
                      exact MeasureTheory.MemLp.toLp_congr htLp
                        (MeasureTheory.memLp_indicator_const
                          2 (ht_meas.inter (hbox_meas n)) (1 : ℝ) (Or.inr hμt_box)) (by
                          filter_upwards with z
                          rfl)
            _ = MeasureTheory.indicatorConstLp 2 (ht_meas.inter (hbox_meas n)) hμt_box (1 : ℝ) := by
                  rfl
        have hsymm_box :
            symmDiff (a ∩ box n) (t ∩ box n) = symmDiff a t ∩ box n := by
          ext z
          by_cases hzbox : z ∈ box n <;> by_cases hza : z ∈ a <;> by_cases hzt : z ∈ t <;>
            simp [Set.mem_symmDiff, hzbox, hza, hzt]
        have hsymm_le :
            νS (symmDiff (a ∩ box n) (t ∩ box n)) ≤ η := by
          calc
            νS (symmDiff (a ∩ box n) (t ∩ box n)) =
                (νS.restrict (box n)) (symmDiff a t) := by
              rw [hsymm_box, MeasureTheory.Measure.restrict_apply (ha.symmDiff ht_meas),
                Set.inter_comm]
            _ = νn n (symmDiff a t) := by rw [← hνn_eq n]
            _ ≤ η := by simpa using le_of_lt hμat
        refine ⟨htLp.toLp (fun z : Ω × Ω ↦ ((t ∩ box n).indicator (fun _ ↦ (1 : ℝ)) z)),
          ht_closure, ?_⟩
        rw [htLp_eq, MeasureTheory.dist_indicatorConstLp_eq_norm]
        have hsmall :
            MeasureTheory.eLpNorm
                (((symmDiff (a ∩ box n) (t ∩ box n)).indicator
                  (fun _ ↦ (1 : ℝ))) : Ω × Ω → ℝ)
                2 νS ≤ ENNReal.ofReal (ε / 2) := hη _ hsymm_le
        have hsymm_ne_top :
            νS (symmDiff (a ∩ box n) (t ∩ box n)) ≠ ∞ := by
          exact ne_of_lt (lt_of_le_of_lt hsymm_le (by simp))
        have hnorm_le :
            ‖MeasureTheory.indicatorConstLp (μ := νS) 2
                ((ha.inter (hbox_meas n)).symmDiff (ht_meas.inter (hbox_meas n)))
                hsymm_ne_top (1 : ℝ)‖ ≤ ε / 2 := by
          rw [MeasureTheory.indicatorConstLp, MeasureTheory.Lp.norm_toLp]
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsmall
        exact lt_of_le_of_lt hnorm_le (by linarith)
      have hsigmaFiniteCoreIndicator_mem_closure_Dcore
          {a : Set (Ω × Ω)} (ha : MeasurableSet a) (hfinite : νS a < ∞) :
          MeasureTheory.indicatorConstLp 2 ha hfinite.ne (1 : ℝ) ∈ closure Dcore := by
        have hbox_finite : ∀ n, νS (a ∩ box n) < ∞ := by
          intro n
          exact (MeasureTheory.measure_mono Set.inter_subset_left).trans_lt hfinite
        have hbox_mem :
            ∀ n, MeasureTheory.indicatorConstLp (μ := νS) 2 (ha.inter (hbox_meas n))
              (hbox_finite n).ne (1 : ℝ) ∈ closure Dcore := by
          intro n
          have hfinite_n : νn n a ≠ ∞ := by
            have hfinite_eq : νn n a = νS (a ∩ box n) := by
              rw [hνn_eq n, MeasureTheory.Measure.restrict_apply ha, Set.inter_comm]
            exact hfinite_eq ▸ (hbox_finite n).ne
          exact hspanningBoxIndicator_mem_closure_Dcore n ha hfinite_n
        let bad : ℕ → Set (Ω × Ω) := fun n ↦ a ∩ (box n)ᶜ
        have hbad_meas : ∀ n, MeasurableSet (bad n) := by
          intro n
          exact ha.inter (hbox_meas n).compl
        have hbad_antitone : Antitone bad := by
          intro m n hmn
          exact Set.inter_subset_inter_right a (Set.compl_subset_compl.2 (hbox_mono hmn))
        have hbad_fin : ∃ n, νS (bad n) ≠ ∞ := by
          refine ⟨0, ?_⟩
          exact ((MeasureTheory.measure_mono Set.inter_subset_left).trans_lt hfinite).ne
        have hbad_iInter : ⋂ n, bad n = a ∩ coreBoxᶜ := by
          ext z
          constructor
          · intro hz
            have hza : z ∈ a := by
              exact (Set.mem_iInter.1 hz 0).1
            have hzcore : z ∉ coreBox := by
              intro hzcore
              rw [← hbox_iUnion] at hzcore
              rcases Set.mem_iUnion.1 hzcore with ⟨n, hn⟩
              exact (Set.mem_iInter.1 hz n).2 hn
            exact ⟨hza, hzcore⟩
          · intro hz
            refine Set.mem_iInter.2 ?_
            intro n
            exact ⟨hz.1, fun hboxz ↦ hz.2 (hbox_subset_core n hboxz)⟩
        have hbad_null : νS (⋂ n, bad n) = 0 := by
          have hcoreBox_meas : MeasurableSet coreBox := by
            exact MeasureTheory.measurableSet_sigmaFiniteSet.prod
              MeasureTheory.measurableSet_sigmaFiniteSet
          calc
            νS (⋂ n, bad n) = νS (a ∩ coreBoxᶜ) := by rw [hbad_iInter]
            _ = ((MeasureTheory.Measure.prod μ μ).restrict coreBox) (a ∩ coreBoxᶜ) := by
              rw [hνS_eq]
            _ = (MeasureTheory.Measure.prod μ μ) ((a ∩ coreBoxᶜ) ∩ coreBox) := by
              rw [MeasureTheory.Measure.restrict_apply (ha.inter hcoreBox_meas.compl)]
            _ = 0 := by
              have hempty : (a ∩ coreBoxᶜ) ∩ coreBox = ∅ := by
                ext z
                simp
              rw [hempty]
              simp
        have hbad_tendsto :
            Filter.Tendsto (νS ∘ bad) Filter.atTop (nhds 0) := by
          simpa [hbad_null] using
            (MeasureTheory.tendsto_measure_iInter_atTop
              (μ := νS) (s := bad)
              (fun n ↦ (hbad_meas n).nullMeasurableSet) hbad_antitone hbad_fin)
        have hsymm_box : ∀ n, symmDiff (a ∩ box n) a = bad n := by
          intro n
          ext z
          by_cases hza : z ∈ a <;> by_cases hzbox : z ∈ box n <;>
            simp [bad, Set.mem_symmDiff, hza, hzbox]
        have htendsto_sets :
            Filter.Tendsto (fun n ↦ νS (symmDiff (a ∩ box n) a)) Filter.atTop (nhds 0) := by
          convert hbad_tendsto using 1
          ext n
          simp [Function.comp, hsymm_box n]
        have htendsto_indicator :
            Filter.Tendsto
              (fun n ↦ MeasureTheory.indicatorConstLp (μ := νS) 2 (ha.inter (hbox_meas n))
                (hbox_finite n).ne (1 : ℝ))
              Filter.atTop
                (nhds (MeasureTheory.indicatorConstLp (μ := νS) 2 ha hfinite.ne (1 : ℝ))) := by
          exact MeasureTheory.tendsto_indicatorConstLp_set
            (μ := νS) (p := (2 : ℝ≥0∞)) (s := a) (hs := ha) (hμs := hfinite.ne)
            (c := (1 : ℝ)) (hp := by simp) (t := fun n ↦ a ∩ box n)
            (ht := fun n ↦ ha.inter (hbox_meas n)) (hμt := fun n ↦ (hbox_finite n).ne)
            htendsto_sets
        exact isClosed_closure.mem_of_tendsto htendsto_indicator
          (Filter.Eventually.of_forall hbox_mem)
      have hsigmaFiniteCoreLp_mem_closure_Dcore :
          ∀ f : MeasureTheory.Lp ℝ 2 νS, f ∈ closure Dcore := by
        intro f
        refine MeasureTheory.Lp.induction (p := (2 : ℝ≥0∞)) (μ := νS)
          (hp_ne_top := by simp)
          (motive := fun f : MeasureTheory.Lp ℝ 2 νS ↦ f ∈ closure Dcore)
          ?_ ?_ isClosed_closure f
        · intro c a ha hfinite
          have hbase :
              MeasureTheory.indicatorConstLp 2 ha hfinite.ne (1 : ℝ) ∈ closure Dcore :=
            hsigmaFiniteCoreIndicator_mem_closure_Dcore ha hfinite
          have hscaled :
              c • MeasureTheory.indicatorConstLp 2 ha hfinite.ne (1 : ℝ) ∈ closure Dcore :=
            hclosure_smul c hbase
          have hindicator_smul :
              MeasureTheory.indicatorConstLp 2 ha hfinite.ne c =
                c • MeasureTheory.indicatorConstLp 2 ha hfinite.ne (1 : ℝ) := by
            -- The general constant indicator is just a scalar multiple of the unit indicator.
            calc
              MeasureTheory.indicatorConstLp 2 ha hfinite.ne c =
                  MeasureTheory.MemLp.toLp
                    (c • fun z : Ω × Ω ↦ (a.indicator (fun _ ↦ (1 : ℝ)) z))
                    ((MeasureTheory.memLp_indicator_const 2 ha (1 : ℝ)
                      (Or.inr hfinite.ne)).const_smul c) := by
                        exact MeasureTheory.MemLp.toLp_congr
                          (MeasureTheory.memLp_indicator_const 2 ha c (Or.inr hfinite.ne))
                          ((MeasureTheory.memLp_indicator_const 2 ha (1 : ℝ)
                            (Or.inr hfinite.ne)).const_smul c) (by
                              filter_upwards with z
                              by_cases hz : z ∈ a <;>
                                simp [hz, Pi.smul_apply, smul_eq_mul])
              _ = c • MeasureTheory.indicatorConstLp 2 ha hfinite.ne (1 : ℝ) := by
                    exact MeasureTheory.MemLp.toLp_const_smul c
                      (MeasureTheory.memLp_indicator_const 2 ha (1 : ℝ) (Or.inr hfinite.ne))
          simpa [hindicator_smul] using hscaled
        · intro f g hf hg _ hf_closure hg_closure
          simpa using hclosure_add hf_closure hg_closure
      exact hsigmaFiniteCoreLp_mem_closure_Dcore (hkνS.toLp (fun z : Ω × Ω ↦ k z.1 z.2))
    intro ε hε
    rcases Metric.mem_closure_iff.1 hkνS_mem_closure ε hε with ⟨f, hfDcore, hclose⟩
    rcases hfDcore with ⟨φ, hφ, hφνS, hφ_off, rfl⟩
    refine ⟨φ, hφ, ?_⟩
    exact hambient_of_coreApprox hφ hφνS hφ_off (by simpa [dist_eq_norm] using hclose)
  -- Once the product-`L²` approximation oracle is available, the operator sequence is assembled
  -- abstractly by choosing `1 / (n + 1)` approximants and squeezing the operator norm to zero.
  exact exists_compactApprox_tendsto_of_lpApprox (μ := μ) (k := k) h_kernel happrox

/-- A Fredholm first-kind integral operator realization on real `L²(Ω)` is compact whenever its
kernel is square-integrable on `Ω × Ω`. -/
theorem IsKernelOperator.isCompactOperator
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) :
    IsCompactOperator K := by
  -- Route correction: the compactness proof now targets direct operator-norm approximation by
  -- finite rectangle-kernel operators, so the only remaining gap is the explicit approximation
  -- theorem `exists_rectKernelApprox_tendsto`.
  have h_eq :
      K = canonicalKernelOperator μ k h_kernel := by
    exact kernelOperator_ext (μ := μ) (k := k) hK
      (canonicalKernelOperator_isKernelOperator (μ := μ) (k := k) h_kernel)
  rw [h_eq]
  rcases exists_rectKernelApprox_tendsto (μ := μ) (k := k) h_kernel with ⟨T, hTcompact, hTlim⟩
  have hTendsto :
      Filter.Tendsto T Filter.atTop (nhds (canonicalKernelOperator μ k h_kernel)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hTlim
  -- Compact operators form a norm-closed set, so the compact approximants force the limit
  -- operator to be compact as well.
  exact
    isClosed_setOf_isCompactOperator.mem_of_tendsto hTendsto
      (Filter.Eventually.of_forall hTcompact)

end

/-- The square-integrable kernel with swapped variables also defines a Fredholm operator. -/
theorem kernel_swap_memLp [MeasureTheory.SFinite μ]
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ)) :
    MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.2 z.1) 2
      (MeasureTheory.Measure.prod μ μ) := by
  -- Swapping the variables preserves the product measure, so the `L²` norm is unchanged.
  convert
    (h_kernel.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap (μ := μ) (ν := μ)) :
        MeasureTheory.MemLp (((fun z : Ω × Ω ↦ k z.1 z.2) ∘ Prod.swap)) 2
          (MeasureTheory.Measure.prod μ μ))
  rfl

/-- Helper for Example 2.4: pairing against a finite-measure indicator test identifies the
adjoint with the swapped canonical kernel realization. -/
theorem indicatorConst_pairing_adjoint_eq_swap
    [MeasureTheory.SFinite μ]
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s < ∞) (c : ℝ)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    inner ℝ (K f) (MeasureTheory.Lp.simpleFunc.indicatorConst 2 hs hμs.ne c) =
      inner ℝ f
        ((canonicalKernelOperator μ (fun x y ↦ k y x)
          (kernel_swap_memLp (μ := μ) (k := k) h_kernel))
          (MeasureTheory.Lp.simpleFunc.indicatorConst 2 hs hμs.ne c)) := by
  -- Package the swapped canonical realization once so the later rewrites stay stable.
  let g : MeasureTheory.Lp ℝ 2 μ := MeasureTheory.Lp.simpleFunc.indicatorConst 2 hs hμs.ne c
  let Kswap : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
    canonicalKernelOperator μ (fun x y ↦ k y x) (kernel_swap_memLp (μ := μ) (k := k) h_kernel)
  have hg_ae : g =ᵐ[μ] s.indicator fun _ ↦ c := by
    simpa [g] using
      (MeasureTheory.indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
        (hs := hs) (hμs := hμs.ne) (c := c))
  have hKswap :
      IsKernelOperator μ (fun x y ↦ k y x) Kswap :=
    canonicalKernelOperator_isKernelOperator (μ := μ) (k := fun x y ↦ k y x)
      (kernel_swap_memLp (μ := μ) (k := k) h_kernel)
  -- Restrict the first variable to the finite-measure set `s` so Fubini applies to the product
  -- integrand built from the kernel and the fixed `L²` datum `f`.
  letI : MeasureTheory.IsFiniteMeasure (μ.restrict s) :=
    (MeasureTheory.isFiniteMeasure_restrict).2 hμs.ne
  have h_kernel_restrict :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2 ((μ.restrict s).prod μ) := by
    convert (h_kernel.restrict (s ×ˢ Set.univ)) using 1
    rw [MeasureTheory.Measure.restrict_prod_eq_prod_univ]
  have hf_prod :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ f z.2) 2 ((μ.restrict s).prod μ) := by
    simpa using (MeasureTheory.Lp.memLp f).comp_snd (μ.restrict s)
  have h_fubini :
      MeasureTheory.Integrable (fun z : Ω × Ω ↦ k z.1 z.2 * f z.2 * c)
        ((μ.restrict s).prod μ) := by
    exact (h_kernel_restrict.integrable_mul hf_prod).mul_const c
  -- Rewrite the left pairing as an iterated integral over the restricted first measure.
  have h_left :
      inner ℝ (K f) g = ∫ x in s, ∫ y, k x y * f y * c ∂μ ∂μ := by
    calc
      inner ℝ (K f) g = ∫ x, K f x * g x ∂μ := by
        rw [MeasureTheory.L2.inner_def]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [mul_comm]
      _ = ∫ x, s.indicator (fun x ↦ K f x * c) x ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hg_ae] with x hx
        by_cases hx_mem : x ∈ s <;> simp [hx, hx_mem]
      _ = ∫ x in s, K f x * c ∂μ := by
        rw [MeasureTheory.integral_indicator hs]
      _ = ∫ x in s, (∫ y, k x y * f y ∂μ) * c ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact MeasureTheory.ae_restrict_of_ae <| (hK f).mono fun x hx ↦ by
          simp [kernelFunction_apply, hx]
      _ = ∫ x in s, ∫ y, k x y * f y * c ∂μ ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact MeasureTheory.ae_restrict_of_ae <|
          (kernelSection_memLp_ae (μ := μ) (k := k) h_kernel).mono fun x hx ↦ by
            have hf_int : MeasureTheory.Integrable (fun y ↦ k x y * f y) μ :=
              hx.integrable_mul (MeasureTheory.Lp.memLp f)
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (MeasureTheory.integral_const_mul c (fun y ↦ k x y * f y)).symm
  -- Rewrite the right pairing so it matches the same product integrand after swapping variables.
  have h_right :
      inner ℝ f (Kswap g) = ∫ y, ∫ x in s, k x y * f y * c ∂μ ∂μ := by
    calc
      inner ℝ f (Kswap g) = ∫ y, f y * Kswap g y ∂μ := by
        rw [MeasureTheory.L2.inner_def]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        simp [mul_comm]
      _ = ∫ y, f y * kernelFunction μ (fun x y ↦ k y x) g y ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact (hKswap g).mono fun y hy ↦ by simp [hy]
      _ = ∫ y, f y * ∫ x in s, k x y * c ∂μ ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        have h_indicator :
            (fun x ↦ k x y * g x) =ᵐ[μ] s.indicator (fun x ↦ k x y * c) := by
          filter_upwards [hg_ae] with x hx
          by_cases hx_mem : x ∈ s <;> simp [hx, hx_mem, mul_comm]
        calc
          f y * kernelFunction μ (fun x y ↦ k y x) g y
              = f y * ∫ x, k x y * g x ∂μ := by
                  rfl
          _ = f y * ∫ x, s.indicator (fun x ↦ k x y * c) x ∂μ := by
                rw [MeasureTheory.integral_congr_ae h_indicator]
          _ = f y * ∫ x in s, k x y * c ∂μ := by
                rw [MeasureTheory.integral_indicator hs]
      _ = ∫ y, ∫ x in s, k x y * f y * c ∂μ ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (MeasureTheory.integral_const_mul (f y) (fun x ↦ k x y * c)).symm
  -- The two iterated integrals are equal by Fubini on the finite-by-sigma-finite product space.
  calc
    inner ℝ (K f) g = ∫ x in s, ∫ y, k x y * f y * c ∂μ ∂μ := h_left
    _ = ∫ y, ∫ x in s, k x y * f y * c ∂μ ∂μ := by
      simpa [Function.uncurry] using
        (MeasureTheory.integral_integral_swap
          (μ := μ.restrict s) (ν := μ) (f := fun x y ↦ k x y * f y * c) h_fubini)
    _ = inner ℝ f (Kswap g) := h_right.symm

/-- The adjoint of a Fredholm kernel operator realization realizes the swapped kernel. -/
theorem IsKernelOperator.adjoint_isKernelOperator_swap
    [MeasureTheory.SFinite μ]
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) :
    IsKernelOperator μ (fun x y ↦ k y x) (ContinuousLinearMap.adjoint K) := by
  -- Route correction: compare the adjoint with the swapped canonical realization on finite-measure
  -- indicator tests, then extend the equality to all `L²` vectors by density.
  let Kswap : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
    canonicalKernelOperator μ (fun x y ↦ k y x) (kernel_swap_memLp (μ := μ) (k := k) h_kernel)
  have h_adjoint_eq_vec :
      ∀ g : MeasureTheory.Lp ℝ 2 μ, ContinuousLinearMap.adjoint K g = Kswap g := by
    intro g
    refine MeasureTheory.Lp.induction (p := (2 : ℝ≥0∞)) (μ := μ)
      (hp_ne_top := by simp)
      (motive := fun g : MeasureTheory.Lp ℝ 2 μ =>
        ContinuousLinearMap.adjoint K g = Kswap g)
      ?_ ?_ ?_ g
    · intro c s hs hμs
      -- The indicator base case follows from the finite-measure pairing identity.
      apply ext_inner_left ℝ
      intro f
      rw [ContinuousLinearMap.adjoint_inner_right]
      simpa [Kswap] using indicatorConst_pairing_adjoint_eq_swap
        (μ := μ) (k := k) h_kernel hK s hs hμs c f
    · intro f g hf hg _ hfg hgg
      -- Both operators are linear, so equality propagates across the additive induction step.
      calc
        ContinuousLinearMap.adjoint K (hf.toLp f + hg.toLp g)
            = ContinuousLinearMap.adjoint K (hf.toLp f) +
                ContinuousLinearMap.adjoint K (hg.toLp g) := by
                  rw [map_add]
        _ = Kswap (hf.toLp f) + Kswap (hg.toLp g) := by rw [hfg, hgg]
        _ = Kswap (hf.toLp f + hg.toLp g) := by rw [map_add]
    · -- The zero set of the continuous difference map is closed.
      exact isClosed_eq (ContinuousLinearMap.adjoint K).continuous Kswap.continuous
  have h_adjoint_eq : ContinuousLinearMap.adjoint K = Kswap := by
    ext g
    let u : Ω →ₘ[μ] ℝ := ((ContinuousLinearMap.adjoint K) g : Ω →ₘ[μ] ℝ)
    let v : Ω →ₘ[μ] ℝ := ((Kswap g : Ω →ₘ[μ] ℝ))
    have huv : u = v := by
      simpa [u, v] using
        congrArg (fun w : MeasureTheory.Lp ℝ 2 μ => (w : Ω →ₘ[μ] ℝ)) (h_adjoint_eq_vec g)
    rw [← u.mk_coeFn, ← v.mk_coeFn, MeasureTheory.AEEqFun.mk_eq_mk] at huv
    simpa [u, v] using huv
  -- Transport the swapped-kernel formula from the canonical realization across the operator
  -- equality proved by density.
  rw [h_adjoint_eq]
  exact canonicalKernelOperator_isKernelOperator (μ := μ) (k := fun x y ↦ k y x)
    (kernel_swap_memLp (μ := μ) (k := k) h_kernel)

/-- The adjoint of a Fredholm kernel operator realization equals any realization of the swapped
kernel. -/
theorem kernelOperator_adjoint_eq_swap
    [MeasureTheory.SFinite μ]
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    {K K' : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K)
    (hK' : IsKernelOperator μ (fun x y ↦ k y x) K') :
    ContinuousLinearMap.adjoint K = K' := by
  exact kernelOperator_ext μ (fun x y ↦ k y x)
    (IsKernelOperator.adjoint_isKernelOperator_swap μ k h_kernel hK) hK'

/-- An almost-everywhere symmetric Fredholm kernel induces a self-adjoint bounded operator on
real `L²(Ω)`. -/
theorem kernelOperator_isSelfAdjoint_of_ae_symmetric
    [MeasureTheory.SFinite μ]
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (h_symm :
      (fun z : Ω × Ω ↦ k z.1 z.2) =ᵐ[MeasureTheory.Measure.prod μ μ]
        fun z ↦ k z.2 z.1)
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) :
    IsSelfAdjoint K := by
  -- Route correction: use product-a.e. symmetry to show that `K` itself realizes the swapped
  -- kernel, then compare it with the adjoint via the swapped-kernel uniqueness theorem.
  have hKswap : IsKernelOperator μ (fun x y ↦ k y x) K := by
    intro f
    -- The product-a.e. symmetry yields a.e. symmetry on almost every section.
    have h_sections : ∀ᵐ x ∂μ, (fun y ↦ k x y) =ᵐ[μ] fun y ↦ k y x := by
      simpa [Function.uncurry] using
        (MeasureTheory.Measure.ae_ae_eq_of_ae_eq_uncurry
          (μ := μ) (ν := μ) (f := k) (g := fun x y ↦ k y x) h_symm)
    filter_upwards [hK f, h_sections] with x hxK hxsec
    -- For each good section, the defining integrals agree by pointwise kernel symmetry.
    have h_integral :
        ∫ y, k x y * f y ∂μ = ∫ y, k y x * f y ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hxsec] with y hy
      simp [hy]
    calc
      K f x = kernelFunction μ k f x := hxK
      _ = ∫ y, k x y * f y ∂μ := rfl
      _ = ∫ y, k y x * f y ∂μ := h_integral
      _ = kernelFunction μ (fun x y ↦ k y x) f x := rfl
  -- Both `K` and `K†` realize the swapped kernel, so uniqueness forces equality.
  have h_adjoint_eq :
      ContinuousLinearMap.adjoint K = K :=
    kernelOperator_ext μ (fun x y ↦ k y x)
      (IsKernelOperator.adjoint_isKernelOperator_swap μ k h_kernel hK) hKswap
  simpa using (ContinuousLinearMap.isSelfAdjoint_iff'.2 h_adjoint_eq)

/-- A pointwise symmetric Fredholm kernel induces a self-adjoint bounded operator on real
`L²(Ω)`. -/
theorem kernelOperator_isSelfAdjoint_of_symmetric
    [MeasureTheory.SFinite μ]
    (h_kernel :
      MeasureTheory.MemLp (fun z : Ω × Ω ↦ k z.1 z.2) 2
        (MeasureTheory.Measure.prod μ μ))
    (h_symm : ∀ x y, k x y = k y x)
    {K : MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ}
    (hK : IsKernelOperator μ k K) :
    IsSelfAdjoint K := by
  exact kernelOperator_isSelfAdjoint_of_ae_symmetric μ k h_kernel
    (Filter.Eventually.of_forall fun z ↦ h_symm z.1 z.2) hK

end RealL2
