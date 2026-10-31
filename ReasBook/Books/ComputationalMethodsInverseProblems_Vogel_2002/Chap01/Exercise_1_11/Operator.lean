/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1.Fredholm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod

public section

noncomputable section

namespace Fredholm1D

/-- The measure model for `L²(0, 1)` used in Exercise 1.11. -/
@[expose] def unitIntervalMeasure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- The pointwise Gaussian Fredholm blur of an `L²(0, 1)` datum. -/
@[expose] def gaussianBlurFunction (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) : ℝ → ℝ :=
  fun x ↦ ∫ t, gaussianKernel C γ (x - t) * f t ∂unitIntervalMeasure

/-- The defining integral formula for `gaussianBlurFunction`. -/
theorem gaussianBlurFunction_apply (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) (x : ℝ) :
    gaussianBlurFunction C γ f x =
      ∫ t, gaussianKernel C γ (x - t) * f t ∂unitIntervalMeasure := rfl

/-- The Gaussian kernel is uniformly bounded by `|C|`. -/
theorem norm_gaussianKernel_le (C γ t : ℝ) : ‖gaussianKernel C γ t‖ ≤ |C| := by
  rw [gaussianKernel_apply, Real.norm_eq_abs, abs_mul]
  have hexp : |Real.exp (-(t ^ 2) / (2 * γ ^ 2))| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    rcases eq_or_ne γ 0 with hγ | hγ
    · simp [hγ]
    · have h2 : (0 : ℝ) < 2 * γ ^ 2 := by positivity
      have h3 : 0 ≤ t ^ 2 / (2 * γ ^ 2) := div_nonneg (sq_nonneg t) h2.le
      rw [neg_div]
      exact neg_nonpos.mpr h3
  calc |C| * |Real.exp (-(t ^ 2) / (2 * γ ^ 2))| ≤ |C| * 1 := by gcongr
    _ = |C| := by ring

/-- For fixed `x`, the blurred integrand `t ↦ k (x - t) * f t` is integrable. -/
theorem integrable_gaussianKernel_mul (C γ : ℝ) (x : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    MeasureTheory.Integrable
      (fun t : ℝ => gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t) unitIntervalMeasure := by
  have hprob : MeasureTheory.IsProbabilityMeasure unitIntervalMeasure := by
    constructor
    show unitIntervalMeasure Set.univ = 1
    rw [unitIntervalMeasure, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num
  haveI := hprob
  have hcont : Continuous (gaussianKernel C γ) := by
    show Continuous (fun x : ℝ => C * Real.exp (-(x ^ 2) / (2 * γ ^ 2)))
    fun_prop
  have hfi : MeasureTheory.Integrable (fun t : ℝ => (f : ℝ → ℝ) t) unitIntervalMeasure :=
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (MeasureTheory.Lp.memLp f)
  have hk_meas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => gaussianKernel C γ (x - t))
      unitIntervalMeasure :=
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact hfi.bdd_mul hk_meas
    (Filter.Eventually.of_forall (fun t => norm_gaussianKernel_le C γ (x - t)))

/-- The restricted measure on `(0, 1)` is a probability measure. -/
theorem isProbabilityMeasure_unitIntervalMeasure :
    MeasureTheory.IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  show unitIntervalMeasure Set.univ = 1
  rw [unitIntervalMeasure, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

/-- On the probability space `(0, 1)`, the `L¹` norm is bounded by the `L²` norm. -/
theorem integral_norm_le_norm (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure ≤ ‖f‖ := by
  haveI := isProbabilityMeasure_unitIntervalMeasure
  have hfi : MeasureTheory.Integrable (fun t : ℝ => (f : ℝ → ℝ) t) unitIntervalMeasure :=
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      (MeasureTheory.Lp.memLp f)
  have h1 : MeasureTheory.eLpNorm (f : ℝ → ℝ) 1 unitIntervalMeasure
      ≤ MeasureTheory.eLpNorm (f : ℝ → ℝ) 2 unitIntervalMeasure :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 2)
      (MeasureTheory.Lp.aestronglyMeasurable f)
  have hlin : ENNReal.ofReal (∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure)
      = ∫⁻ t, ‖(f : ℝ → ℝ) t‖ₑ ∂unitIntervalMeasure :=
    MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hfi
  calc ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure
      = (∫⁻ t, ‖(f : ℝ → ℝ) t‖ₑ ∂unitIntervalMeasure).toReal := by
        rw [← hlin, ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg (fun t => norm_nonneg _))]
    _ = (MeasureTheory.eLpNorm (f : ℝ → ℝ) 1 unitIntervalMeasure).toReal := by
        rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (MeasureTheory.eLpNorm (f : ℝ → ℝ) 2 unitIntervalMeasure).toReal :=
        ENNReal.toReal_mono (ne_top_of_lt (MeasureTheory.Lp.memLp f).2) h1
    _ = ‖f‖ := by rw [MeasureTheory.Lp.norm_def]

/-- Pointwise bound for the Gaussian blur by the `L¹` norm of the datum. -/
theorem norm_gaussianBlurFunction_le (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) (x : ℝ) :
    ‖gaussianBlurFunction C γ f x‖
      ≤ |C| * ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure := by
  haveI := isProbabilityMeasure_unitIntervalMeasure
  rw [gaussianBlurFunction_apply]
  calc ‖∫ t, gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t ∂unitIntervalMeasure‖
      ≤ ∫ t, ‖gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t‖ ∂unitIntervalMeasure :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, |C| * ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure := by
        refine MeasureTheory.integral_mono (integrable_gaussianKernel_mul C γ x f).norm
          ((MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
            (MeasureTheory.Lp.memLp f)).norm.const_mul |C|) ?_
        intro t
        show ‖gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t‖ ≤ |C| * ‖(f : ℝ → ℝ) t‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_gaussianKernel_le C γ (x - t)) (norm_nonneg _)
    _ = |C| * ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure :=
        MeasureTheory.integral_const_mul _ _

/-- The Gaussian blur of an `L²(0, 1)` datum is again an `L²(0, 1)` function class. -/
theorem gaussianBlurFunction_memLp (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    MeasureTheory.MemLp (gaussianBlurFunction C γ f) 2 unitIntervalMeasure := by
  have hcont : Continuous (gaussianKernel C γ) := by
    show Continuous (fun x : ℝ => C * Real.exp (-(x ^ 2) / (2 * γ ^ 2)))
    fun_prop
  -- The restricted measure on `(0, 1)` is a probability measure.
  have hprob : MeasureTheory.IsProbabilityMeasure unitIntervalMeasure := by
    constructor
    show unitIntervalMeasure Set.univ = 1
    rw [unitIntervalMeasure, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num
  haveI := hprob
  -- Measurability of `x ↦ ∫ t, k (x - t) * f t` as a parametric integral.
  have hmeas : MeasureTheory.AEStronglyMeasurable (gaussianBlurFunction C γ f)
      unitIntervalMeasure :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (f := fun p : ℝ × ℝ => gaussianKernel C γ (p.1 - p.2) * (f : ℝ → ℝ) p.2)
      (((hcont.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable f).comp_snd)
  -- Pointwise bound by `|C|` times the `L¹` norm of `f`, which is finite.
  refine MeasureTheory.MemLp.of_bound hmeas
    (|C| * ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure) ?_
  filter_upwards with x
  rw [gaussianBlurFunction_apply]
  have hfi : MeasureTheory.Integrable (fun t : ℝ => (f : ℝ → ℝ) t) unitIntervalMeasure :=
    MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      (MeasureTheory.Lp.memLp f)
  have hfni : MeasureTheory.Integrable (fun t : ℝ => ‖(f : ℝ → ℝ) t‖) unitIntervalMeasure :=
    hfi.norm
  have hk_meas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => gaussianKernel C γ (x - t))
      unitIntervalMeasure :=
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : MeasureTheory.Integrable
      (fun t : ℝ => gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t) unitIntervalMeasure :=
    hfi.bdd_mul hk_meas
      (Filter.Eventually.of_forall (fun t => norm_gaussianKernel_le C γ (x - t)))
  calc ‖∫ t, gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t ∂unitIntervalMeasure‖
      ≤ ∫ t, ‖gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t‖ ∂unitIntervalMeasure :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, |C| * ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure := by
        refine MeasureTheory.integral_mono hint.norm (hfni.const_mul |C|) ?_
        intro t
        show ‖gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t‖ ≤ |C| * ‖(f : ℝ → ℝ) t‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_gaussianKernel_le C γ (x - t)) (norm_nonneg _)
    _ = |C| * ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure :=
        MeasureTheory.integral_const_mul _ _

/-- The `L²(0, 1)` Gaussian blur respects addition. -/
theorem gaussianBlurL2_map_add (C γ : ℝ)
    (f g : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    (gaussianBlurFunction_memLp C γ (f + g)).toLp (gaussianBlurFunction C γ (f + g)) =
      (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f) +
        (gaussianBlurFunction_memLp C γ g).toLp (gaussianBlurFunction C γ g) := by
  have hfun : gaussianBlurFunction C γ (f + g) =ᵐ[unitIntervalMeasure]
      gaussianBlurFunction C γ f + gaussianBlurFunction C γ g := by
    have hcoe : ((f + g : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) : ℝ → ℝ) =ᵐ[unitIntervalMeasure]
        (f : ℝ → ℝ) + (g : ℝ → ℝ) := MeasureTheory.Lp.coeFn_add f g
    filter_upwards with x
    simp only [Pi.add_apply]
    rw [gaussianBlurFunction_apply, gaussianBlurFunction_apply, gaussianBlurFunction_apply]
    calc ∫ t, gaussianKernel C γ (x - t)
          * ((f + g : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) : ℝ → ℝ) t ∂unitIntervalMeasure
        = ∫ t, gaussianKernel C γ (x - t) * ((f : ℝ → ℝ) t + (g : ℝ → ℝ) t)
            ∂unitIntervalMeasure := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hcoe] with t ht
          simp only [Pi.add_apply] at ht
          rw [ht]
      _ = ∫ t, (gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t +
            gaussianKernel C γ (x - t) * (g : ℝ → ℝ) t) ∂unitIntervalMeasure := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t; ring
      _ = ∫ t, gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t ∂unitIntervalMeasure +
          ∫ t, gaussianKernel C γ (x - t) * (g : ℝ → ℝ) t ∂unitIntervalMeasure :=
          MeasureTheory.integral_add (integrable_gaussianKernel_mul C γ x f)
            (integrable_gaussianKernel_mul C γ x g)
  rw [← MeasureTheory.MemLp.toLp_add (gaussianBlurFunction_memLp C γ f)
    (gaussianBlurFunction_memLp C γ g)]
  exact MeasureTheory.MemLp.toLp_congr _ _ hfun

/-- The `L²(0, 1)` Gaussian blur commutes with scalar multiplication. -/
theorem gaussianBlurL2_map_smul (C γ a : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    (gaussianBlurFunction_memLp C γ (a • f)).toLp (gaussianBlurFunction C γ (a • f)) =
      a • (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f) := by
  have hfun : gaussianBlurFunction C γ (a • f) =ᵐ[unitIntervalMeasure]
      a • gaussianBlurFunction C γ f := by
    have hcoe : ((a • f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) : ℝ → ℝ) =ᵐ[unitIntervalMeasure]
        a • (f : ℝ → ℝ) := MeasureTheory.Lp.coeFn_smul a f
    filter_upwards with x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [gaussianBlurFunction_apply, gaussianBlurFunction_apply]
    calc ∫ t, gaussianKernel C γ (x - t)
          * ((a • f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) : ℝ → ℝ) t ∂unitIntervalMeasure
        = ∫ t, gaussianKernel C γ (x - t) * (a * (f : ℝ → ℝ) t) ∂unitIntervalMeasure := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hcoe] with t ht
          simp only [Pi.smul_apply, smul_eq_mul] at ht
          rw [ht]
      _ = ∫ t, a * (gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t) ∂unitIntervalMeasure := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t; ring
      _ = a * ∫ t, gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t ∂unitIntervalMeasure :=
          MeasureTheory.integral_const_mul a _
  rw [← MeasureTheory.MemLp.toLp_const_smul a (gaussianBlurFunction_memLp C γ f)]
  exact MeasureTheory.MemLp.toLp_congr _ _ hfun

/-- The pointwise Gaussian blur induces a continuous `L²(0, 1)` operator. -/
theorem gaussianBlurL2_continuous (C γ : ℝ) :
    Continuous (fun f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure ↦
      (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f)) := by
  -- Bundle the map as a linear map; continuity then follows from the operator bound.
  let T : MeasureTheory.Lp ℝ 2 unitIntervalMeasure →ₗ[ℝ]
      MeasureTheory.Lp ℝ 2 unitIntervalMeasure :=
    { toFun := fun f ↦
        (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f)
      map_add' := gaussianBlurL2_map_add C γ
      map_smul' := gaussianBlurL2_map_smul C γ }
  have hbound : ∀ f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure, ‖T f‖ ≤ |C| * ‖f‖ := by
    intro f
    show ‖(gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f)‖ ≤ |C| * ‖f‖
    rw [MeasureTheory.Lp.norm_toLp]
    haveI := isProbabilityMeasure_unitIntervalMeasure
    have hae : ∀ᵐ x ∂unitIntervalMeasure, ‖gaussianBlurFunction C γ f x‖ ≤ |C| * ‖f‖ := by
      filter_upwards with x
      calc ‖gaussianBlurFunction C γ f x‖
          ≤ |C| * ∫ t, ‖(f : ℝ → ℝ) t‖ ∂unitIntervalMeasure :=
            norm_gaussianBlurFunction_le C γ f x
        _ ≤ |C| * ‖f‖ := by
            gcongr
            exact integral_norm_le_norm f
    have h1 : MeasureTheory.eLpNorm (gaussianBlurFunction C γ f) 2 unitIntervalMeasure
        ≤ ENNReal.ofReal (|C| * ‖f‖) := by
      refine (MeasureTheory.eLpNorm_le_of_ae_bound (p := 2) hae).trans_eq ?_
      simp
    calc (MeasureTheory.eLpNorm (gaussianBlurFunction C γ f) 2 unitIntervalMeasure).toReal
        ≤ (ENNReal.ofReal (|C| * ‖f‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = |C| * ‖f‖ := ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg C) (norm_nonneg f))
  exact AddMonoidHomClass.continuous_of_bound T |C| hbound

/-- The Chapter 1 Gaussian Fredholm blur operator on `L²(0, 1)`. -/
@[expose] def gaussianBlurL2 (C γ : ℝ) :
    MeasureTheory.Lp ℝ 2 unitIntervalMeasure →L[ℝ] MeasureTheory.Lp ℝ 2 unitIntervalMeasure :=
  { toLinearMap :=
      { toFun := fun f ↦
          (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f)
        map_add' := gaussianBlurL2_map_add C γ
        map_smul' := gaussianBlurL2_map_smul C γ }
    cont := gaussianBlurL2_continuous C γ }

/-- Applying `gaussianBlurL2` is the `Lp` class of `gaussianBlurFunction`. -/
theorem gaussianBlurL2_apply (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    gaussianBlurL2 C γ f =
      (gaussianBlurFunction_memLp C γ f).toLp (gaussianBlurFunction C γ f) := rfl

/-- The bundled Gaussian `L²(0, 1)` blur realizes the source operator `(1.1)`
specialized to `gaussianKernel C γ`. -/
theorem gaussianBlurL2_realizesOperator (C γ : ℝ)
    (f : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    gaussianBlurFunction C γ f = operator (gaussianKernel C γ) f := by
  -- Both sides integrate the same Gaussian kernel over `(0, 1)`; the left one uses the
  -- restricted measure on `Ioo 0 1` and the right one the interval integral on `Ioc 0 1`.
  funext x
  simp only [gaussianBlurFunction, operator, unitIntervalMeasure]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

open MeasureTheory

lemma gaussianKernel_neg (C γ s : ℝ) : gaussianKernel C γ (-s) = gaussianKernel C γ s := by
  rw [gaussianKernel_apply, gaussianKernel_apply, neg_sq]

lemma inner_eq_integral (f g : Lp ℝ 2 unitIntervalMeasure) :
    inner ℝ f g = ∫ x, (f : ℝ → ℝ) x * (g : ℝ → ℝ) x ∂unitIntervalMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [mul_comm]

theorem inner_gaussianBlurL2_swap (C γ : ℝ) (f g : Lp ℝ 2 unitIntervalMeasure) :
    inner ℝ (gaussianBlurL2 C γ f) g = inner ℝ f (gaussianBlurL2 C γ g) := by
  haveI := isProbabilityMeasure_unitIntervalMeasure
  have hfi : Integrable (fun x : ℝ => (f : ℝ → ℝ) x) unitIntervalMeasure :=
    MemLp.integrable (q := 2) (by norm_num) (Lp.memLp f)
  have hgi : Integrable (fun x : ℝ => (g : ℝ → ℝ) x) unitIntervalMeasure :=
    MemLp.integrable (q := 2) (by norm_num) (Lp.memLp g)
  have hprod' : Integrable (fun p : ℝ × ℝ => (g : ℝ → ℝ) p.1 * (f : ℝ → ℝ) p.2)
      (unitIntervalMeasure.prod unitIntervalMeasure) := hgi.mul_prod hfi
  have hKcont : Continuous (gaussianKernel C γ) := by
    show Continuous (fun x : ℝ => C * Real.exp (-(x ^ 2) / (2 * γ ^ 2)))
    fun_prop
  have hcoeT (z : Lp ℝ 2 unitIntervalMeasure) :
      (gaussianBlurL2 C γ z : ℝ → ℝ) =ᵐ[unitIntervalMeasure] gaussianBlurFunction C γ z := by
    rw [gaussianBlurL2_apply]
    exact MemLp.coeFn_toLp _
  have hblur (z : Lp ℝ 2 unitIntervalMeasure) :
      (gaussianBlurL2 C γ z : ℝ → ℝ) =ᵐ[unitIntervalMeasure]
        fun x => ∫ t, gaussianKernel C γ (x - t) * (z : ℝ → ℝ) t ∂unitIntervalMeasure :=
    (hcoeT z).trans (Filter.Eventually.of_forall (fun x => gaussianBlurFunction_apply C γ z x))
  -- Left side: `x` outside, `t` inside.
  have hL : inner ℝ (gaussianBlurL2 C γ f) g
      = ∫ x, ∫ t, gaussianKernel C γ (x - t) * ((f : ℝ → ℝ) t * (g : ℝ → ℝ) x)
          ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    rw [inner_eq_integral]
    calc ∫ x, (gaussianBlurL2 C γ f : ℝ → ℝ) x * (g : ℝ → ℝ) x ∂unitIntervalMeasure
        = ∫ x, (∫ t, gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t ∂unitIntervalMeasure)
              * (g : ℝ → ℝ) x ∂unitIntervalMeasure := by
          refine integral_congr_ae ?_
          filter_upwards [hblur f] with x hx
          rw [hx]
      _ = ∫ x, ∫ t, (gaussianKernel C γ (x - t) * (f : ℝ → ℝ) t) * (g : ℝ → ℝ) x
            ∂unitIntervalMeasure ∂unitIntervalMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          exact (MeasureTheory.integral_mul_const _ _).symm
      _ = ∫ x, ∫ t, gaussianKernel C γ (x - t) * ((f : ℝ → ℝ) t * (g : ℝ → ℝ) x)
            ∂unitIntervalMeasure ∂unitIntervalMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
          ring
  -- Right side: swap the two integrations (Fubini) and use symmetry of the kernel.
  have hR : inner ℝ f (gaussianBlurL2 C γ g)
      = ∫ x, ∫ t, gaussianKernel C γ (x - t) * ((f : ℝ → ℝ) t * (g : ℝ → ℝ) x)
          ∂unitIntervalMeasure ∂unitIntervalMeasure := by
    rw [inner_eq_integral]
    have hdom : Integrable
        (fun p : ℝ × ℝ => (|C| : ℝ) * ((f : ℝ → ℝ) p.1 * (g : ℝ → ℝ) p.2))
        (unitIntervalMeasure.prod unitIntervalMeasure) := (hfi.mul_prod hgi).const_mul |C|
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (gaussianKernel C γ (p.1 - p.2) * (g : ℝ → ℝ) p.2)
          * (f : ℝ → ℝ) p.1) (unitIntervalMeasure.prod unitIntervalMeasure) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => gaussianKernel C γ (p.1 - p.2))
          (unitIntervalMeasure.prod unitIntervalMeasure) :=
        (hKcont.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (g : ℝ → ℝ) p.2)
          (unitIntervalMeasure.prod unitIntervalMeasure) :=
        hgi.aestronglyMeasurable.comp_snd
      have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => (f : ℝ → ℝ) p.1)
          (unitIntervalMeasure.prod unitIntervalMeasure) :=
        hfi.aestronglyMeasurable.comp_fst
      exact (h1.mul h2).mul h3
    have hint : Integrable
        (fun p : ℝ × ℝ => (gaussianKernel C γ (p.1 - p.2) * (g : ℝ → ℝ) p.2)
          * (f : ℝ → ℝ) p.1) (unitIntervalMeasure.prod unitIntervalMeasure) := by
      refine Integrable.mono hdom hmeas ?_
      filter_upwards with p
      have hk := norm_gaussianKernel_le C γ (p.1 - p.2)
      have hg' : (0 : ℝ) ≤ ‖(g : ℝ → ℝ) p.2‖ := norm_nonneg _
      have hf' : (0 : ℝ) ≤ ‖(f : ℝ → ℝ) p.1‖ := norm_nonneg _
      calc ‖(gaussianKernel C γ (p.1 - p.2) * (g : ℝ → ℝ) p.2) * (f : ℝ → ℝ) p.1‖
          = ‖gaussianKernel C γ (p.1 - p.2)‖ * ‖(g : ℝ → ℝ) p.2‖
              * ‖(f : ℝ → ℝ) p.1‖ := by rw [norm_mul, norm_mul]
        _ ≤ |C| * ‖(g : ℝ → ℝ) p.2‖ * ‖(f : ℝ → ℝ) p.1‖ := by gcongr
        _ = ‖(|C| : ℝ) * ((f : ℝ → ℝ) p.1 * (g : ℝ → ℝ) p.2)‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_abs]
            ring
    calc ∫ x, (f : ℝ → ℝ) x * (gaussianBlurL2 C γ g : ℝ → ℝ) x ∂unitIntervalMeasure
        = ∫ x, (gaussianBlurL2 C γ g : ℝ → ℝ) x * (f : ℝ → ℝ) x ∂unitIntervalMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          ring
      _ = ∫ x, (∫ t, gaussianKernel C γ (x - t) * (g : ℝ → ℝ) t ∂unitIntervalMeasure)
              * (f : ℝ → ℝ) x ∂unitIntervalMeasure := by
          refine integral_congr_ae ?_
          filter_upwards [hblur g] with x hx
          rw [hx]
      _ = ∫ x, ∫ t, (gaussianKernel C γ (x - t) * (g : ℝ → ℝ) t) * (f : ℝ → ℝ) x
            ∂unitIntervalMeasure ∂unitIntervalMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          exact (MeasureTheory.integral_mul_const _ _).symm
      _ = ∫ t, ∫ x, (gaussianKernel C γ (x - t) * (g : ℝ → ℝ) t) * (f : ℝ → ℝ) x
            ∂unitIntervalMeasure ∂unitIntervalMeasure :=
          MeasureTheory.integral_integral_swap hint
      _ = ∫ x, ∫ t, (gaussianKernel C γ (t - x) * (g : ℝ → ℝ) x) * (f : ℝ → ℝ) t
            ∂unitIntervalMeasure ∂unitIntervalMeasure := rfl
      _ = ∫ x, ∫ t, gaussianKernel C γ (x - t) * ((f : ℝ → ℝ) t * (g : ℝ → ℝ) x)
            ∂unitIntervalMeasure ∂unitIntervalMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
          show gaussianKernel C γ (t - x) * (g : ℝ → ℝ) x * (f : ℝ → ℝ) t
              = gaussianKernel C γ (x - t) * ((f : ℝ → ℝ) t * (g : ℝ → ℝ) x)
          rw [show t - x = -(x - t) from by ring, gaussianKernel_neg]
          ring
  rw [hL, hR]

/-- The Gaussian `L²(0, 1)` blur operator is self-adjoint. -/
theorem gaussianBlurL2_adjoint_eq (C γ : ℝ) :
    ContinuousLinearMap.adjoint (gaussianBlurL2 C γ) = gaussianBlurL2 C γ := by
  refine ContinuousLinearMap.ext (fun f => ?_)
  refine ext_inner_right (𝕜 := ℝ) (fun y => ?_)
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (inner_gaussianBlurL2_swap C γ f y).symm

end Fredholm1D
