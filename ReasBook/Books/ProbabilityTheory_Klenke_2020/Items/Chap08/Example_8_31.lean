/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.WithDensity

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The `x`-marginal density obtained by integrating a joint density on `ℝ × ℝ` over the second
coordinate. -/
noncomputable def first_marginal_density (f : ℝ → ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun x ↦ ∫⁻ y, f x y ∂(volume : Measure ℝ)

/-- Helper for Example 8.31: the first marginal density of a measurable joint density is
measurable. -/
private theorem measurable_first_marginal_density
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2) :
    Measurable (first_marginal_density f) := by
  -- Proof comment: this is the standard measurability of the fiberwise Tonelli integral.
  simpa [first_marginal_density] using
    (Measurable.lintegral_prod_right (ν := (volume : Measure ℝ))
      (f := fun x y ↦ f x y) hf)

section JointDensity

variable (P : Measure Ω)
variable {X Y : Ω → ℝ} {f : ℝ → ℝ → ℝ≥0∞}
variable (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
variable
  (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
    (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
      fun z : ℝ × ℝ ↦ f z.1 z.2) P)

-- Proof sketch: rewrite the joint law of `(X, Y)` as the density measure on `ℝ × ℝ`, then push
-- forward along `Prod.fst` and use Fubini/product-measure identities to identify the resulting
-- marginal with `volume.withDensity (first_marginal_density f)`.
/-- The first marginal of a joint Lebesgue density is obtained by integrating out the second
coordinate. -/
theorem hasLaw_fst_withDensity_first_marginal
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P)
    :
    HasLaw X ((volume : Measure ℝ).withDensity (first_marginal_density f)) P := by
  let μjoint : Measure (ℝ × ℝ) :=
    (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
      fun z : ℝ × ℝ ↦ f z.1 z.2)
  have hfst_law :
      HasLaw Prod.fst ((volume : Measure ℝ).withDensity (first_marginal_density f)) μjoint := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    ext s hs
    -- Proof comment: push the joint density measure forward along `Prod.fst` and integrate out
    -- the second coordinate on the rectangle `s ×ˢ univ`.
    rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (measurable_fst hs),
      withDensity_apply _ hs]
    have hpre : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set ℝ) := by
      ext z
      simp
    rw [hpre, MeasureTheory.setLIntegral_prod (fun z : ℝ × ℝ ↦ f z.1 z.2)
      hf.aemeasurable.restrict]
    congr with x
    simp [first_marginal_density]
  simpa [μjoint, Function.comp] using hfst_law.comp hXY_law

-- Proof sketch: use the previous marginal-law statement to replace `P.map X` by
-- `volume.withDensity (first_marginal_density f)`, then show that the set where
-- `first_marginal_density f = 0` has zero mass for this density measure.
/-- Under the marginal law determined by a joint density, the marginal density is positive for
`P.map X`-almost every `x`. -/
theorem first_marginal_density_pos_ae_of_hasLaw_prod_withDensity
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P)
    :
    ∀ᵐ x ∂P.map X, 0 < first_marginal_density f x := by
  have hX_law := hasLaw_fst_withDensity_first_marginal (P := P) (X := X) (Y := Y) (f := f)
    hf hXY_law
  -- Proof comment: under the `withDensity` marginal law, only points with nonzero marginal
  -- density contribute.
  rw [hX_law.map_eq, ae_withDensity_iff (measurable_first_marginal_density (f := f) hf)]
  exact Filter.Eventually.of_forall fun x hx ↦ bot_lt_iff_ne_bot.mpr hx

/-- Helper for Example 8.31: away from points where the marginal density is infinite, multiplying
the normalized fiber kernel by the marginal density recovers the original fiber mass on every
measurable set. -/
private theorem firstMarginal_mul_densityRatioKernel_apply_of_ne_top
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    {t : Set ℝ} (ht : MeasurableSet t) {x : ℝ}
    (hx_top : first_marginal_density f x ≠ ∞) :
    first_marginal_density f x *
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun x y ↦ f x y / first_marginal_density f x) x t
      =
        ∫⁻ y in t, f x y ∂(volume : Measure ℝ) := by
  have hfm_meas := measurable_first_marginal_density (f := f) hf
  have hratio_meas :
      Measurable (Function.uncurry fun x y ↦ f x y / first_marginal_density f x) := by
    simpa [Function.uncurry] using hf.div (hfm_meas.comp measurable_fst)
  have hfiber_meas : Measurable fun y : ℝ ↦ f x y := Measurable.of_uncurry_left hf
  -- Proof comment: evaluate the `withDensity` kernel on `t` and split on whether the marginal
  -- density vanishes. If it does not vanish, finite cancellation gives the identity.
  rw [Kernel.withDensity_apply' (Kernel.const ℝ (volume : Measure ℝ)) hratio_meas]
  by_cases hx_zero : first_marginal_density f x = 0
  · have hzero_ae : ∀ᵐ y ∂(volume : Measure ℝ), f x y = 0 := by
      apply (lintegral_eq_zero_iff hfiber_meas).1
      simpa [first_marginal_density] using hx_zero
    have hfiber_zero :
        ∫⁻ y in t, f x y ∂(volume : Measure ℝ) = 0 := by
      apply (setLIntegral_eq_zero_iff ht hfiber_meas).2
      filter_upwards [hzero_ae] with y hy hy_mem
      simp [hy]
    have hratio_zero :
        ∫⁻ y in t, f x y / first_marginal_density f x ∂(volume : Measure ℝ) = 0 := by
      apply (setLIntegral_eq_zero_iff ht (hfiber_meas.div measurable_const)).2
      filter_upwards [hzero_ae] with y hy hy_mem
      simp [hx_zero, hy]
    simp [hx_zero, hfiber_zero]
  · rw [show (fun y : ℝ ↦ f x y / first_marginal_density f x) =
      fun y ↦ f x y * (first_marginal_density f x)⁻¹ by
        funext y
        rw [div_eq_mul_inv]]
    rw [lintegral_mul_const (first_marginal_density f x)⁻¹ hfiber_meas]
    calc
      first_marginal_density f x *
          ((∫⁻ y in t, f x y ∂(volume : Measure ℝ)) *
            (first_marginal_density f x)⁻¹)
        = (∫⁻ y in t, f x y ∂(volume : Measure ℝ)) *
            (first_marginal_density f x * (first_marginal_density f x)⁻¹) := by
              ac_rfl
      _ = (∫⁻ y in t, f x y ∂(volume : Measure ℝ)) * 1 := by
            rw [ENNReal.mul_inv_cancel hx_zero hx_top]
      _ = ∫⁻ y in t, f x y ∂(volume : Measure ℝ) := by simp

/-- Helper for Example 8.31: if the first marginal density vanishes at `x`, then the whole fiber
`y ↦ f x y` vanishes `volume`-almost everywhere. -/
private theorem fiber_ae_eq_zero_of_first_marginal_density_eq_zero
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    {x : ℝ} (hx : first_marginal_density f x = 0) :
    (fun y : ℝ ↦ f x y) =ᵐ[(volume : Measure ℝ)] 0 := by
  have hfiber_meas : Measurable fun y : ℝ ↦ f x y := Measurable.of_uncurry_left hf
  -- Proof comment: the fiber integral defining the marginal is zero, so the nonnegative fiber
  -- function itself is zero almost everywhere.
  exact (lintegral_eq_zero_iff hfiber_meas).mp (by simpa [first_marginal_density] using hx)

/-- Helper for Example 8.31: the raw density-ratio kernel has total mass at most `1` on every
fiber, so it is a finite kernel. -/
private theorem densityRatioKernel_univ_le_one
    {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2) :
    ∀ x : ℝ,
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun x y ↦ f x y / first_marginal_density f x) x Set.univ ≤ 1 := by
  have hratio_meas :
      Measurable (Function.uncurry fun x y ↦ f x y / first_marginal_density f x) := by
    simpa [Function.uncurry] using
      hf.div ((measurable_first_marginal_density (f := f) hf).comp measurable_fst)
  intro x
  by_cases hx_zero : first_marginal_density f x = 0
  · -- Proof comment: if the marginal mass is zero, the whole fiber density vanishes a.e., so the
    -- corresponding `withDensity` kernel is the zero measure.
    rw [Kernel.withDensity_apply' (Kernel.const ℝ (volume : Measure ℝ)) hratio_meas,
      Kernel.const_apply]
    have hzero_ae :=
      fiber_ae_eq_zero_of_first_marginal_density_eq_zero (f := f) hf hx_zero
    have hratio_zero :
        (fun y : ℝ ↦ f x y / first_marginal_density f x) =ᵐ[(volume : Measure ℝ)] 0 := by
      filter_upwards [hzero_ae] with y hy
      simp [hx_zero, hy]
    have hratio_zero_integral :
        ∫⁻ b in Set.univ, f x b / first_marginal_density f x ∂(volume : Measure ℝ) = 0 := by
      have hplain :
          ∫⁻ b, f x b / first_marginal_density f x ∂(volume : Measure ℝ) = 0 := by
        rw [lintegral_congr_ae hratio_zero]
        simp
      simpa [Measure.restrict_univ] using hplain
    rw [hratio_zero_integral]
    simp
  · by_cases hx_top : first_marginal_density f x = ∞
    · -- Proof comment: division by an infinite marginal density kills the fiber density pointwise.
      rw [Kernel.withDensity_apply' (Kernel.const ℝ (volume : Measure ℝ)) hratio_meas,
        Kernel.const_apply]
      simp [hx_top]
    · -- Proof comment: on a finite nonzero fiber, the normalized density integrates to `1`.
      have hmass :
          first_marginal_density f x *
              Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
                (fun x y ↦ f x y / first_marginal_density f x) x Set.univ
            = first_marginal_density f x := by
        simpa [first_marginal_density] using
          firstMarginal_mul_densityRatioKernel_apply_of_ne_top
            (f := f) hf MeasurableSet.univ (x := x) hx_top
      have hunit :
          Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
              (fun x y ↦ f x y / first_marginal_density f x) x Set.univ
            = 1 := by
        calc
          Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
              (fun x y ↦ f x y / first_marginal_density f x) x Set.univ
            = (first_marginal_density f x)⁻¹ *
                (first_marginal_density f x *
                  Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
                    (fun x y ↦ f x y / first_marginal_density f x) x Set.univ) := by
                symm
                simpa [mul_assoc] using
                  (ENNReal.inv_mul_cancel_left
                    (a := first_marginal_density f x)
                    (b := Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
                      (fun x y ↦ f x y / first_marginal_density f x) x Set.univ)
                    hx_zero hx_top)
          _ = (first_marginal_density f x)⁻¹ * first_marginal_density f x := by rw [hmass]
          _ = 1 := by simpa [hx_zero, hx_top] using
                (ENNReal.inv_mul_cancel hx_zero hx_top)
      simp [hunit]

/-- Helper for Example 8.31: under the joint density hypothesis, the joint density factors
`volume.prod volume`-almost everywhere as the first marginal density times the normalized fiber
density. -/
private theorem jointDensity_eq_firstMarginal_mul_densityRatio_ae
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P) :
    (fun z : ℝ × ℝ ↦ f z.1 z.2) =ᵐ[((volume : Measure ℝ).prod (volume : Measure ℝ))]
      (fun z ↦
        first_marginal_density f z.1 * (f z.1 z.2 / first_marginal_density f z.1)) := by
  have hfm_meas : Measurable (first_marginal_density f) :=
    measurable_first_marginal_density (f := f) hf
  have hratio_meas :
      Measurable (fun z : ℝ × ℝ ↦ f z.1 z.2 / first_marginal_density f z.1) := by
    exact hf.div (hfm_meas.comp measurable_fst)
  have hfactor_meas :
      Measurable (fun z : ℝ × ℝ ↦
        first_marginal_density f z.1 * (f z.1 z.2 / first_marginal_density f z.1)) := by
    exact (hfm_meas.comp measurable_fst).mul hratio_meas
  have hX_law := hasLaw_fst_withDensity_first_marginal (P := P) (X := X) (Y := Y) (f := f)
    hf hXY_law
  have hfm_ne_top : ∫⁻ x, first_marginal_density f x ∂(volume : Measure ℝ) ≠ ∞ := by
    have hfm_univ :
        ((volume : Measure ℝ).withDensity (first_marginal_density f)) Set.univ ≠ ∞ := by
      simpa [hX_law.map_eq] using (measure_ne_top (P.map X) Set.univ)
    simpa [withDensity_apply, Measure.restrict_univ] using hfm_univ
  have hfm_ae_lt_top :
      ∀ᵐ x ∂(volume : Measure ℝ), first_marginal_density f x < ∞ :=
    ae_lt_top hfm_meas hfm_ne_top
  have hfiber_factor :
      ∀ᵐ x ∂(volume : Measure ℝ),
        ∀ᵐ y ∂(volume : Measure ℝ),
          f x y =
            first_marginal_density f x * (f x y / first_marginal_density f x) := by
    filter_upwards [hfm_ae_lt_top] with x hx_top
    by_cases hx_zero : first_marginal_density f x = 0
    · have hzero_ae :=
        fiber_ae_eq_zero_of_first_marginal_density_eq_zero (f := f) hf hx_zero
      filter_upwards [hzero_ae] with y hy
      simp [hx_zero, hy]
    · -- Proof comment: outside the zero-marginal exceptional set, ENNReal cancellation gives the
      -- fiberwise factorization pointwise for every `y`.
      exact Filter.Eventually.of_forall fun y ↦ by
        symm
        exact ENNReal.mul_div_cancel hx_zero hx_top.ne
  -- Proof comment: upgrade the fiberwise a.e. factorization to the product measure.
  change ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
    f z.1 z.2 =
      first_marginal_density f z.1 * (f z.1 z.2 / first_marginal_density f z.1)
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hf hfactor_meas)]
  simpa using hfiber_factor

/-- Helper for Example 8.31: the joint law equals the composition-product of the `X`-marginal and
the raw density-ratio kernel. -/
private theorem jointDensityMap_eq_compProd_densityRatioKernel
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {f : ℝ → ℝ → ℝ≥0∞}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P) :
    P.map (fun ω ↦ (X ω, Y ω)) = P.map X ⊗ₘ
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun x y ↦ f x y / first_marginal_density f x) := by
  let κ : Kernel ℝ ℝ :=
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (fun x y ↦ f x y / first_marginal_density f x)
  have hfm_meas : Measurable (first_marginal_density f) :=
    measurable_first_marginal_density (f := f) hf
  have hratio_meas :
      Measurable (Function.uncurry fun x y ↦ f x y / first_marginal_density f x) := by
    simpa [Function.uncurry] using hf.div (hfm_meas.comp measurable_fst)
  have hκfinite : IsFiniteKernel κ := by
    refine ⟨⟨1, by simp, fun x ↦ ?_⟩⟩
    simpa [κ] using densityRatioKernel_univ_le_one (f := f) hf x
  letI : IsFiniteKernel κ := hκfinite
  have hfactor_ae :=
    jointDensity_eq_firstMarginal_mul_densityRatio_ae
      (P := P) (X := X) (Y := Y) (f := f) hf hXY_law
  have hX_law := hasLaw_fst_withDensity_first_marginal (P := P) (X := X) (Y := Y) (f := f)
    hf hXY_law
  -- Route correction: normalize both sides to the same `withDensity` shape before invoking the
  -- composition-product rewrite lemmas.
  calc
    P.map (fun ω ↦ (X ω, Y ω))
        = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
            fun z : ℝ × ℝ ↦ f z.1 z.2) := by
            rw [hXY_law.map_eq]
    _ = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦
            first_marginal_density f z.1 * (f z.1 z.2 / first_marginal_density f z.1)) := by
          simpa using MeasureTheory.withDensity_congr_ae hfactor_ae
    _ = (((volume : Measure ℝ).withDensity (first_marginal_density f)).prod
          (volume : Measure ℝ)).withDensity
            (fun z : ℝ × ℝ ↦ f z.1 z.2 / first_marginal_density f z.1) := by
          calc
            (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
                fun z : ℝ × ℝ ↦
                  first_marginal_density f z.1 * (f z.1 z.2 / first_marginal_density f z.1))
              = ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
                    fun z : ℝ × ℝ ↦ first_marginal_density f z.1)).withDensity
                  (fun z : ℝ × ℝ ↦ f z.1 z.2 / first_marginal_density f z.1) := by
                    simpa using
                      (MeasureTheory.withDensity_mul
                        ((volume : Measure ℝ).prod (volume : Measure ℝ))
                        (f := fun z : ℝ × ℝ ↦ first_marginal_density f z.1)
                        (g := fun z : ℝ × ℝ ↦ f z.1 z.2 / first_marginal_density f z.1)
                        (by simpa using hfm_meas.comp measurable_fst) hratio_meas)
            _ = (((volume : Measure ℝ).withDensity (first_marginal_density f)).prod
                  (volume : Measure ℝ)).withDensity
                    (fun z : ℝ × ℝ ↦ f z.1 z.2 / first_marginal_density f z.1) := by
                  rw [← MeasureTheory.prod_withDensity_left (μ := (volume : Measure ℝ))
                    (ν := (volume : Measure ℝ)) (f := first_marginal_density f) hfm_meas]
    _ = ((P.map X).prod (volume : Measure ℝ)).withDensity
          (fun z : ℝ × ℝ ↦ f z.1 z.2 / first_marginal_density f z.1) := by
          rw [← hX_law.map_eq]
    _ = P.map X ⊗ₘ κ := by
          rw [← Measure.compProd_const (μ := P.map X) (ν := (volume : Measure ℝ)),
            ← Measure.compProd_withDensity (μ := P.map X) (κ := Kernel.const ℝ (volume : Measure ℝ))
              (f := fun x y ↦ f x y / first_marginal_density f x) hratio_meas]

variable [IsProbabilityMeasure P]

-- Proof sketch: first identify the law of `(X, Y)` with the density measure
-- `((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity (fun z ↦ f z.1 z.2)`. Then apply
-- `condDistrib_ae_eq_of_measure_eq_compProd` to the canonical candidate kernel
-- `Kernel.withDensity (Kernel.const ℝ volume) (fun x y ↦ f x y / first_marginal_density f x)`,
-- using Fubini to show that its composition-product with `P.map X` recovers the joint law. The
-- previous positivity statement identifies the normalizing marginal factor on `P.map X`-almost
-- every `x`.
/-- Example 8.31: if `(X, Y)` has joint Lebesgue density `f`, then the regular conditional
distribution kernel of `Y` given `X` is, for `P.map X`-almost every `x`, the Lebesgue-density
kernel with density `y ↦ f x y / first_marginal_density f x`. -/
theorem condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P) :
    condDistrib Y X P =ᵐ[P.map X]
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun x y ↦ f x y / first_marginal_density f x) := by
  let κ : Kernel ℝ ℝ :=
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (fun x y ↦ f x y / first_marginal_density f x)
  have hκfinite : IsFiniteKernel κ := by
    refine ⟨⟨1, by simp, fun x ↦ ?_⟩⟩
    simpa [κ] using densityRatioKernel_univ_le_one (f := f) hf x
  letI : IsFiniteKernel κ := hκfinite
  have hpair :=
    jointDensityMap_eq_compProd_densityRatioKernel
      (P := P) (X := X) (Y := Y) (f := f) hf hXY_law
  have hY_meas : AEMeasurable Y P := by
    exact measurable_snd.aemeasurable.comp_aemeasurable hXY_law.aemeasurable
  -- Proof comment: once the joint law is written as a composition-product, the a.e. uniqueness
  -- theorem for `condDistrib` identifies the conditional kernel with the density-ratio kernel.
  simpa [κ] using condDistrib_ae_eq_of_measure_eq_compProd X hY_meas hpair

-- Proof sketch: apply the kernel-valued conditional-density statement above and evaluate both
-- sides on `s` using `Kernel.withDensity_apply'`.
/-- For every measurable `s`, the conditional probability of `Y ∈ s` given `X = x` is the
integral of the conditional density over `s`, for `P.map X`-almost every `x`. -/
theorem condDistrib_ae_eq_lintegral_density_ratio_of_jointDensity
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P)
    {s : Set ℝ} (_hs : MeasurableSet s) :
    (fun x ↦ condDistrib Y X P x s) =ᵐ[P.map X]
      fun x ↦ ∫⁻ y in s, f x y / first_marginal_density f x ∂(volume : Measure ℝ) := by
  have hratio_meas :
      Measurable (Function.uncurry fun x y ↦ f x y / first_marginal_density f x) := by
    simpa [Function.uncurry] using
      hf.div ((measurable_first_marginal_density (f := f) hf).comp measurable_fst)
  -- Proof comment: evaluate the kernel identity from the previous theorem on the measurable set
  -- `s`.
  filter_upwards [condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity
    (P := P) (X := X) (Y := Y) (f := f) hf hXY_law] with x hx
  rw [hx, Kernel.withDensity_apply' (Kernel.const ℝ (volume : Measure ℝ)) hratio_meas]
  simp [Kernel.const_apply]

end JointDensity
