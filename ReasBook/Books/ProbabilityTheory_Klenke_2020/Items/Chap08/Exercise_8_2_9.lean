/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Exercise_8_2_8
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Helper for Exercise 8.2.9: swapping the coordinates of a joint Lebesgue density swaps the
ambient density measure as well. -/
private lemma map_swap_withDensity_jointDensity {f : ℝ → ℝ → ENNReal}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2) :
    ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2)).map Prod.swap
      = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ f z.2 z.1) := by
  -- Proof comment: rewrite the pushed-forward measure on measurable sets and move the swap from
  -- the set to the density by `lintegral_map'`. The base product volume is invariant under swap.
  ext s hs
  rw [Measure.map_apply measurable_swap hs, withDensity_apply _ hs]
  have hs_swap : MeasurableSet (Prod.swap ⁻¹' s) := measurable_swap hs
  rw [withDensity_apply _ hs_swap]
  rw [← lintegral_indicator hs_swap, ← lintegral_indicator hs]
  nth_rewrite 2 [← Measure.prod_swap]
  convert
      (lintegral_map' (((hf.comp measurable_swap).indicator hs).aemeasurable)
        measurable_swap.aemeasurable).symm using 1

/-- Helper for Exercise 8.2.9: integrating against the flipped density-ratio kernel gives the
displayed quotient of ordinary Lebesgue integrals once the marginal is finite and positive. -/
private lemma integralCondKernelEqJointDensityRatio
    {f : ℝ → ℝ → ENNReal} (h : ℝ → ℝ)
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2) {y : ℝ}
    (hy_pos : 0 < first_marginal_density (fun y x ↦ f x y) y)
    (hy_top : first_marginal_density (fun y x ↦ f x y) y < ⊤) :
    ∫ x, h x ∂(Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun y x ↦ f x y / first_marginal_density (fun y x ↦ f x y) y) y)
      = (∫ x, h x * (f x y).toReal) / (∫ x, (f x y).toReal) := by
  let d : ℝ≥0∞ := first_marginal_density (fun y x ↦ f x y) y
  have hf_flip : Measurable fun z : ℝ × ℝ ↦ f z.2 z.1 := hf.comp measurable_swap
  have hd_meas : Measurable (fun y : ℝ ↦ first_marginal_density (fun y x ↦ f x y) y) := by
    simpa [first_marginal_density] using
      hf_flip.lintegral_prod_right'
  have hratio_meas :
      Measurable (Function.uncurry fun y x ↦ f x y / first_marginal_density (fun y x ↦ f x y) y) :=
    hf_flip.div (hd_meas.comp measurable_fst)
  have hfiber_meas : Measurable fun x : ℝ ↦ f x y := by
    simpa using hf.comp (measurable_id.prodMk measurable_const)
  have hfiber_lt_top : ∫⁻ x, f x y ∂(volume : Measure ℝ) < ⊤ := by
    simpa [d, first_marginal_density] using hy_top
  have hfiber_ae_lt_top : ∀ᵐ x ∂(volume : Measure ℝ), f x y < ⊤ :=
    ae_lt_top hfiber_meas hfiber_lt_top.ne
  have hd_ne_zero : d ≠ 0 := ne_of_gt hy_pos
  have hd_toReal_ne_zero : d.toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hd_ne_zero, hy_top.ne⟩
  have hratio_ae_lt_top : ∀ᵐ x ∂(volume : Measure ℝ), f x y / d < ⊤ := by
    filter_upwards [hfiber_ae_lt_top] with x hx
    exact ENNReal.div_lt_top hx.ne hd_ne_zero
  have hden :
      (∫ x, (f x y).toReal ∂(volume : Measure ℝ)) = d.toReal := by
    rw [integral_toReal hfiber_meas.aemeasurable hfiber_ae_lt_top]
    simp [d, first_marginal_density]
  have hkernel_integrand :
      (fun x : ℝ ↦ ((f x y / d).toReal) * h x) =
        fun x ↦ (h x * (f x y).toReal) / d.toReal := by
    funext x
    rw [ENNReal.toReal_div, div_eq_mul_inv, div_eq_mul_inv]
    ring
  -- Proof comment: rewrite the kernel value as a `withDensity` measure on `volume`, convert the
  -- density to a real scalar, and then pull out the constant denominator.
  calc
    ∫ x, h x ∂(Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun y x ↦ f x y / first_marginal_density (fun y x ↦ f x y) y) y)
      = ∫ x, ((f x y / d).toReal) * h x ∂(volume : Measure ℝ) := by
          have hratio_fiber_meas :
              Measurable fun x ↦ f x y / first_marginal_density (fun y x ↦ f x y) y :=
            Measurable.of_uncurry_left hratio_meas
          rw [Kernel.withDensity_apply _ hratio_meas, Kernel.const_apply,
            integral_withDensity_eq_integral_toReal_smul hratio_fiber_meas]
          · simp [smul_eq_mul, d]
          · simpa [d] using hratio_ae_lt_top
    _ = ∫ x, (h x * (f x y).toReal) / d.toReal ∂(volume : Measure ℝ) := by
          rw [hkernel_integrand]
    _ = (∫ x, h x * (f x y).toReal ∂(volume : Measure ℝ)) / d.toReal := by
          rw [integral_div]
    _ = (∫ x, h x * (f x y).toReal) / (∫ x, (f x y).toReal) := by
          rw [hden]

/-- Helper for Exercise 8.2.9: a nonpositive exponential rate gives the zero measure. -/
private lemma expMeasureEqZeroOfNonpos {θ : ℝ} (hθ : θ ≤ 0) : expMeasure θ = 0 := by
  -- Proof comment: the exponential density vanishes pointwise when the rate is nonpositive, so
  -- the corresponding `withDensity` measure is zero.
  rw [expMeasure, gammaMeasure]
  have hzero : gammaPDF 1 θ =ᵐ[volume] 0 := by
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · rw [show gammaPDF 1 θ x = exponentialPDF θ x by rfl, exponentialPDF_of_nonneg hx]
      apply ENNReal.ofReal_eq_zero.2
      exact mul_nonpos_of_nonpos_of_nonneg hθ (le_of_lt (Real.exp_pos _))
    · have hx' : x < 0 := by linarith
      simp [show gammaPDF 1 θ x = exponentialPDF θ x by rfl, exponentialPDF_of_neg hx']
  rw [withDensity_congr_ae hzero, withDensity_zero]

/-- Helper for Exercise 8.2.9: an exponential law under a probability measure forces a positive
rate. -/
private lemma ratePosOfHasLawExpLocal {X : Ω → ℝ} {θ : ℝ}
    (hX : HasLaw X (expMeasure θ) P) : 0 < θ := by
  -- Proof comment: rule out `θ ≤ 0` by the previous zero-measure lemma, which would contradict
  -- that `expMeasure θ` is the pushforward of a probability measure.
  by_contra hθ
  have hθ' : θ ≤ 0 := le_of_not_gt hθ
  have hprob : IsProbabilityMeasure (expMeasure θ) := hX.isProbabilityMeasure_iff.mp inferInstance
  letI : IsProbabilityMeasure (expMeasure θ) := hprob
  have huniv : expMeasure θ Set.univ = 1 := by simp
  rw [expMeasureEqZeroOfNonpos hθ'] at huniv
  simp at huniv

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 8.2.9: an exponential random variable is almost surely nonnegative. -/
private lemma aeNonnegOfHasLawExpLocal {X : Ω → ℝ} {θ : ℝ}
    (hX : HasLaw X (expMeasure θ) P) :
    ∀ᵐ ω ∂P, 0 ≤ X ω := by
  have hIio : expMeasure θ (Set.Iio 0) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    rw [show gammaPDF 1 θ = exponentialPDF θ by funext x; rfl]
    exact lintegral_exponentialPDF_of_nonpos (x := 0) le_rfl
  have hAe : ∀ᵐ x ∂expMeasure θ, 0 ≤ x := by
    rw [ae_iff]
    simpa [not_le] using hIio
  -- Proof comment: the exponential density vanishes on `(-∞, 0)`, and `HasLaw.ae_iff` pulls
  -- that support statement back along `X`.
  exact (hX.ae_iff (p := fun x : ℝ ↦ 0 ≤ x) (by fun_prop)).2 hAe

-- Proof sketch: identify the conditional expectation of `h ∘ X` given `Y` with the integral of
-- `h` against the regular conditional distribution of `X` given `Y`, then use the joint-density
-- hypothesis to compute that conditional distribution by disintegrating the joint law of `(X, Y)`
-- along the second coordinate and normalizing by the marginal density of `Y`.
/-- Exercise 8.2.9 (1): If `X` and `Y` have joint Lebesgue density `f` and `h(X)` is
integrable, then the conditional expectation of `h(X)` given `Y` is almost surely the ratio of the
`x`-integral of `h(x) f(x, Y)` and the `x`-integral of `f(x, Y)`. -/
theorem condExp_transform_given_right_ae_eq_joint_density_ratio
    {X Y : Ω → ℝ} {f : ℝ → ℝ → ENNReal} {h : ℝ → ℝ}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (h_joint : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P)
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hh_meas : Measurable h) (hh_int : Integrable (fun ω ↦ h (X ω)) P) :
    P[h ∘ X | MeasurableSpace.comap Y (borel ℝ)] =ᵐ[P]
      fun ω ↦
        (∫ x, h x * (f x (Y ω)).toReal) /
          (∫ x, (f x (Y ω)).toReal) := by
  let g : ℝ → ℝ → ENNReal := fun y x ↦ f x y
  have hg_meas : Measurable fun z : ℝ × ℝ ↦ g z.1 z.2 := by
    simpa [g, Function.uncurry] using hf.comp measurable_swap
  have hswap_joint :
      HasLaw (fun ω ↦ (Y ω, X ω))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ g z.1 z.2) P := by
    have hswap_law :
        HasLaw Prod.swap
          (Measure.map Prod.swap
            ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
              fun z : ℝ × ℝ ↦ f z.1 z.2)))
          ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
            fun z : ℝ × ℝ ↦ f z.1 z.2)) := by
      exact ⟨measurable_swap.aemeasurable, rfl⟩
    -- Proof comment: swap the coordinates in the given joint law and rewrite the pushed-forward
    -- density using the swap transport lemma.
    simpa [g, Function.comp, map_swap_withDensity_jointDensity hf] using
      hswap_law.comp h_joint
  have hcondKernel :
      condDistrib X Y P =ᵐ[P.map Y]
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun y x ↦ g y x / first_marginal_density g y) := by
    simpa [g] using
      (condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity
        (P := P) (X := Y) (Y := X) (f := g) hg_meas hswap_joint)
  have hpos :
      ∀ᵐ y ∂P.map Y, 0 < first_marginal_density g y := by
    simpa [g] using
      (first_marginal_density_pos_ae_of_hasLaw_prod_withDensity
        (P := P) (X := Y) (Y := X) (f := g) hg_meas hswap_joint)
  have hg_marginal_meas : Measurable (first_marginal_density g) := by
    simpa [first_marginal_density] using hg_meas.lintegral_prod_right'
  have hY_law :=
    hasLaw_fst_withDensity_first_marginal (P := P) (X := Y) (Y := X) (f := g)
      hg_meas hswap_joint
  have hfinite_ne_top : ∫⁻ y, first_marginal_density g y ∂(volume : Measure ℝ) ≠ ∞ := by
    have hfinite_univ :
        ((volume : Measure ℝ).withDensity (first_marginal_density g)) Set.univ ≠ ∞ := by
      simpa [hY_law.map_eq] using measure_ne_top (P.map Y) Set.univ
    simpa [withDensity_apply, Measure.restrict_univ] using hfinite_univ
  have hfinite_volume :
      ∀ᵐ y ∂(volume : Measure ℝ), first_marginal_density g y < ∞ :=
    ae_lt_top hg_marginal_meas hfinite_ne_top
  have hfinite :
      ∀ᵐ y ∂P.map Y, first_marginal_density g y < ∞ := by
    rw [hY_law.map_eq, ae_withDensity_iff hg_marginal_meas]
    filter_upwards [hfinite_volume] with y hy _
    exact hy
  have hcondInt :
      P[h ∘ X | MeasurableSpace.comap Y (borel ℝ)] =ᵐ[P]
        fun ω ↦ ∫ x, h x ∂condDistrib X Y P (Y ω) := by
    -- Proof comment: rewrite the conditional expectation as an integral against the regular
    -- conditional law of `X` given `Y`.
    simpa using
      (condExp_ae_eq_integral_condDistrib
        (μ := P) (X := Y) (Y := X) hY_meas hX_meas.aemeasurable
        hh_meas.stronglyMeasurable hh_int)
  have hkernel_comp :
      (fun ω ↦ condDistrib X Y P (Y ω)) =ᵐ[P]
        fun ω ↦
          Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
            (fun y x ↦ g y x / first_marginal_density g y) (Y ω) :=
    ae_eq_comp hY_meas.aemeasurable hcondKernel
  have hpos_comp :
      ∀ᵐ ω ∂P, 0 < first_marginal_density g (Y ω) :=
    ae_of_ae_map hY_meas.aemeasurable hpos
  have hfinite_comp :
      ∀ᵐ ω ∂P, first_marginal_density g (Y ω) < ∞ :=
    ae_of_ae_map hY_meas.aemeasurable hfinite
  filter_upwards [hcondInt, hkernel_comp, hpos_comp, hfinite_comp] with ω hω hκ hposω hfiniteω
  rw [hω, hκ]
  simpa [g] using
    integralCondKernelEqJointDensityRatio (f := f) (h := h) hf
      (y := Y ω) hposω hfiniteω

/-- Helper for Exercise 8.2.9: the exponential law is `volume.withDensity (exponentialPDF θ)`. -/
private lemma expMeasure_eq_withDensity_exponentialPDF (θ : ℝ) :
    expMeasure θ = (volume : Measure ℝ).withDensity (exponentialPDF θ) := by
  rfl

/-- Helper for Exercise 8.2.9: pushing a product `withDensity` measure through the shear
`(x, y) ↦ (x + y, x)` rewrites the density by the inverse map `(s, x) ↦ (x, s - x)`. -/
private lemma map_sumLeft_withDensity (f : ℝ → ℝ → ENNReal) :
    Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1))
      ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2))
      = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ f z.2 (z.1 - z.2)) := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let e : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.shearAddRight ℝ).trans MeasurableEquiv.prodComm
  have hshear : MeasurePreserving (MeasurableEquiv.shearAddRight ℝ) μ μ := by
    simpa [μ] using
      (measurePreserving_prod_add (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hswap : MeasurePreserving Prod.swap μ μ := by
    refine ⟨measurable_swap, ?_⟩
    simpa [μ] using (Measure.prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hpres : MeasurePreserving e μ μ := by
    simpa [e] using hswap.comp hshear
  ext s hs
  rw [show Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1))
      (μ.withDensity fun z : ℝ × ℝ ↦ f z.1 z.2) s
        = Measure.map e (μ.withDensity fun z : ℝ × ℝ ↦ f z.1 z.2) s by
      rfl]
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  -- Proof comment: rewrite the restricted integral on `e ⁻¹' s` as an unrestricted integral of
  -- an indicator, transport it across the measurable equivalence, then identify the inverse map.
  calc
    ∫⁻ z in e ⁻¹' s, f z.1 z.2 ∂μ
      = ∫⁻ z, Set.indicator (e ⁻¹' s) (fun z : ℝ × ℝ ↦ f z.1 z.2) z ∂μ := by
          rw [lintegral_indicator (e.measurable hs)]
    _ = ∫⁻ z, Set.indicator s (fun z : ℝ × ℝ ↦ f z.2 (z.1 - z.2)) (e z) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards with z
          have hsub : z.1 + z.2 - z.1 = z.2 := by ring
          by_cases hz : z ∈ e ⁻¹' s
          · have hz' : e z ∈ s := hz
            rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
            have hsnd : (e z).2 = z.1 := by
              rfl
            have hfstsub : (e z).1 - (e z).2 = z.2 := by
              change z.1 + z.2 - z.1 = z.2
              exact hsub
            have hfstsub' : (e z).1 - z.1 = z.2 := by
              simpa [hsnd] using hfstsub
            rw [hsnd, hfstsub']
          · have hz' : e z ∉ s := hz
            rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
    _ = ∫⁻ z, Set.indicator s (fun z : ℝ × ℝ ↦ f z.2 (z.1 - z.2)) z ∂Measure.map e μ := by
          symm
          simpa using
            (lintegral_map_equiv (μ := μ)
              (f := Set.indicator s (fun z : ℝ × ℝ ↦ f z.2 (z.1 - z.2))) e)
    _ = ∫⁻ z, Set.indicator s (fun z : ℝ × ℝ ↦ f z.2 (z.1 - z.2)) z ∂μ := by
          rw [hpres.map_eq]
    _ = ∫⁻ z in s, f z.2 (z.1 - z.2) ∂μ := by
          rw [lintegral_indicator hs]

/-- Helper for Exercise 8.2.9: the wedge density obtained from the shear image of the exponential
product law. -/
private noncomputable def wedgeDensity (θ : ℝ) (s x : ℝ) : ℝ≥0∞ :=
  Set.indicator (Set.Icc 0 s)
    (fun _ : ℝ ↦ ENNReal.ofReal (θ ^ 2 * Real.exp (-(θ * s)))) x

/-- Helper for Exercise 8.2.9: the wedge density is measurable on `ℝ × ℝ`. -/
private lemma measurable_wedgeDensity (θ : ℝ) :
    Measurable fun z : ℝ × ℝ ↦ wedgeDensity θ z.1 z.2 := by
  let A : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1}
  have hA : MeasurableSet A := by
    change MeasurableSet {z : ℝ × ℝ | 0 ≤ z.2 ∧ z.2 ≤ z.1}
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hconst : Measurable fun z : ℝ × ℝ ↦
      ENNReal.ofReal (θ ^ 2 * Real.exp (-(θ * z.1))) := by
    have : Measurable fun z : ℝ × ℝ ↦ θ ^ 2 * Real.exp (-(θ * z.1)) := by
      fun_prop
    exact this.ennreal_ofReal
  simpa [A, wedgeDensity, Set.indicator] using hconst.piecewise hA measurable_const

/-- Helper for Exercise 8.2.9: independence and identical exponential marginals give the product
law of `(X, Y)`. -/
private lemma indepExpPairHasLawProd {X Y : Ω → ℝ} {θ : ℝ}
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P)
    (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (fun ω ↦ (X ω, Y ω)) ((expMeasure θ).prod (expMeasure θ)) P := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure
    (ratePosOfHasLawExpLocal hX)
  -- Proof comment: independence is equivalent to the product pushforward formula for the pair map.
  refine ⟨hX.aemeasurable.prodMk hY.aemeasurable, ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hXY,
    hX.map_eq, hY.map_eq]

/-- Helper for Exercise 8.2.9: after the shear `(x, y) ↦ (x + y, x)`, the exponential product
density becomes the wedge density on `{(s, x) | 0 ≤ x ≤ s}`. -/
private lemma expProdDensity_after_sumLeft_eq_wedgeDensity {θ : ℝ} (hθ : 0 < θ) :
    (fun z : ℝ × ℝ ↦ exponentialPDF θ z.2 * exponentialPDF θ (z.1 - z.2))
      = fun z ↦ wedgeDensity θ z.1 z.2 := by
  funext z
  by_cases hz : z.2 ∈ Set.Icc (0 : ℝ) z.1
  · rcases hz with ⟨hz0, hz1⟩
    have hzsub : 0 ≤ z.1 - z.2 := sub_nonneg.mpr hz1
    have hnonneg : 0 ≤ θ * Real.exp (-(θ * z.2)) :=
      mul_nonneg hθ.le (le_of_lt (Real.exp_pos _))
    have hmem : z.2 ∈ Set.Icc 0 z.1 := ⟨hz0, hz1⟩
    rw [wedgeDensity, Set.indicator_of_mem hmem,
      exponentialPDF_of_nonneg hz0, exponentialPDF_of_nonneg hzsub, ← ENNReal.ofReal_mul hnonneg]
    congr 1
    calc
      (θ * Real.exp (-(θ * z.2))) * (θ * Real.exp (-(θ * (z.1 - z.2))))
          = θ ^ 2 * (Real.exp (-(θ * z.2)) * Real.exp (-(θ * (z.1 - z.2)))) := by
              ring
      _ = θ ^ 2 * Real.exp (-(θ * z.1)) := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
  · rw [wedgeDensity, Set.indicator_of_notMem hz]
    by_cases hz0 : 0 ≤ z.2
    · have hzsub : z.1 - z.2 < 0 := by
        have hnot : ¬ z.2 ≤ z.1 := by
          intro hz1
          exact hz ⟨hz0, hz1⟩
        linarith
      rw [exponentialPDF_of_nonneg hz0, exponentialPDF_of_neg hzsub]
      simp
    · have hzneg : z.2 < 0 := by linarith
      rw [exponentialPDF_of_neg hzneg]
      simp

/-- Helper for Exercise 8.2.9: the shear image of the exponential product law has the wedge
density with respect to `volume.prod volume`. -/
private lemma shearMapExpProd_eq_withDensityWedge {θ : ℝ} (hθ : 0 < θ) :
    Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1)) ((expMeasure θ).prod (expMeasure θ))
      = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ wedgeDensity θ z.1 z.2) := by
  have hexp_meas : Measurable (exponentialPDF θ) := by
    simpa [exponentialPDF] using (measurable_exponentialPDFReal θ).ennreal_ofReal
  have hpair_meas :
      Measurable fun z : ℝ × ℝ ↦ exponentialPDF θ z.1 * exponentialPDF θ z.2 :=
    (hexp_meas.comp measurable_fst).mul (hexp_meas.comp measurable_snd)
  calc
    Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1)) ((expMeasure θ).prod (expMeasure θ))
      = Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1))
          ((((volume : Measure ℝ).withDensity (exponentialPDF θ)).prod
            ((volume : Measure ℝ).withDensity (exponentialPDF θ)))) := by
              rfl
    _ = Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1))
          ((((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
            fun z : ℝ × ℝ ↦ exponentialPDF θ z.1 * exponentialPDF θ z.2)) := by
              rw [MeasureTheory.prod_withDensity hexp_meas hexp_meas]
    _ = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ exponentialPDF θ z.2 * exponentialPDF θ (z.1 - z.2)) := by
            simpa using
              map_sumLeft_withDensity (fun x y ↦ exponentialPDF θ x * exponentialPDF θ y)
    _ = (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ wedgeDensity θ z.1 z.2) := by
            congr 1
            exact expProdDensity_after_sumLeft_eq_wedgeDensity hθ

/-- Helper for Exercise 8.2.9: the first marginal of the wedge density is the Gamma(2)-type
density `s ↦ θ² s exp (-(θ s))` on `(0, ∞)`. -/
private lemma firstMarginalWedgeDensity_of_pos {θ s : ℝ} (hs : 0 < s) :
    first_marginal_density (wedgeDensity θ) s
      = ENNReal.ofReal (θ ^ 2 * Real.exp (-(θ * s)) * s) := by
  rw [first_marginal_density]
  -- Proof comment: on the positive fiber, the wedge density is a constant on `Icc 0 s`.
  simp [wedgeDensity, lintegral_indicator, Real.volume_Icc, hs.le, mul_comm]

/-- Helper for Exercise 8.2.9: on a positive fiber, the wedge density normalized by its first
marginal is the constant density `1 / s` on `Icc 0 s`. -/
private lemma wedgeDensityRatio_eq_indicator_of_pos {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    (fun x : ℝ ↦ wedgeDensity θ s x / first_marginal_density (wedgeDensity θ) s)
      = Set.indicator (Set.Icc 0 s) (fun _ : ℝ ↦ ENNReal.ofReal (1 / s)) := by
  have hfm : first_marginal_density (wedgeDensity θ) s
      = ENNReal.ofReal (θ ^ 2 * Real.exp (-(θ * s)) * s) :=
    firstMarginalWedgeDensity_of_pos hs
  have hconst_pos : 0 < θ ^ 2 * Real.exp (-(θ * s)) := by
    exact mul_pos (sq_pos_of_pos hθ) (Real.exp_pos _)
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) s
  · rw [wedgeDensity, Set.indicator_of_mem hx, hfm, Set.indicator_of_mem hx]
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hconst_pos hs)]
    congr 1
    field_simp [hconst_pos.ne', hs.ne']
  · simp [wedgeDensity, hfm, hx]

/-- Helper for Exercise 8.2.9: for `s > 0`, the density-ratio kernel of the wedge density is the
conditioned Lebesgue measure on `Set.Icc 0 s`. -/
private lemma wedgeKernel_eq_uniformIccZero_of_pos {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
      (fun s x ↦ wedgeDensity θ s x / first_marginal_density (wedgeDensity θ) s) s
      = volume[|Set.Icc 0 s] := by
  have hw_meas : Measurable fun z : ℝ × ℝ ↦ wedgeDensity θ z.1 z.2 :=
    measurable_wedgeDensity θ
  have hfm_meas : Measurable (fun s : ℝ ↦ first_marginal_density (wedgeDensity θ) s) := by
    simpa [first_marginal_density] using
      hw_meas.lintegral_prod_right'
  have hratio_meas :
      Measurable (Function.uncurry
        fun s x ↦ wedgeDensity θ s x / first_marginal_density (wedgeDensity θ) s) :=
    hw_meas.div (hfm_meas.comp measurable_fst)
  ext t ht
  rw [Kernel.withDensity_apply' (Kernel.const ℝ (volume : Measure ℝ)) hratio_meas,
    Kernel.const_apply, wedgeDensityRatio_eq_indicator_of_pos hθ hs,
    lintegral_indicator measurableSet_Icc]
  rw [ProbabilityTheory.cond_apply' ht (volume : Measure ℝ), Real.volume_Icc]
  simp [ENNReal.ofReal_inv_of_pos hs, Set.inter_comm]

/-- Helper for Exercise 8.2.9: a variable with exponential law is almost surely strictly
positive. -/
private lemma aePosOfHasLawExp {X : Ω → ℝ} {θ : ℝ} (hX : HasLaw X (expMeasure θ) P) :
    ∀ᵐ ω ∂P, 0 < X ω := by
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ X ω := aeNonnegOfHasLawExpLocal hX
  have hsingleton : expMeasure θ ({0} : Set ℝ) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  have hne_zero_exp : ∀ᵐ x ∂expMeasure θ, x ≠ 0 := by
    rw [ae_iff]
    simpa using hsingleton
  have hne_zero : ∀ᵐ ω ∂P, X ω ≠ 0 := by
    have hp : Measurable fun x : ℝ ↦ x ≠ 0 := by fun_prop
    exact (hX.ae_iff (p := fun x : ℝ ↦ x ≠ 0) hp).2 hne_zero_exp
  -- Proof comment: nonnegativity plus almost-sure avoidance of the singleton `{0}` gives strict
  -- positivity.
  filter_upwards [hnonneg, hne_zero] with ω hω_nonneg hω_ne
  exact lt_of_le_of_ne hω_nonneg (Ne.symm hω_ne)

/-- Helper for Exercise 8.2.9: the mean of the conditioned Lebesgue measure on `Set.Icc 0 s` is
`s / 2`. -/
private lemma integralId_uniformIccZero {s : ℝ} (hs : 0 ≤ s) :
    ∫ t, t ∂(volume[|Set.Icc 0 s] : Measure ℝ) = s / 2 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [ProbabilityTheory.cond]
  have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  rw [ProbabilityTheory.cond, MeasureTheory.integral_smul_measure]
  -- Proof comment: after unfolding the conditioned measure, only the interval integral of `id`
  -- over `[0, s]` remains.
  rw [show (∫ t, t ∂(volume.restrict (Set.Icc 0 s) : Measure ℝ)) =
      ∫ t in Set.Icc 0 s, t ∂(volume : Measure ℝ) by
    rfl]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs, integral_id,
    Real.volume_Icc]
  have hsub : s - 0 = s := by ring
  rw [hsub]
  have hinv : ((ENNReal.ofReal s)⁻¹).toReal = 1 / s := by
    simp [ENNReal.toReal_inv, hs]
  rw [hinv, smul_eq_mul]
  field_simp [hs'.ne']
  ring

/-- Helper for Exercise 8.2.9: on a positive interval `Set.Icc 0 s`, the conditioned Lebesgue
measure of `Set.Iic x` is `1` for `s ≤ x` and `x / s` otherwise. -/
private lemma uniformIccZero_real_Iic_of_pos {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    ((volume[|Set.Icc 0 s] : Measure ℝ).real (Set.Iic x)) = if s ≤ x then 1 else x / s := by
  by_cases hsx : s ≤ x
  · have hinter : Set.Icc (0 : ℝ) s ∩ Set.Iic x = Set.Icc 0 s := by
      ext y
      constructor
      · intro hy
        exact hy.1
      · intro hy
        exact ⟨hy, le_trans hy.2 hsx⟩
    -- Proof comment: when `x` lies to the right of the interval endpoint, the whole interval is
    -- counted and the conditioned mass is `1`.
    have hmass : (volume[|Set.Icc 0 s] : Measure ℝ) (Set.Iic x) = 1 := by
      rw [ProbabilityTheory.cond_apply' measurableSet_Iic (volume : Measure ℝ), hinter,
        Real.volume_Icc, sub_zero]
      exact ENNReal.inv_mul_cancel (by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact hs) (by simp)
    simpa [measureReal_def, hsx] using congrArg ENNReal.toReal hmass
  · have hsx_lt : x < s := by linarith
    have hinter : Set.Icc (0 : ℝ) s ∩ Set.Iic x = Set.Icc 0 x := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1.1, hy.2⟩
      · intro hy
        exact ⟨⟨hy.1, le_trans hy.2 hsx_lt.le⟩, hy.2⟩
    -- Proof comment: when `x < s`, the event truncates the interval to `[0, x]`, so the
    -- conditioned mass is the length ratio `x / s`.
    have hmass :
        (volume[|Set.Icc 0 s] : Measure ℝ) (Set.Iic x) = ENNReal.ofReal (x / s) := by
      rw [ProbabilityTheory.cond_apply' measurableSet_Iic (volume : Measure ℝ), hinter,
        Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero, mul_comm]
      rw [← ENNReal.ofReal_inv_of_pos hs, ← ENNReal.ofReal_mul hx, div_eq_mul_inv]
    simpa [measureReal_def, hsx, ENNReal.toReal_ofReal (div_nonneg hx hs.le)] using
      congrArg ENNReal.toReal hmass

section IidExp

variable {X Y : Ω → ℝ} {θ : ℝ}

local notation "mSum" => MeasurableSpace.comap (X + Y) (borel ℝ)

-- Proof sketch: compute the conditional law of `X` given `X + Y = s` from the joint exponential
-- density in the setting of Exercise 8.2.9 (2). It is the conditioned Lebesgue measure on
-- `[0, s]`.
private theorem condDistrib_left_given_sum_of_iid_exp_ae_eq_uniform_interval_aux
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P)
    (hX_meas : Measurable X) (hY_meas : Measurable Y) (hXY : X ⟂ᵢ[P] Y) :
    ∀ᵐ s ∂P.map (X + Y), condDistrib X (X + Y) P s = volume[|Set.Icc 0 s] := by
  have hθ : 0 < θ := ratePosOfHasLawExpLocal hX
  have hpair_law :
      HasLaw (fun ω ↦ (X ω, Y ω)) ((expMeasure θ).prod (expMeasure θ)) P :=
    indepExpPairHasLawProd hX hY hXY
  have hsum_left_law :
      HasLaw (fun ω ↦ (X ω + Y ω, X ω))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          fun z : ℝ × ℝ ↦ wedgeDensity θ z.1 z.2) P := by
    have hshear_law :
        HasLaw (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1))
          (Measure.map (fun z : ℝ × ℝ ↦ (z.1 + z.2, z.1))
            ((expMeasure θ).prod (expMeasure θ)))
          ((expMeasure θ).prod (expMeasure θ)) := by
      exact ⟨((measurable_fst.add measurable_snd).prodMk measurable_fst).aemeasurable, rfl⟩
    -- Proof comment: transport the product exponential law through the shear `(x, y) ↦ (x + y, x)`.
    simpa [Function.comp, shearMapExpProd_eq_withDensityWedge hθ] using
      hshear_law.comp hpair_law
  have hcondKernel :
      condDistrib X (X + Y) P =ᵐ[P.map (X + Y)]
        Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun s x ↦ wedgeDensity θ s x / first_marginal_density (wedgeDensity θ) s) := by
    simpa using
      (condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity
        (P := P) (X := X + Y) (Y := X) (f := wedgeDensity θ)
        (measurable_wedgeDensity θ) hsum_left_law)
  have hsum_pos :
      ∀ᵐ s ∂P.map (X + Y), 0 < s := by
    exact
      (MeasureTheory.ae_map_iff (μ := P) (f := fun ω ↦ X ω + Y ω)
        (hf := (hX_meas.add hY_meas).aemeasurable)
        (hp := measurableSet_Ioi)).2 <|
        by
          filter_upwards [aePosOfHasLawExp hX, aePosOfHasLawExp hY] with ω hωX hωY
          simpa [Set.mem_Ioi] using add_pos hωX hωY
  filter_upwards [hcondKernel, hsum_pos] with s hs_kernel hs_pos
  rw [hs_kernel]
  simpa using wedgeKernel_eq_uniformIccZero_of_pos hθ hs_pos

-- Proof sketch: the pair `(X, Y)` is exchangeable because `X` and `Y` are independent with the
-- same exponential law. Hence the conditional expectations of `X` and `Y` given `X + Y` agree
-- almost surely. Summing them and using that `X + Y` is measurable with respect to its own
-- generated σ-algebra yields `2 * E[X | X + Y] = X + Y`.
/-- Exercise 8.2.9 (2): If `X` and `Y` are independent
and both have exponential law with common rate `θ`, then the conditional expectation of `X` given
`X + Y` is almost surely half of the sum. -/
theorem condExp_left_given_sum_of_iid_exp_ae_eq_half_sum
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P)
    (hX_meas : Measurable X) (hY_meas : Measurable Y) (hXY : X ⟂ᵢ[P] Y) :
    P[X | mSum] =ᵐ[P] (X + Y) / 2 := by
  have hkernel :
      (fun ω ↦ condDistrib X (X + Y) P (X ω + Y ω)) =ᵐ[P]
        fun ω ↦ volume[|Set.Icc 0 (X ω + Y ω)] := by
    exact ae_eq_comp (hX_meas.add hY_meas).aemeasurable
      (condDistrib_left_given_sum_of_iid_exp_ae_eq_uniform_interval_aux hX hY hX_meas hY_meas hXY)
  have hsum_nonneg : ∀ᵐ ω ∂P, 0 ≤ X ω + Y ω := by
    filter_upwards [aeNonnegOfHasLawExpLocal hX, aeNonnegOfHasLawExpLocal hY] with ω hωX hωY
    linarith
  have hcondInt :
      P[X | mSum] =ᵐ[P] fun ω ↦ ∫ x, x ∂condDistrib X (X + Y) P (X ω + Y ω) := by
    -- Proof comment: rewrite the conditional expectation as the integral of `id` against the
    -- conditional distribution of `X` given `X + Y`.
    simpa using
      (condExp_ae_eq_integral_condDistrib
        (hX_meas.add hY_meas) hX_meas.aemeasurable stronglyMeasurable_id
        (integrableOfHasLawExp hX))
  filter_upwards [hcondInt, hkernel, hsum_nonneg] with ω hω hκ hnonneg
  rw [hω, hκ]
  simpa using integralId_uniformIccZero hnonneg

-- Proof sketch: evaluate the auxiliary conditional-distribution formula on the event `(-∞, x]`. The
-- conditioned Lebesgue measure on `[0, s]` gives mass `1` when `s ≤ x` and `x / s` when `s > x`.
/-- Companion to Exercise 8.2.9 (2): if `X` and `Y` are independent and both have exponential law
with common rate `θ`, then for every `x ≥ 0` the conditional probability of the event `X ≤ x`
given `X + Y` is almost surely the truncated-uniform cdf on the random interval `[0, X + Y]`. -/
theorem condProb_left_le_given_sum_of_iid_exp_ae_eq {x : ℝ} (hx : 0 ≤ x)
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P)
    (hX_meas : Measurable X) (hY_meas : Measurable Y) (hXY : X ⟂ᵢ[P] Y) :
    P⟦X ⁻¹' Set.Iic x | mSum⟧ =ᵐ[P]
      fun ω ↦ if X ω + Y ω ≤ x then 1 else x / (X ω + Y ω) := by
  have hkernel :
      (fun ω ↦ condDistrib X (X + Y) P (X ω + Y ω)) =ᵐ[P]
        fun ω ↦ volume[|Set.Icc 0 (X ω + Y ω)] := by
    exact ae_eq_comp (hX_meas.add hY_meas).aemeasurable
      (condDistrib_left_given_sum_of_iid_exp_ae_eq_uniform_interval_aux hX hY hX_meas hY_meas hXY)
  have hsum_pos : ∀ᵐ ω ∂P, 0 < X ω + Y ω := by
    filter_upwards [aePosOfHasLawExp hX, aePosOfHasLawExp hY] with ω hωX hωY
    linarith
  have hcondProb :
      P⟦X ⁻¹' Set.Iic x | mSum⟧ =ᵐ[P]
        fun ω ↦ (condDistrib X (X + Y) P (X ω + Y ω)).real (Set.Iic x) := by
    simpa using
      (condDistrib_ae_eq_condExp
        (hX_meas.add hY_meas) hX_meas measurableSet_Iic).symm
  filter_upwards [hcondProb, hkernel, hsum_pos] with ω hω hκ hpos
  rw [hω, hκ]
  simpa using uniformIccZero_real_Iic_of_pos hx hpos

end IidExp
