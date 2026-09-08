module

public import ReasLib.Analysis.Calculus.SmoothCutoff
public import ReasLib.Analysis.Calculus.ContDiff.AffineBounds
public import ReasLib.Analysis.Calculus.ContDiff.ProductRule

public section

open Set
open scoped ContDiff

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineBump

/-- A scaled linear bump multiplies a cutoff by the linear functional
`z ↦ inner ℝ a (z - x)` after translating and rescaling its argument. -/
def scaledLinearBump (χ : E → ℝ) (x : E) (ρ : ℝ) (a : E) : E → ℝ :=
  fun z ↦ χ (ρ⁻¹ • (z - x)) * inner ℝ a (z - x)

/-- Evaluation of a scaled linear bump. -/
@[simp]
theorem scaledLinearBump_apply (χ : E → ℝ) (x : E) (ρ : ℝ) (a z : E) :
    scaledLinearBump χ x ρ a z = χ (ρ⁻¹ • (z - x)) * inner ℝ a (z - x) := by
  rw [scaledLinearBump]

/-- A smooth cutoff produces a smooth scaled linear bump at every center, scale, and
linear coefficient. -/
theorem contDiff_scaledLinearBump (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (x : E) (ρ : ℝ) (a : E) :
    ContDiff ℝ ∞ (scaledLinearBump χ x ρ a) := by
  have htranslate : ContDiff ℝ ∞ (fun z : E ↦ z - x) :=
    contDiff_id.sub contDiff_const
  have hscaled : ContDiff ℝ ∞ (fun z : E ↦ ρ⁻¹ • (z - x)) := by
    exact (htranslate.const_smul ρ⁻¹)
  have hcutoff : ContDiff ℝ ∞ (fun z : E ↦ χ (ρ⁻¹ • (z - x))) :=
    hχ.comp hscaled
  have hlinear : ContDiff ℝ ∞ (fun z : E ↦ inner ℝ a (z - x)) := by
    convert (innerSL ℝ a).contDiff.comp htranslate using 1
    ext z
    simp
  have hproduct : ContDiff ℝ ∞
      (fun z : E ↦ χ (ρ⁻¹ • (z - x)) • inner ℝ a (z - x)) :=
    hcutoff.smul hlinear
  change ContDiff ℝ ∞
    (fun z : E ↦ χ (ρ⁻¹ • (z - x)) * inner ℝ a (z - x))
  simpa only [smul_eq_mul] using hproduct

/-- If the cutoff is supported in the open unit ball, a positive-scale scaled linear bump
has topological support inside the corresponding closed ball. -/
theorem tsupport_scaledLinearBump_subset_closedBall (χ : E → ℝ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1) (x : E) (ρ : ℝ) (a : E)
    (hρ : 0 < ρ) :
    tsupport (scaledLinearBump χ x ρ a) ⊆ Metric.closedBall x ρ := by
  intro z hz
  have htranslate : Continuous (fun w : E ↦ w - x) := continuous_id.sub continuous_const
  have hscaled : Continuous (fun w : E ↦ ρ⁻¹ • (w - x)) :=
    continuous_const.smul htranslate
  have hcutoff_support :
      tsupport (fun w : E ↦ χ (ρ⁻¹ • (w - x))) ⊆
        (fun w : E ↦ ρ⁻¹ • (w - x)) ⁻¹' tsupport χ := by
    exact tsupport_comp_subset_preimage χ hscaled
  have hmul :
      tsupport (fun w : E ↦
        χ (ρ⁻¹ • (w - x)) * inner ℝ a (w - x)) ⊆
        tsupport (fun w : E ↦ χ (ρ⁻¹ • (w - x))) := tsupport_mul_subset_left
  have hzprod : z ∈ tsupport (fun w : E ↦
      χ (ρ⁻¹ • (w - x)) * inner ℝ a (w - x)) := by
    change z ∈ tsupport (fun w : E ↦
      χ (ρ⁻¹ • (w - x)) * inner ℝ a (w - x)) at hz
    exact hz
  have hzcutoff : z ∈ tsupport (fun w : E ↦ χ (ρ⁻¹ • (w - x))) := hmul hzprod
  have hzχ : ρ⁻¹ • (z - x) ∈ tsupport χ := hcutoff_support hzcutoff
  have hzχball : ρ⁻¹ • (z - x) ∈ Metric.ball (0 : E) 1 := hχ_support hzχ
  have hnorm : ‖ρ⁻¹ • (z - x)‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hzχball
  have hρnorm : ‖ρ⁻¹‖ * ‖z - x‖ < 1 := by
    simpa [norm_smul] using hnorm
  have hρinv : ‖ρ⁻¹‖ = ρ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  have hdist : ‖z - x‖ < ρ := by
    rw [hρinv] at hρnorm
    have hprod : ρ⁻¹ * ‖z - x‖ < ρ⁻¹ * ρ := by
      simpa [hρ.ne'] using hρnorm
    exact lt_of_mul_lt_mul_left hprod (le_of_lt (inv_pos.mpr hρ))
  simpa [Metric.mem_closedBall, dist_eq_norm] using (le_of_lt hdist)

/-- The scaled linear bump vanishes at its center. -/
theorem scaledLinearBump_apply_center (χ : E → ℝ) (x : E) (ρ : ℝ) (a : E) :
    scaledLinearBump χ x ρ a x = 0 := by
  simp [scaledLinearBump]

/-- The first Fréchet derivative of a scaled linear bump splits into the cutoff term and
the derivative of the rescaled cutoff. -/
theorem fderiv_scaledLinearBump (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (x : E) (ρ : ℝ) (a z : E) (_hρ : 0 < ρ) :
    fderiv ℝ (scaledLinearBump χ x ρ a) z =
      χ (ρ⁻¹ • (z - x)) • innerSL ℝ a +
        (ρ⁻¹ * inner ℝ a (z - x)) •
          fderiv ℝ χ (ρ⁻¹ • (z - x)) := by
  have htranslate : DifferentiableAt ℝ (fun y : E ↦ y - x) z := by
    fun_prop
  have hscaled : DifferentiableAt ℝ (fun y : E ↦ ρ⁻¹ • (y - x)) z := by
    fun_prop
  have htwo_ne : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hχdiff : Differentiable ℝ χ := hχ.differentiable htwo_ne
  have hχat : DifferentiableAt ℝ χ (ρ⁻¹ • (z - x)) :=
    hχdiff (ρ⁻¹ • (z - x))
  have hcutoff : DifferentiableAt ℝ
      (fun y : E ↦ χ (ρ⁻¹ • (y - x))) z :=
    hχat.comp z hscaled
  have hlinear : DifferentiableAt ℝ (fun y : E ↦ inner ℝ a (y - x)) z := by
    exact (differentiableAt_const (c := a)).inner ℝ htranslate
  have hlinear_fderiv :
      fderiv ℝ (fun y : E ↦ inner ℝ a (y - x)) z = innerSL ℝ a := by
    have hsub : HasFDerivAt (fun y : E ↦ y - x)
        (ContinuousLinearMap.id ℝ E) z := by
      convert (hasFDerivAt_id (𝕜 := ℝ) z).sub (hasFDerivAt_const x z) using 1
      · ext y
        rfl
      · simp
    ext v
    have hinner := fderiv_inner_apply
      (f := fun _ : E ↦ a) (g := fun y : E ↦ y - x)
      ℝ (differentiableAt_const (c := a)) htranslate v
    rw [hsub.fderiv] at hinner
    simpa [Function.id_def] using hinner
  have hqderiv : fderiv ℝ (fun y : E ↦ ρ⁻¹ • (y - x)) z =
      ρ⁻¹ • ContinuousLinearMap.id ℝ E := by
    have hsub : HasFDerivAt (fun y : E ↦ y - x)
        (ContinuousLinearMap.id ℝ E) z := by
      convert (hasFDerivAt_id (𝕜 := ℝ) z).sub (hasFDerivAt_const x z) using 1
      · ext y
        rfl
      · simp
    exact (hsub.const_smul (ρ⁻¹ : ℝ)).fderiv
  have hcutoff_deriv : fderiv ℝ (fun y : E ↦ χ (ρ⁻¹ • (y - x))) z =
      ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • (z - x)) := by
    change fderiv ℝ (χ ∘ (fun y : E ↦ ρ⁻¹ • (y - x))) z = _
    rw [fderiv_comp z (f := fun y : E ↦ ρ⁻¹ • (y - x)) (g := χ) hχat hscaled,
      hqderiv]
    ext v
    simp [smul_eq_mul]
  have hprod := fderiv_fun_mul hcutoff hlinear
  change fderiv ℝ
      (fun y : E ↦ χ (ρ⁻¹ • (y - x)) * inner ℝ a (y - x)) z = _
  rw [hprod, hlinear_fderiv, hcutoff_deriv]
  ext v
  simp [innerSL_apply_apply, smul_eq_mul]
  ring

/-- Evaluating the second Fréchet derivative of a scaled linear bump on two directions
exposes the two first-derivative cross terms and the second-derivative term. -/
theorem secondFDeriv_scaledLinearBump_apply (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (x : E) (ρ : ℝ) (a z v u : E) (_hρ : 0 < ρ) :
    fderiv ℝ (fderiv ℝ (scaledLinearBump χ x ρ a)) z v u =
      ρ⁻¹ *
          (fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u +
            inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u) +
        ρ⁻¹ ^ 2 * inner ℝ a (z - x) *
          fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u := by
  have htwo_ne : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hχdiff : Differentiable ℝ χ := hχ.differentiable htwo_ne
  have hscaleCont : ContDiff ℝ ∞ (fun y : E ↦ ρ⁻¹ • (y - x)) := by
    have htranslate : ContDiff ℝ ∞ (fun y : E ↦ y - x) :=
      contDiff_id.sub (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ x))
    exact htranslate.const_smul ρ⁻¹
  have htwo_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
    have htwo_nat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr htwo_nat
  have hcutoffCont : ContDiff ℝ 2
      (fun y : E ↦ χ (ρ⁻¹ • (y - x))) :=
    hχ.comp (hscaleCont.of_le htwo_le_infty)
  have hcutoffAt : ContDiffAt ℝ 2
      (fun y : E ↦ χ (ρ⁻¹ • (y - x))) z := hcutoffCont.contDiffAt
  have hlinearCont : ContDiff ℝ ∞ (fun y : E ↦ inner ℝ a (y - x)) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ a)).inner ℝ
      (contDiff_id.sub (contDiff_const : ContDiff ℝ ∞ (fun _ : E ↦ x)))
  have hlinearAt : ContDiffAt ℝ 2
      (fun y : E ↦ inner ℝ a (y - x)) z :=
    (hlinearCont.of_le htwo_le_infty).contDiffAt
  have hqdiff : ∀ y : E, DifferentiableAt ℝ
      (fun w : E ↦ ρ⁻¹ • (w - x)) y := by
    intro y
    fun_prop
  have hqderiv : ∀ y : E, fderiv ℝ
      (fun w : E ↦ ρ⁻¹ • (w - x)) y =
        ρ⁻¹ • ContinuousLinearMap.id ℝ E := by
    intro y
    have hsub : HasFDerivAt (fun w : E ↦ w - x)
        (ContinuousLinearMap.id ℝ E) y := by
      convert (hasFDerivAt_id (𝕜 := ℝ) y).sub (hasFDerivAt_const x y) using 1
      · ext w
        rfl
      · simp
    exact (hsub.const_smul (ρ⁻¹ : ℝ)).fderiv
  have hcutoff_fderiv : fderiv ℝ
      (fun y : E ↦ χ (ρ⁻¹ • (y - x))) =
        fun y ↦ ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • (y - x)) := by
    funext y
    change fderiv ℝ (χ ∘ (fun w : E ↦ ρ⁻¹ • (w - x))) y = _
    rw [fderiv_comp y (f := fun w : E ↦ ρ⁻¹ • (w - x)) (g := χ)
      (hχdiff (ρ⁻¹ • (y - x))) (hqdiff y), hqderiv y]
    ext w
    simp [smul_eq_mul]
  have hlinear_fderiv : fderiv ℝ
      (fun y : E ↦ inner ℝ a (y - x)) =
        fun _ ↦ innerSL ℝ a := by
    funext y
    ext w
    have hsub : HasFDerivAt (fun t : E ↦ t - x)
        (ContinuousLinearMap.id ℝ E) y := by
      convert (hasFDerivAt_id (𝕜 := ℝ) y).sub (hasFDerivAt_const x y) using 1
      · ext t
        rfl
      · simp
    have hinner := fderiv_inner_apply
      (f := fun _ : E ↦ a) (g := fun t : E ↦ t - x)
      ℝ (differentiableAt_const (c := a)) hsub.differentiableAt w
    rw [hsub.fderiv] at hinner
    simpa [Function.id_def] using hinner
  have hfdχ : DifferentiableAt ℝ (fderiv ℝ χ)
      (ρ⁻¹ • (z - x)) := by
    have horder : 1 + 1 ≤ (2 : WithTop ℕ∞) := by norm_num
    have hone_ne : (1 : WithTop ℕ∞) ≠ 0 := by
      norm_num
    exact (hχ.fderiv_right horder).differentiable hone_ne
      (ρ⁻¹ • (z - x))
  have hfdχ_comp : DifferentiableAt ℝ
      (fun y : E ↦ fderiv ℝ χ (ρ⁻¹ • (y - x))) z :=
    hfdχ.comp z (hqdiff z)
  have hfdχ_comp_deriv : fderiv ℝ
      (fun y : E ↦ fderiv ℝ χ (ρ⁻¹ • (y - x))) z =
        (fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x))).comp
          (fderiv ℝ (fun y : E ↦ ρ⁻¹ • (y - x)) z) := by
    change fderiv ℝ ((fderiv ℝ χ) ∘
      (fun y : E ↦ ρ⁻¹ • (y - x))) z = _
    exact fderiv_comp z (f := fun y : E ↦ ρ⁻¹ • (y - x))
      (g := fderiv ℝ χ) hfdχ (hqdiff z)
  have hcutoff_second : fderiv ℝ
      (fderiv ℝ (fun y : E ↦ χ (ρ⁻¹ • (y - x)))) z =
        ρ⁻¹ • ((fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x))).comp
          (ρ⁻¹ • ContinuousLinearMap.id ℝ E)) := by
    rw [hcutoff_fderiv]
    change fderiv ℝ (ρ⁻¹ •
      (fun y : E ↦ fderiv ℝ χ (ρ⁻¹ • (y - x)))) z = _
    rw [fderiv_const_smul hfdχ_comp (ρ⁻¹ : ℝ), hfdχ_comp_deriv, hqderiv z]
  have hcutoff_first_v : fderiv ℝ
      (fun y : E ↦ χ (ρ⁻¹ • (y - x))) z v =
        ρ⁻¹ * fderiv ℝ χ (ρ⁻¹ • (z - x)) v := by
    rw [hcutoff_fderiv]
    simp [smul_eq_mul]
  have hcutoff_first_u : fderiv ℝ
      (fun y : E ↦ χ (ρ⁻¹ • (y - x))) z u =
        ρ⁻¹ * fderiv ℝ χ (ρ⁻¹ • (z - x)) u := by
    rw [hcutoff_fderiv]
    simp [smul_eq_mul]
  have hcutoff_second_vu : fderiv ℝ
      (fderiv ℝ (fun y : E ↦ χ (ρ⁻¹ • (y - x)))) z v u =
        ρ⁻¹ ^ 2 * fderiv ℝ (fderiv ℝ χ)
          (ρ⁻¹ • (z - x)) v u := by
    rw [hcutoff_second]
    simp [smul_eq_mul, pow_two]
    ring
  have hlinear_first_v : fderiv ℝ
      (fun y : E ↦ inner ℝ a (y - x)) z v = inner ℝ a v := by
    rw [hlinear_fderiv]
    simp [innerSL_apply_apply]
  have hlinear_first_u : fderiv ℝ
      (fun y : E ↦ inner ℝ a (y - x)) z u = inner ℝ a u := by
    rw [hlinear_fderiv]
    simp [innerSL_apply_apply]
  have hlinear_second : fderiv ℝ
      (fderiv ℝ (fun y : E ↦ inner ℝ a (y - x))) z = 0 := by
    rw [hlinear_fderiv]
    simp
  have hproduct := fderiv_fderiv_mul_apply
    (f := fun y : E ↦ χ (ρ⁻¹ • (y - x)))
    (g := fun y : E ↦ inner ℝ a (y - x)) (x := z) (v := v) (u := u)
    hcutoffAt hlinearAt
  change fderiv ℝ (fderiv ℝ
      (fun y : E ↦ χ (ρ⁻¹ • (y - x)) * inner ℝ a (y - x))) z v u = _
  rw [hproduct, hlinear_second, hcutoff_first_v, hcutoff_first_u,
    hlinear_first_v, hlinear_first_u, hcutoff_second_vu]
  simp only [zero_apply, mul_zero]
  ring

/-- A uniform cutoff bound gives a supportwise value bound for a positive-scale scaled
linear bump. -/
theorem norm_scaledLinearBump_le (χ : E → ℝ) (_hχ : ContDiff ℝ 2 χ) (M₀ : ℝ)
    (hχ_support : tsupport χ ⊆ Metric.ball 0 1) (hχ_bound : ∀ y, ‖χ y‖ ≤ M₀)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (scaledLinearBump χ x ρ a)) :
    ‖scaledLinearBump χ x ρ a z‖ ≤ M₀ * ‖a‖ * ρ := by
  have hzclosed := tsupport_scaledLinearBump_subset_closedBall
    χ hχ_support x ρ a hρ hz
  have hdist : ‖z - x‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
  have hM₀ : 0 ≤ M₀ :=
    le_trans (norm_nonneg (χ 0)) (hχ_bound 0)
  have hinner : ‖inner ℝ a (z - x)‖ ≤ ‖a‖ * ‖z - x‖ :=
    norm_inner_le_norm _ _
  have hprod : ‖χ (ρ⁻¹ • (z - x))‖ * ‖inner ℝ a (z - x)‖ ≤
      M₀ * (‖a‖ * ‖z - x‖) := by
    exact mul_le_mul (hχ_bound _) hinner (norm_nonneg _) hM₀
  have hscale : M₀ * (‖a‖ * ‖z - x‖) ≤ M₀ * (‖a‖ * ρ) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)) hM₀
  calc
    ‖scaledLinearBump χ x ρ a z‖ =
        ‖χ (ρ⁻¹ • (z - x))‖ * ‖inner ℝ a (z - x)‖ := by
      simp [scaledLinearBump, norm_mul]
    _ ≤ M₀ * (‖a‖ * ‖z - x‖) := hprod
    _ ≤ M₀ * (‖a‖ * ρ) := hscale
    _ = M₀ * ‖a‖ * ρ := by ring

/-- Uniform zeroth- and first-derivative cutoff bounds give a supportwise first-derivative
bound for a positive-scale scaled linear bump. -/
theorem norm_fderiv_scaledLinearBump_le (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (M₀ M₁ : ℝ) (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (hχ_bound : ∀ y, ‖χ y‖ ≤ M₀)
    (hDχ_bound : ∀ y, ‖fderiv ℝ χ y‖ ≤ M₁)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (scaledLinearBump χ x ρ a)) :
    ‖fderiv ℝ (scaledLinearBump χ x ρ a) z‖ ≤ (M₁ + M₀) * ‖a‖ := by
  have hzclosed := tsupport_scaledLinearBump_subset_closedBall
    χ hχ_support x ρ a hρ hz
  have hdist : ‖z - x‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
  have hM₀ : 0 ≤ M₀ :=
    le_trans (norm_nonneg (χ 0)) (hχ_bound 0)
  have hM₁ : 0 ≤ M₁ :=
    le_trans (norm_nonneg (fderiv ℝ χ 0)) (hDχ_bound 0)
  have hscalar : ‖ρ⁻¹ * inner ℝ a (z - x)‖ ≤ ‖a‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    calc
      ρ⁻¹ * ‖inner ℝ a (z - x)‖ ≤
          ρ⁻¹ * (‖a‖ * ‖z - x‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _)
          (le_of_lt (inv_pos.mpr hρ))
      _ ≤ ρ⁻¹ * (‖a‖ * ρ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
          (le_of_lt (inv_pos.mpr hρ))
      _ = ‖a‖ := by field_simp [hρ.ne']
  have hterm₀ : ‖χ (ρ⁻¹ • (z - x))‖ * ‖innerSL ℝ a‖ ≤
      M₀ * ‖a‖ := by
    rw [innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_right (hχ_bound _) (norm_nonneg _)
  have hterm₁ : ‖ρ⁻¹ * inner ℝ a (z - x)‖ *
      ‖fderiv ℝ χ (ρ⁻¹ • (z - x))‖ ≤ ‖a‖ * M₁ :=
    mul_le_mul hscalar (hDχ_bound _) (norm_nonneg _) (norm_nonneg _)
  rw [fderiv_scaledLinearBump χ hχ x ρ a z hρ]
  calc
    ‖χ (ρ⁻¹ • (z - x)) • innerSL ℝ a +
        (ρ⁻¹ * inner ℝ a (z - x)) •
          fderiv ℝ χ (ρ⁻¹ • (z - x))‖ ≤
        ‖χ (ρ⁻¹ • (z - x)) • innerSL ℝ a‖ +
          ‖(ρ⁻¹ * inner ℝ a (z - x)) •
            fderiv ℝ χ (ρ⁻¹ • (z - x))‖ := norm_add_le _ _
    _ = ‖χ (ρ⁻¹ • (z - x))‖ * ‖innerSL ℝ a‖ +
          ‖ρ⁻¹ * inner ℝ a (z - x)‖ *
            ‖fderiv ℝ χ (ρ⁻¹ • (z - x))‖ := by rw [norm_smul, norm_smul]
    _ ≤ M₀ * ‖a‖ + ‖a‖ * M₁ := add_le_add hterm₀ hterm₁
    _ = (M₁ + M₀) * ‖a‖ := by ring

/-- Uniform first- and second-derivative cutoff bounds give the supportwise Hessian bound
for a positive-scale scaled linear bump. -/
theorem norm_secondFDeriv_scaledLinearBump_le (χ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (M₁ M₂ : ℝ) (hχ_support : tsupport χ ⊆ Metric.ball 0 1)
    (hDχ_bound : ∀ y, ‖fderiv ℝ χ y‖ ≤ M₁)
    (hD2χ_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ χ) y‖ ≤ M₂)
    (x : E) (ρ : ℝ) (a z : E) (hρ : 0 < ρ)
    (hz : z ∈ tsupport (scaledLinearBump χ x ρ a)) :
    ‖fderiv ℝ (fderiv ℝ (scaledLinearBump χ x ρ a)) z‖ ≤
      (M₂ + 2 * M₁) * ‖a‖ / ρ := by
  have hzclosed := tsupport_scaledLinearBump_subset_closedBall
    χ hχ_support x ρ a hρ hz
  have hdist : ‖z - x‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
  have hM₁ : 0 ≤ M₁ :=
    le_trans (norm_nonneg (fderiv ℝ χ 0)) (hDχ_bound 0)
  have hM₂ : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ χ) 0)) (hD2χ_bound 0)
  have hcross : ∀ v u : E,
      ‖ρ⁻¹ * (fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u +
          inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u)‖ ≤
        ρ⁻¹ * (2 * M₁ * ‖a‖ * ‖v‖ * ‖u‖) := by
    intro v u
    have hDv := (fderiv ℝ χ (ρ⁻¹ • (z - x))).le_of_opNorm_le
      (hDχ_bound _) v
    have hDu := (fderiv ℝ χ (ρ⁻¹ • (z - x))).le_of_opNorm_le
      (hDχ_bound _) u
    have hav : ‖inner ℝ a v‖ ≤ ‖a‖ * ‖v‖ := norm_inner_le_norm _ _
    have hau : ‖inner ℝ a u‖ ≤ ‖a‖ * ‖u‖ := norm_inner_le_norm _ _
    have hterm₁ : ‖fderiv ℝ χ (ρ⁻¹ • (z - x)) v‖ *
        ‖inner ℝ a u‖ ≤ (M₁ * ‖v‖) * (‖a‖ * ‖u‖) :=
      mul_le_mul hDv hau (norm_nonneg _) (mul_nonneg hM₁ (norm_nonneg _))
    have hterm₂ : ‖inner ℝ a v‖ *
        ‖fderiv ℝ χ (ρ⁻¹ • (z - x)) u‖ ≤ (‖a‖ * ‖v‖) * (M₁ * ‖u‖) :=
      mul_le_mul hav hDu (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    calc
      ρ⁻¹ * ‖fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u +
          inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u‖ ≤
          ρ⁻¹ * (‖fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u‖ +
            ‖inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (le_of_lt (inv_pos.mpr hρ))
      _ = ρ⁻¹ * (‖fderiv ℝ χ (ρ⁻¹ • (z - x)) v‖ *
          ‖inner ℝ a u‖ + ‖inner ℝ a v‖ *
            ‖fderiv ℝ χ (ρ⁻¹ • (z - x)) u‖) := by
        rw [norm_mul, norm_mul]
      _ ≤ ρ⁻¹ * ((M₁ * ‖v‖) * (‖a‖ * ‖u‖) +
          (‖a‖ * ‖v‖) * (M₁ * ‖u‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm₁ hterm₂)
          (le_of_lt (inv_pos.mpr hρ))
      _ = ρ⁻¹ * (2 * M₁ * ‖a‖ * ‖v‖ * ‖u‖) := by ring
  have hquad : ∀ v u : E,
      ‖ρ⁻¹ ^ 2 * inner ℝ a (z - x) *
          fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u‖ ≤
        ρ⁻¹ * (M₂ * ‖a‖ * ‖v‖ * ‖u‖) := by
    intro v u
    have hD2v := (fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x))).le_of_opNorm_le
      (hD2χ_bound _) v
    have hD2vu :=
      (fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v).le_of_opNorm_le
        hD2v u
    have hinnerd : ‖inner ℝ a (z - x)‖ ≤ ‖a‖ * ρ :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
    calc
      ‖ρ⁻¹ ^ 2 * inner ℝ a (z - x) *
          fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u‖ =
          (ρ⁻¹) ^ 2 * ‖inner ℝ a (z - x)‖ *
            ‖fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u‖ := by
        rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hρ)]
      _ ≤ (ρ⁻¹) ^ 2 * (‖a‖ * ρ) *
          ((M₂ * ‖v‖) * ‖u‖) := by
        gcongr
      _ = ρ⁻¹ * (M₂ * ‖a‖ * ‖v‖ * ‖u‖) := by
        field_simp [hρ.ne']
  have hpoint : ∀ v u : E,
      ‖fderiv ℝ (fderiv ℝ (scaledLinearBump χ x ρ a)) z v u‖ ≤
        ρ⁻¹ * ((M₂ + 2 * M₁) * ‖a‖) * ‖v‖ * ‖u‖ := by
    intro v u
    rw [secondFDeriv_scaledLinearBump_apply χ hχ x ρ a z v u hρ]
    calc
      ‖ρ⁻¹ * (fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u +
          inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u) +
          ρ⁻¹ ^ 2 * inner ℝ a (z - x) *
            fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u‖ ≤
          ‖ρ⁻¹ * (fderiv ℝ χ (ρ⁻¹ • (z - x)) v * inner ℝ a u +
            inner ℝ a v * fderiv ℝ χ (ρ⁻¹ • (z - x)) u)‖ +
          ‖ρ⁻¹ ^ 2 * inner ℝ a (z - x) *
            fderiv ℝ (fderiv ℝ χ) (ρ⁻¹ • (z - x)) v u‖ := norm_add_le _ _
      _ ≤ ρ⁻¹ * (2 * M₁ * ‖a‖ * ‖v‖ * ‖u‖) +
          ρ⁻¹ * (M₂ * ‖a‖ * ‖v‖ * ‖u‖) :=
        add_le_add (hcross v u) (hquad v u)
      _ = ρ⁻¹ * ((M₂ + 2 * M₁) * ‖a‖) * ‖v‖ * ‖u‖ := by ring
  have hC : 0 ≤ (M₂ + 2 * M₁) * ‖a‖ / ρ := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 := by
      norm_num
    have hsum_nonneg : 0 ≤ M₂ + 2 * M₁ :=
      add_nonneg hM₂ (mul_nonneg htwo_nonneg hM₁)
    have hprod_nonneg : 0 ≤ (M₂ + 2 * M₁) * ‖a‖ :=
      mul_nonneg hsum_nonneg (norm_nonneg _)
    exact div_nonneg hprod_nonneg (le_of_lt hρ)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC (norm_nonneg v))
  intro u
  calc
    ‖fderiv ℝ (fderiv ℝ (scaledLinearBump χ x ρ a)) z v u‖ ≤
        ρ⁻¹ * ((M₂ + 2 * M₁) * ‖a‖) * ‖v‖ * ‖u‖ := hpoint v u
    _ = ((M₂ + 2 * M₁) * ‖a‖ / ρ) * ‖v‖ * ‖u‖ := by
      field_simp [hρ.ne']

end AffineBump
