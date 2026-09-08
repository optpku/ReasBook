module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Support

public section

noncomputable section

open Filter Set
open scoped Topology Pointwise

universe uE uF

namespace LocalCutoff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The remainder obtained by multiplying `N` by the cutoff `χ` rescaled by `ρ`. -/
noncomputable def remainder (χ : E → ℝ) (ρ : ℝ) (N : E → F) : E → F :=
  fun x ↦ χ (ρ⁻¹ • x) • N x

/-- The perturbation of a continuous linear map by a rescaled cutoff remainder. -/
noncomputable def linearize (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) : E → F :=
  fun x ↦ A x + remainder χ ρ N x

/-- The rescaled cutoff remainder evaluates as `χ (ρ⁻¹ • x) • N x`. -/
theorem remainder_apply (χ : E → ℝ) (ρ : ℝ) (N : E → F) (x : E) :
    remainder χ ρ N x = χ (ρ⁻¹ • x) • N x := by
  rfl

/-- The cutoff perturbation evaluates as `A x + χ (ρ⁻¹ • x) • N x`. -/
theorem linearize_apply (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) (x : E) :
    linearize χ ρ A N x = A x + χ (ρ⁻¹ • x) • N x := by
  rfl

/-- On the scaled inner closed ball, a plateau cutoff perturbation agrees with
`x ↦ A x + N x`. -/
theorem linearize_eq_add_of_mem_closedBall (χ : E → ℝ) (ρ rIn : ℝ)
    (A : E →L[ℝ] F) (N : E → F) (hρ : 0 < ρ)
    (hχ_inner : ∀ y ∈ Metric.closedBall (0 : E) rIn, χ y = 1) {x : E}
    (hx : x ∈ Metric.closedBall 0 (ρ * rIn)) :
    linearize χ ρ A N x = A x + N x := by
  rw [linearize_apply]
  have hnorm : ‖ρ⁻¹ • x‖ ≤ rIn := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
    have hx' : ‖x‖ ≤ ρ * rIn := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    calc
      ρ⁻¹ * ‖x‖ ≤ ρ⁻¹ * (ρ * rIn) :=
        mul_le_mul_of_nonneg_left hx' (by positivity)
      _ = rIn := by field_simp
  have hy : ρ⁻¹ • x ∈ Metric.closedBall (0 : E) rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa [norm_zero] using hnorm
  rw [hχ_inner _ hy]
  simp

/-- At and beyond the scaled outer radius, a cutoff perturbation agrees with its
linear part. -/
theorem linearize_eq_linear_of_outer_radius_le_norm (χ : E → ℝ) (ρ rOut : ℝ)
    (A : E →L[ℝ] F) (N : E → F) (hρ : 0 < ρ)
    (hχ_outer : ∀ y, rOut ≤ ‖y‖ → χ y = 0) {x : E}
    (hx : ρ * rOut ≤ ‖x‖) :
    linearize χ ρ A N x = A x := by
  rw [linearize_apply]
  have hnorm : rOut ≤ ‖ρ⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
    have hmul : ρ⁻¹ * (ρ * rOut) ≤ ρ⁻¹ * ‖x‖ :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    calc
      rOut = ρ⁻¹ * (ρ * rOut) := by field_simp
      _ ≤ ρ⁻¹ * ‖x‖ := hmul
  rw [hχ_outer _ hnorm]
  simp

/-- A cutoff equal to one near zero makes the cutoff perturbation and the original
nonlinear map have the same germ at zero. -/
theorem linearize_eventuallyEq (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) (hχ : χ =ᶠ[𝓝 0] 1) :
    linearize χ ρ A N =ᶠ[𝓝 0] fun x ↦ A x + N x := by
  have harg : Tendsto (fun x : E ↦ ρ⁻¹ • x) (𝓝 0) (𝓝 0) := by
    have harg' : Tendsto (fun x : E ↦ (ρ⁻¹ : ℝ) • x) (𝓝 0)
        (𝓝 ((ρ⁻¹ : ℝ) • (0 : E))) :=
      tendsto_const_nhds.smul tendsto_id
    simpa using harg'
  have hscaled :
      (fun x : E ↦ χ (ρ⁻¹ • x)) =ᶠ[𝓝 0] (fun _ : E ↦ (1 : ℝ)) := by
    simpa [Function.comp_def] using hχ.comp_tendsto harg
  filter_upwards [hscaled] with x hx
  simp only [linearize_apply, hx, one_smul]

/-- Every iterated Fréchet derivative at zero is preserved by a cutoff equal to one
near zero. -/
theorem iteratedFDeriv_linearize_zero (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) (hχ : χ =ᶠ[𝓝 0] 1) (n : ℕ) :
    iteratedFDeriv ℝ n (linearize χ ρ A N) 0 =
      iteratedFDeriv ℝ n (fun x ↦ A x + N x) 0 := by
  have hlocal : linearize χ ρ A N =ᶠ[𝓝 0] fun x ↦ A x + N x :=
    linearize_eventuallyEq χ ρ A N hχ
  exact (hlocal.iteratedFDeriv ℝ n).eq_of_nhds

/-- A nonzero rescaling of a compactly supported cutoff produces a compactly supported
cutoff remainder. -/
theorem hasCompactSupport_remainder (χ : E → ℝ) (ρ : ℝ) (N : E → F)
    (hρ : ρ ≠ 0) (hχ : HasCompactSupport χ) :
    HasCompactSupport (remainder χ ρ N) := by
  unfold remainder
  apply HasCompactSupport.smul_right
  exact hχ.comp_smul (inv_ne_zero hρ)

/-- Local `C^ν` regularity on an open neighborhood of the rescaled cutoff support
suffices for the cutoff perturbation to be globally `C^ν`. -/
theorem contDiff_linearize (ν : ℕ) (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) (U : Set E) (hU : IsOpen U) (hU_zero : U ∈ 𝓝 0)
    (hχ : ContDiff ℝ ν fun x ↦ χ (ρ⁻¹ • x)) (hN : ContDiffOn ℝ ν N U)
    (hsupport : tsupport (fun x ↦ χ (ρ⁻¹ • x)) ⊆ U) :
    ContDiff ℝ ν (linearize χ ρ A N) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hxU : x ∈ U
  · have hN_at : ContDiffAt ℝ ν N x :=
      (hN x hxU).contDiffAt (hU.mem_nhds hxU)
    have hχ_at : ContDiffAt ℝ ν (fun y ↦ χ (ρ⁻¹ • y)) x :=
      hχ.contDiffAt
    have hprod : ContDiffAt ℝ ν (fun y ↦ χ (ρ⁻¹ • y) • N y) x :=
      hχ_at.smul hN_at
    have hA : ContDiffAt ℝ ν (fun y ↦ A y) x :=
      A.contDiff.contDiffAt
    have hadd := hA.add hprod
    have hfun : linearize χ ρ A N =
        (A : E → F) + (fun y ↦ χ (ρ⁻¹ • y) • N y) := by
      funext y
      rfl
    rw [hfun]
    exact hadd
  · have hxnot : x ∉ tsupport (fun y : E ↦ χ (ρ⁻¹ • y)) := by
      intro hx
      exact hxU (hsupport hx)
    have hopen : (tsupport (fun y : E ↦ χ (ρ⁻¹ • y)))ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hxnot
    have hzero : (fun y : E ↦ remainder χ ρ N y) =ᶠ[𝓝 x]
        (fun _ : E ↦ (0 : F)) := by
      filter_upwards [hopen] with y hy
      have hc : χ (ρ⁻¹ • y) = 0 := by
        exact image_eq_zero_of_notMem_tsupport
          (f := fun z : E ↦ χ (ρ⁻¹ • z)) hy
      simp [remainder, hc]
    have hprod : ContDiffAt ℝ ν (remainder χ ρ N) x :=
      contDiffAt_const.congr_of_eventuallyEq hzero
    have hA : ContDiffAt ℝ ν (fun y ↦ A y) x :=
      A.contDiff.contDiffAt
    have hadd := hA.add hprod
    have hfun : linearize χ ρ A N = (A : E → F) + remainder χ ρ N := by
      funext y
      rfl
    rw [hfun]
    exact hadd

/-- A cutoff perturbation fixes zero when its nonlinear remainder vanishes there. -/
theorem linearize_zero (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) (hN : N 0 = 0) :
    linearize χ ρ A N 0 = 0 := by
  simp [linearize, remainder, hN]

/-- If the nonlinear map has zero value and derivative at zero, then a differentiable
rescaled cutoff perturbation has derivative `A` there. -/
theorem fderiv_linearize_zero (χ : E → ℝ) (ρ : ℝ) (A : E →L[ℝ] F)
    (N : E → F) (hχ : DifferentiableAt ℝ (fun x ↦ χ (ρ⁻¹ • x)) 0)
    (hN : DifferentiableAt ℝ N 0) (hN_zero : N 0 = 0)
    (hDN_zero : fderiv ℝ N 0 = 0) :
    fderiv ℝ (linearize χ ρ A N) 0 = A := by
  have hrem_raw := hχ.hasFDerivAt.smul hN.hasFDerivAt
  have hrem : HasFDerivAt (remainder χ ρ N) (0 : E →L[ℝ] F) 0 := by
    convert hrem_raw using 1
    · rfl
    · simp [hN_zero, hDN_zero]
  have hfun : linearize χ ρ A N = (A : E → F) + remainder χ ρ N := by
    funext x
    rfl
  have hlin : HasFDerivAt (linearize χ ρ A N) (A + 0) 0 := by
    rw [hfun]
    exact A.hasFDerivAt.add hrem
  simpa using hlin.fderiv

/-- Under explicit first-order remainder and derivative bounds, shrinking a compact
`C¹` cutoff makes the derivative of the cutoff remainder uniformly small. -/
theorem exists_scale_norm_fderiv_remainder_le (χ : E → ℝ) (N : E → F)
    (U : Set E) (hU : IsOpen U) (hU_zero : U ∈ 𝓝 0)
    (hχ : ContDiff ℝ 1 χ) (hχ_compact : HasCompactSupport χ)
    (hN : ContDiffOn ℝ 1 N U) (hN_zero : N 0 = 0)
    (hDN_zero : fderiv ℝ N 0 = 0)
    (hN_remainder : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖N x‖ ≤ η * ‖x‖)
    (hDN_control : ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ x, ‖x‖ < δ → ‖fderiv ℝ N x‖ ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ, 0 < ρ → ρ < δ → ∀ x,
      ‖fderiv ℝ (remainder χ ρ N) x‖ ≤ ε := by
  obtain ⟨M₀, hM₀⟩ := hχ.continuous.bounded_above_of_compact_support hχ_compact
  have hM₀_nonneg : 0 ≤ M₀ := (norm_nonneg (χ 0)).trans (hM₀ 0)
  obtain ⟨M₁, hM₁_nonneg, hM₁⟩ :=
    HasCompactSupport.exists_norm_fderiv_le hχ_compact hχ
  obtain ⟨R, hR_pos, hR⟩ := hχ_compact.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨rU, hrU_pos, hrU_ball⟩ := Metric.mem_nhds_iff.mp hU_zero
  let K : ℝ := M₀ + M₁ * R
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let η : ℝ := ε / (K + 1)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos hε (by linarith)
  have hηK : η * K ≤ ε := by
    dsimp [η]
    calc
      ε / (K + 1) * K ≤ ε / (K + 1) * (K + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε := by field_simp
  obtain ⟨δN, hδN_pos, hδN⟩ := hN_remainder η hη_pos
  obtain ⟨δD, hδD_pos, hδD⟩ := hDN_control η hη_pos
  let δ₀ : ℝ := min (min δN δD) rU
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min (lt_min hδN_pos hδD_pos) hrU_pos
  let δ : ℝ := δ₀ / (R + 1)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact div_pos hδ₀_pos (by linarith)
  refine ⟨δ, hδ_pos, ?_⟩
  intro ρ hρ_pos hρ_small x
  let c : E → ℝ := fun y ↦ χ (ρ⁻¹ • y)
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
  have htsupport_c : tsupport c = ρ • tsupport χ := by
    dsimp [c]
    rw [tsupport, support_comp_inv_smul₀ hρ_ne, tsupport]
    exact closure_smul₀' hρ_ne _
  have htsupport_remainder : tsupport (remainder χ ρ N) ⊆ tsupport c := by
    change tsupport (fun y : E ↦ χ (ρ⁻¹ • y) • N y) ⊆ tsupport c
    simpa [c] using
      (tsupport_smul_subset_left (fun y : E ↦ χ (ρ⁻¹ • y)) N)
  by_cases hx : x ∈ tsupport c
  · have hx_scaled : x ∈ ρ • tsupport χ := by
      rw [← htsupport_c]
      exact hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_smul_set.mp hx_scaled
    have hy_norm : ‖y‖ ≤ R := hR y hy
    have hx_norm_le : ‖x‖ ≤ ρ * R := by
      rw [← hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hρ_pos]
      exact mul_le_mul_of_nonneg_left hy_norm (le_of_lt hρ_pos)
    have hrhoR : ρ * R < δ₀ := by
      calc
        ρ * R ≤ ρ * (R + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hρ_pos)
        _ < δ₀ / (R + 1) * (R + 1) := by
          exact mul_lt_mul_of_pos_right hρ_small (by positivity)
        _ = δ₀ := by field_simp
    have hx_norm_lt : ‖x‖ < δ₀ := lt_of_le_of_lt hx_norm_le hrhoR
    have hxU : x ∈ U := by
      apply hrU_ball
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hx_norm_lt
        (min_le_right (min δN δD) rU)
    have hxNδ : ‖x‖ < δN := lt_of_lt_of_le hx_norm_lt
      ((min_le_left (min δN δD) rU).trans (min_le_left δN δD))
    have hxDδ : ‖x‖ < δD := lt_of_lt_of_le hx_norm_lt
      ((min_le_left (min δN δD) rU).trans (min_le_right δN δD))
    have hN_at : DifferentiableAt ℝ N x :=
      ((hN x hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
    have hscale_at : DifferentiableAt ℝ (fun z : E ↦ ρ⁻¹ • z) x := by
      exact ((hasFDerivAt_id x).const_smul (ρ⁻¹)).differentiableAt
    have hc_at : DifferentiableAt ℝ c x := by
      dsimp [c]
      exact (hχ.differentiable (by norm_num)).differentiableAt.comp x hscale_at
    have hformula : fderiv ℝ (remainder χ ρ N) x =
        c x • fderiv ℝ N x + (fderiv ℝ c x).smulRight (N x) := by
      change fderiv ℝ (fun y : E ↦ c y • N y) x = _
      exact fderiv_fun_smul hc_at hN_at
    have hcutoff_deriv : fderiv ℝ c x = ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • x) := by
      dsimp [c]
      exact fderiv_comp_smul ρ⁻¹
    rw [hformula, hcutoff_deriv]
    calc
      ‖c x • fderiv ℝ N x + (ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • x)).smulRight (N x)‖ ≤
          ‖c x • fderiv ℝ N x‖ +
            ‖(ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • x)).smulRight (N x)‖ := norm_add_le _ _
      _ = ‖c x‖ * ‖fderiv ℝ N x‖ +
          ‖ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • x)‖ * ‖N x‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ M₀ * η + (ρ⁻¹ * M₁) * (η * ‖x‖) := by
        have hc_bound : ‖c x‖ ≤ M₀ := hM₀ _
        have hDx_bound : ‖fderiv ℝ N x‖ ≤ η := hδD x hxDδ
        have hχD_bound : ‖fderiv ℝ χ (ρ⁻¹ • x)‖ ≤ M₁ := hM₁ _
        have hcx_bound : ‖N x‖ ≤ η * ‖x‖ := hδN x hxNδ
        have hfirst : ‖c x‖ * ‖fderiv ℝ N x‖ ≤ M₀ * η :=
          mul_le_mul hc_bound hDx_bound (norm_nonneg _) hM₀_nonneg
        have hinv_nonneg : 0 ≤ ρ⁻¹ := le_of_lt (inv_pos.mpr hρ_pos)
        have hsecond : ‖ρ⁻¹ • fderiv ℝ χ (ρ⁻¹ • x)‖ * ‖N x‖ ≤
            (ρ⁻¹ * M₁) * (η * ‖x‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ_pos)]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hχD_bound hinv_nonneg)
            hcx_bound (by positivity) (by positivity)
        exact add_le_add hfirst hsecond
      _ ≤ M₀ * η + M₁ * (η * R) := by
        have hscale : ρ⁻¹ * (η * ‖x‖) ≤ η * R := by
          calc
            ρ⁻¹ * (η * ‖x‖) ≤ ρ⁻¹ * (η * (ρ * R)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hx_norm_le (le_of_lt hη_pos))
                (le_of_lt (inv_pos.mpr hρ_pos))
            _ = η * R := by field_simp
        have hsecond_scale : (ρ⁻¹ * M₁) * (η * ‖x‖) ≤ M₁ * (η * R) := by
          calc
            (ρ⁻¹ * M₁) * (η * ‖x‖) = M₁ * (ρ⁻¹ * (η * ‖x‖)) := by ring
            _ ≤ M₁ * (η * R) := mul_le_mul_of_nonneg_left hscale hM₁_nonneg
        exact add_le_add_right hsecond_scale (M₀ * η)
      _ = η * K := by
        dsimp [K]
        ring
      _ ≤ ε := hηK
  · have hxrem : x ∉ tsupport (remainder χ ρ N) :=
      fun hxr ↦ hx (htsupport_remainder hxr)
    rw [fderiv_of_notMem_tsupport ℝ hxrem, norm_zero]
    exact le_of_lt hε

end LocalCutoff
