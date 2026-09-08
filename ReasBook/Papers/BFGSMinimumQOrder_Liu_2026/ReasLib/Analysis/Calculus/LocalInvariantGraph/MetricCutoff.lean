module

public import ReasLib.Analysis.Calculus.LocalCutoff
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.Tangent
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.MeanValue

public section

noncomputable section

open Filter Set
open scoped NNReal Pointwise Topology

universe u v

namespace LocalInvariantGraph

/-- A zero-jet map that is smooth near the origin admits a globally smooth,
compactly supported cutoff with an arbitrarily small Lipschitz constant. -/
theorem exists_smallLipschitzCutoffRemainder
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (nu : ℕ) (hnu : 1 ≤ nu) (N : E → G)
    (hN_smooth : ContDiffAt ℝ nu N 0) (hN_zero : N 0 = 0)
    (hN_deriv : HasFDerivAt N (0 : E →L[ℝ] G) 0)
    {epsilon : ℝ≥0} (hepsilon : 0 < epsilon) :
    ∃ R : E → G,
      ContDiff ℝ nu R ∧ HasCompactSupport R ∧ R 0 = 0 ∧
        LipschitzWith epsilon R ∧ R =ᶠ[𝓝 0] N := by
  let chi : ContDiffBump (0 : E) := default
  -- Restrict the local smoothness witness to an open neighborhood, so the
  -- scaled cutoff support can be placed wholly inside it.
  have htop :
      (↑nu : WithTop ℕ∞) = (↑(⊤ : ℕ∞) : WithTop ℕ∞) →
        (↑nu : WithTop ℕ∞) = ⊤ := by
    intro h
    simpa using h
  obtain ⟨U, hU_nhds, hN_on_U⟩ := hN_smooth.contDiffOn le_rfl htop
  obtain ⟨V, hVU, hV_open, hzero_V⟩ := mem_nhds_iff.mp hU_nhds
  have hV_nhds : V ∈ 𝓝 (0 : E) := hV_open.mem_nhds hzero_V
  have hN_on_V : ContDiffOn ℝ nu N V := hN_on_U.mono hVU
  have hnu_one_le : (1 : WithTop ℕ∞) ≤ (↑nu : WithTop ℕ∞) := by
    exact_mod_cast hnu
  have hN_on_V_one : ContDiffOn ℝ 1 N V := hN_on_V.of_le hnu_one_le
  obtain ⟨rV, hrV_pos, hball_V⟩ := Metric.mem_nhds_iff.mp hV_nhds
  have hDN_zero : fderiv ℝ N 0 = 0 := hN_deriv.fderiv
  have hnu_pos : 0 < nu := Nat.zero_lt_one.trans_le hnu
  have hnu_ne : nu ≠ 0 := Nat.ne_of_gt hnu_pos
  -- The zero derivative gives the first-order remainder estimate consumed by
  -- the quantitative cutoff theorem.
  have hN_remainder : ∀ eta : ℝ, 0 < eta →
      ∃ delta > 0, ∀ x, ‖x‖ < delta → ‖N x‖ ≤ eta * ‖x‖ := by
    intro eta heta
    obtain ⟨delta, hdelta_pos, hdelta⟩ :=
      exists_norm_fderiv_remainder_le_at_zero hN_deriv heta
    refine ⟨delta, hdelta_pos, ?_⟩
    intro x hx
    simpa only [hN_zero, sub_zero, zero_apply] using hdelta x hx
  -- Continuity of the derivative near zero supplies the second smallness
  -- condition required by the same cutoff theorem.
  have hDN_control : ∀ eta : ℝ, 0 < eta →
      ∃ delta > 0, ∀ x, ‖x‖ < delta → ‖fderiv ℝ N x‖ ≤ eta := by
    intro eta heta
    have htend : Tendsto (fderiv ℝ N) (𝓝 0) (𝓝 0) := by
      have hcont := hN_smooth.continuousAt_fderiv (Nat.cast_ne_zero.mpr hnu_ne)
      simpa only [ContinuousAt, hDN_zero] using hcont
    have hevent : ∀ᶠ x in 𝓝 (0 : E), ‖fderiv ℝ N x‖ < eta := by
      have hball : Metric.ball (0 : E →L[ℝ] G) eta ∈ 𝓝 0 :=
        Metric.ball_mem_nhds _ heta
      filter_upwards [htend.eventually hball] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    obtain ⟨delta, hdelta_pos, hdelta⟩ := Metric.mem_nhds_iff.mp hevent
    refine ⟨delta, hdelta_pos, ?_⟩
    intro x hx
    apply le_of_lt
    apply hdelta
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hepsilon_real : (0 : ℝ) < epsilon := NNReal.coe_pos.mpr hepsilon
  obtain ⟨deltaD, hdeltaD_pos, hdeltaD⟩ :=
    LocalCutoff.exists_scale_norm_fderiv_remainder_le
      chi N V hV_open hV_nhds chi.contDiff chi.hasCompactSupport
      hN_on_V_one hN_zero hDN_zero hN_remainder hDN_control hepsilon_real
  -- Choose one positive scale satisfying both the derivative estimate and the
  -- support-containment estimate.
  let supportScale : ℝ := rV / (chi.rOut + 1)
  have houtOne_pos : 0 < chi.rOut + 1 := by
    nlinarith [chi.rOut_pos]
  have hsupportScale_pos : 0 < supportScale := by
    exact div_pos hrV_pos houtOne_pos
  let rho : ℝ := min deltaD supportScale / 2
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have hrho_pos : 0 < rho := by
    exact div_pos (lt_min hdeltaD_pos hsupportScale_pos) htwo_pos
  have hrho_lt_min : rho < min deltaD supportScale := by
    dsimp only [rho]
    nlinarith [lt_min hdeltaD_pos hsupportScale_pos]
  have hrho_deltaD : rho < deltaD := hrho_lt_min.trans_le (min_le_left _ _)
  have hrho_supportScale : rho < supportScale :=
    hrho_lt_min.trans_le (min_le_right _ _)
  have hscaled_support :
      tsupport (fun x : E ↦ chi (rho⁻¹ • x)) ⊆ V := by
    have hrho_ne : rho ≠ 0 := ne_of_gt hrho_pos
    have htsupport : tsupport (fun x : E ↦ chi (rho⁻¹ • x)) =
        rho • tsupport (chi : E → ℝ) := by
      rw [tsupport, support_comp_inv_smul₀ hrho_ne, tsupport]
      exact closure_smul₀' hrho_ne _
    rw [htsupport]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    have hy_norm : ‖y‖ ≤ chi.rOut := by
      rw [chi.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hy
      exact hy
    apply hball_V
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hrho_pos]
    calc
      rho * ‖y‖ ≤ rho * chi.rOut :=
        mul_le_mul_of_nonneg_left hy_norm hrho_pos.le
      _ < supportScale * chi.rOut :=
        mul_lt_mul_of_pos_right hrho_supportScale chi.rOut_pos
      _ < rV := by
        dsimp only [supportScale]
        rw [div_mul_eq_mul_div]
        have hquotient : rV * chi.rOut < rV * (chi.rOut + 1) := by
          nlinarith [chi.rOut_pos, hrV_pos]
        exact (div_lt_iff₀ houtOne_pos).2 hquotient
  have hscaled_smooth : ContDiff ℝ nu (fun x : E ↦ chi (rho⁻¹ • x)) :=
    chi.contDiff.comp (contDiff_const_smul rho⁻¹)
  have hlinearized_smooth :
      ContDiff ℝ nu (LocalCutoff.linearize chi rho (0 : E →L[ℝ] G) N) :=
    LocalCutoff.contDiff_linearize nu chi rho 0 N V hV_open hV_nhds
      hscaled_smooth hN_on_V hscaled_support
  have hlinearized_eq_remainder :
      LocalCutoff.linearize chi rho (0 : E →L[ℝ] G) N =
        LocalCutoff.remainder chi rho N := by
    funext x
    simp only [LocalCutoff.linearize_apply, zero_apply, zero_add,
      LocalCutoff.remainder_apply]
  have hR_smooth : ContDiff ℝ nu (LocalCutoff.remainder chi rho N) := by
    rw [← hlinearized_eq_remainder]
    exact hlinearized_smooth
  have hR_deriv_bound : ∀ x,
      ‖fderiv ℝ (LocalCutoff.remainder chi rho N) x‖ ≤ (epsilon : ℝ) :=
    hdeltaD rho hrho_pos hrho_deltaD
  have hR_lipschitz : LipschitzWith epsilon (LocalCutoff.remainder chi rho N) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      (hR_smooth.differentiable (Nat.cast_ne_zero.mpr hnu_ne))
    intro x
    exact_mod_cast hR_deriv_bound x
  have hR_germ : LocalCutoff.remainder chi rho N =ᶠ[𝓝 0] N := by
    have hlinearized_germ := LocalCutoff.linearize_eventuallyEq
      chi rho (0 : E →L[ℝ] G) N chi.eventuallyEq_one
    filter_upwards [hlinearized_germ] with x hx
    simpa only [LocalCutoff.linearize_apply, zero_apply, zero_add,
      LocalCutoff.remainder_apply] using hx
  refine ⟨LocalCutoff.remainder chi rho N, hR_smooth, ?_, ?_, hR_lipschitz, hR_germ⟩
  · exact LocalCutoff.hasCompactSupport_remainder chi rho N (ne_of_gt hrho_pos)
      chi.hasCompactSupport
  · simp only [LocalCutoff.remainder_apply, smul_eq_zero, hN_zero, or_true]

end LocalInvariantGraph
