module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_5_11_Global_realized_objective_Objective
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_8_Global_C_2_extension_of_the_disjoint_bump_sum
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_10_Global_Hessian_bound_for_the_bump_correction
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_29_Hessian_norm_bound_gives_Loewner_quadratic_form_bounds
import ReasLib.Analysis.Convex.HessianPerturbation.Bounds

public section

noncomputable section

open Filter Set
open scoped Asymptotics Matrix Topology

/-- Proposition 5.12a (Global Hessian bounds) (1): the realized objective
is globally twice continuously differentiable. -/
theorem contDiff_two_slowCurveRealizedObjective (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ContDiff ℝ 2 (orbit.realizedObjective Clim Glim) := by
  obtain ⟨εbar, hεbar, hBump⟩ :=
    contDiff_two_slowCurveBumpCorrection
      p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim Glim hGlim hGlimTendsto
  have hBumpData := hBump ε₀ hε₀ Clim hClim
    Glim hGlim hGlimTendsto
  have hObjective : orbit.realizedObjective Clim Glim = fun z ↦
      (1 / 2 : ℝ) * ‖z - Clim‖ ^ 2 + orbit.bumpCorrection Clim Glim z := by
    funext z
    exact DFP.TwoPhaseOrbit.realizedObjective_apply orbit Clim Glim z
  rw [hObjective]
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact HessianPerturbation.contDiffAt_halfNormSq_sub_add
    Clim (orbit.bumpCorrection Clim Glim) z hBumpData.contDiffAt

/-- Proposition 5.12a (Global Hessian bounds) (2): whenever
`K * ε₀ ≤ 1 / 2`, the Hessian of the realized objective lies globally between
`(1 / 2)I` and `(3 / 2)I`. -/
theorem slowCurveRealizedObjectiveHessianBounds (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Ioc 0 εbar, K * ε₀ ≤ 1 / 2 →
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ z : EuclideanSpace ℝ (Fin 2),
                  (EuclideanPlane.hessianMatrix (orbit.realizedObjective Clim Glim) z -
                    (1 / 2 : ℝ) • 1).PosSemidef ∧
                  ((3 / 2 : ℝ) • 1 -
                    EuclideanPlane.hessianMatrix
                      (orbit.realizedObjective Clim Glim) z).PosSemidef := by
  obtain ⟨ηBump, hηBump, hBump⟩ :=
    contDiff_two_slowCurveBumpCorrection
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηHessian, hηHessian, K, hK, hHessian⟩ :=
    slowCurveBumpCorrectionHessianBound
      p h h_invariant h_pJet h_hJet
  let εbar := min ηBump ηHessian
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηBump.1 hηHessian.1
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηBump.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, K, hK, ?_⟩
  intro ε₀ hε₀ hSmall
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεBump : ε₀ ∈ Ioc 0 ηBump :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεHessian : ε₀ ∈ Ioc 0 ηHessian :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hBumpData := hBump ε₀ hεBump Clim hClim
    Glim hGlim hGlimTendsto
  have hHessianData := hHessian ε₀ hεHessian Clim hClim
    Glim hGlim hGlimTendsto
  intro z
  have hNormHalf :
      ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ ≤ 1 / 2 :=
    (hHessianData z).trans hSmall
  have hBounds := EuclideanPlane.hessianMatrix_sqNorm_add_bounds_of_norm_le
    Clim (orbit.bumpCorrection Clim Glim) z (1 / 2 : ℝ)
      hBumpData.contDiffAt hNormHalf
  have hObjective : orbit.realizedObjective Clim Glim = fun x ↦
      (1 / 2 : ℝ) * ‖x - Clim‖ ^ 2 + orbit.bumpCorrection Clim Glim x := by
    funext x
    exact DFP.TwoPhaseOrbit.realizedObjective_apply orbit Clim Glim x
  rw [hObjective]
  norm_num at hBounds
  exact hBounds
