module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_5_12a_Global_Hessian_bounds
public import ReasLib.Analysis.Convex.EuclideanPlaneHessian

public section

noncomputable section

open Filter Set
open scoped Asymptotics Topology

/-- Corollary 5.12b (Global strong and uniform convexity): the realized objective is
globally `(1 / 2)`-strongly convex and therefore uniformly convex with quadratic modulus
`(fun r ↦ (1 / 2 : ℝ) / 2 * r ^ 2)`. -/
theorem slowCurveRealizedObjective_strongConvexOn (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Ioc 0 εbar, K * ε₀ ≤ 1 / 2 →
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                StrongConvexOn Set.univ (1 / 2) (orbit.realizedObjective Clim Glim) := by
  obtain ⟨ηSmooth, hηSmooth, hSmooth⟩ :=
    contDiff_two_slowCurveRealizedObjective
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηBounds, hηBounds, K, hK, hBounds⟩ :=
    slowCurveRealizedObjectiveHessianBounds
      p h h_invariant h_pJet h_hJet
  let εbar := min ηSmooth ηBounds
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηSmooth.1 hηBounds.1
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηSmooth.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, K, hK, ?_⟩
  intro ε₀ hε₀ hSmall
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεSmooth : ε₀ ∈ Ioc 0 ηSmooth :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεBounds : ε₀ ∈ Ioc 0 ηBounds :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hSmoothData := hSmooth ε₀ hεSmooth Clim hClim
    Glim hGlim hGlimTendsto
  have hBoundsData := hBounds ε₀ hεBounds hSmall Clim hClim
    Glim hGlim hGlimTendsto
  have hHalfPos : (0 : ℝ) < 1 / 2 := by
    norm_num
  refine EuclideanPlane.strongConvexOnOfHessianLowerBound
    (orbit.realizedObjective Clim Glim) (1 / 2 : ℝ)
      hSmoothData hHalfPos ?_
  intro x v
  have hLower := (EuclideanPlane.lowerBound_hessianMatrix_iff
    (orbit.realizedObjective Clim Glim) x (1 / 2 : ℝ)
      hSmoothData.contDiffAt).mp (hBoundsData x).1
  exact hLower v
