module

public import ReasLib.Analysis.Calculus.Gradient.Hessian.EuclideanPlane
public import ReasLib.Optimization.DFP.WolfeCounterexample
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_1_Isolation_radii_and_pairwise_disjoint_interpolation_balls
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_5_12a_Global_Hessian_bounds
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_5_14_The_realized_endpoint_sequence_is_the_exact_classical_DFP_orbit
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_6_7a_Master_choice_of_one_initial_scale_satisfying_all_smallness_requireme
import ReasLib.Optimization.DFP.Orbit
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve
import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterConvergence
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit
import ReasLib.Optimization.DFP.TwoPhaseOrbit.Iteration
import ReasLib.Optimization.DFP.TwoPhaseOrbit.Wolfe
import Mathlib.Tactic.Abel

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP

/-- A planar inverse-form DFP trajectory with the paper's fixed Hessian bounds and
weak-Wolfe constants whose gradient norms converge to a positive limit. -/
abbrev PlanarWeakWolfeCounterexample :=
  DFP.WolfeCounterexample (Fin 2) (1 / 2) (3 / 2) (1 / 4) (3 / 4)

/-- Theorem 2.3 (Uniformly convex weak-Wolfe DFP counterexample in dimension two):
there exists a globally `C²` planar objective with Hessian between `(1 / 2)I` and
`(3 / 2)I`, a well-defined positive-step inverse-form DFP trajectory satisfying weak
Wolfe with `(1 / 4, 3 / 4)`, and gradient norms tending to a positive limit. -/
theorem existsPlanarWeakWolfeCounterexample :
    Nonempty DFP.PlanarWeakWolfeCounterexample := by
  obtain ⟨p, h, _, _, _, h_invariant, h_pJet, h_hJet, _⟩ :=
    DFP.TwoLeg.exists_localForwardInvariantSlowCurve
  have h_oneEighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨ηExact, hηExact, hExactAt⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurveExact p h h_invariant h_pJet h_hJet
      (1 / 8) h_oneEighth
  obtain ⟨ηCenter, hηCenter, hCenterAt⟩ :=
    DFP.TwoPhaseOrbit.slowCurveCenterTendsto
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmplitude, hηAmplitude, hAmplitudeAt⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeExistsPositiveLimit
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGradient, hηGradient, hGradientAt⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointGradientNormTendsto
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηRadius, hηRadius, cLower, hcLower, cUpper, hcUpper, hRadiusAt⟩ :=
    slowCurveInterpolationRadiusUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηDisjoint, hηDisjoint, hDisjointAt⟩ :=
    slowCurvePairwiseDisjointInterpolationClosedBalls
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηSmooth, hηSmooth, hSmoothAt⟩ :=
    contDiff_two_slowCurveRealizedObjective
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηHessian, hηHessian, K, hK, hHessianAt⟩ :=
    slowCurveRealizedObjectiveHessianBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηArmijo, hηArmijo, hArmijoAt⟩ :=
    DFP.TwoPhaseOrbit.slowCurveArmijo p h h_invariant h_pJet h_hJet
  let threshold : Fin 9 → ℝ :=
    ![ηExact, ηCenter, ηAmplitude, ηGradient, ηRadius, ηDisjoint,
      ηSmooth, ηHessian, ηArmijo]
  have h_threshold (i : Fin 9) : 0 < threshold i := by
    fin_cases i <;>
      simp [threshold, hηExact.1, hηCenter.1, hηAmplitude, hηGradient,
        hηRadius.1, hηDisjoint.1, hηSmooth.1, hηHessian.1, hηArmijo.1]
  obtain ⟨ε₀, hε₀, hεThreshold⟩ :=
    existsCommonInitialScale threshold K h_threshold hK
  have hεExactLe : ε₀ ≤ ηExact := by
    simpa [threshold] using hεThreshold (0 : Fin 9)
  have hεCenterLe : ε₀ ≤ ηCenter := by
    simpa [threshold] using hεThreshold (1 : Fin 9)
  have hεAmplitudeLe : ε₀ ≤ ηAmplitude := by
    simpa [threshold] using hεThreshold (2 : Fin 9)
  have hεGradientLe : ε₀ ≤ ηGradient := by
    simpa [threshold] using hεThreshold (3 : Fin 9)
  have hεRadiusLe : ε₀ ≤ ηRadius := by
    simpa [threshold] using hεThreshold (4 : Fin 9)
  have hεDisjointLe : ε₀ ≤ ηDisjoint := by
    simpa [threshold] using hεThreshold (5 : Fin 9)
  have hεSmoothLe : ε₀ ≤ ηSmooth := by
    simpa [threshold] using hεThreshold (6 : Fin 9)
  have hεHessianLe : ε₀ ≤ ηHessian := by
    simpa [threshold] using hεThreshold (7 : Fin 9)
  have hεArmijoLe : ε₀ ≤ ηArmijo := by
    simpa [threshold] using hεThreshold (8 : Fin 9)
  have hεExact : ε₀ ∈ Set.Ioc 0 ηExact :=
    ⟨hε₀.1, hεExactLe⟩
  have hεCenter : ε₀ ∈ Set.Ioc 0 ηCenter :=
    ⟨hε₀.1, hεCenterLe⟩
  have hεAmplitude : ε₀ ∈ Set.Ioc 0 ηAmplitude :=
    ⟨hε₀.1, hεAmplitudeLe⟩
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient :=
    ⟨hε₀.1, hεGradientLe⟩
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hεRadiusLe⟩
  have hεDisjoint : ε₀ ∈ Set.Ioc 0 ηDisjoint :=
    ⟨hε₀.1, hεDisjointLe⟩
  have hεSmooth : ε₀ ∈ Set.Ioc 0 ηSmooth :=
    ⟨hε₀.1, hεSmoothLe⟩
  have hεHessian : ε₀ ∈ Set.Ioc 0 ηHessian :=
    ⟨hε₀.1, hεHessianLe⟩
  have hεArmijo : ε₀ ∈ Set.Ioc 0 ηArmijo :=
    ⟨hε₀.1, hεArmijoLe⟩
  have hHessianSmall : K * ε₀ ≤ 1 / 2 := by
    calc
      K * ε₀ ≤ K * (2 * K)⁻¹ :=
        mul_le_mul_of_nonneg_left hε₀.2 hK.le
      _ = 1 / 2 := by
        field_simp [ne_of_gt hK]
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hExact (j : ℕ) :
      DFP.TwoPhaseOrbit.State.ExactCycle (orbit.state j) := by
    simpa only [orbit] using hExactAt ε₀ hεExact j
  have hCenterExists : ∃ Clim : EuclideanSpace ℝ (Fin 2),
      Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) := by
    simpa only [orbit] using hCenterAt ε₀ hεCenter
  obtain ⟨Clim, hCenterTendsto⟩ := hCenterExists
  have hAmplitudeExists : ∃ Glim > 0,
      Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) := by
    simpa only [orbit] using hAmplitudeAt ε₀ hεAmplitude
  obtain ⟨Glim, hGlim, hAmplitudeTendsto⟩ := hAmplitudeExists
  have hGradientExists : ∃ gradientLimit > 0,
      Tendsto (fun k : ℕ ↦ ‖orbit.endpointGradient k‖) atTop
        (𝓝 gradientLimit) := by
    simpa only [orbit] using hGradientAt ε₀ hεGradient
  obtain ⟨gradientLimit, hGradientLimit, hEndpointGradientTendsto⟩ :=
    hGradientExists
  have hRadiusBounds (k : ℕ) : orbit.interpolationRadius Clim Glim k ∈ Set.Icc
      (cLower * (orbit.state (k / 2)).ε ^ 2)
      (cUpper * (orbit.state (k / 2)).ε ^ 2) := by
    simpa only [orbit] using hRadiusAt ε₀ hεRadius Clim hCenterTendsto
      Glim hGlim hAmplitudeTendsto k
  have hRadius (k : ℕ) : 0 < orbit.interpolationRadius Clim Glim k := by
    have hscalePos : 0 < (orbit.state (k / 2)).ε :=
      (hExact (k / 2)).valid.ε_pos
    have hlower : 0 < cLower * (orbit.state (k / 2)).ε ^ 2 :=
      mul_pos hcLower (pow_pos hscalePos 2)
    exact hlower.trans_le (hRadiusBounds k).1
  have hDisjoint : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius Clim Glim k)) := by
    simpa only [orbit] using hDisjointAt ε₀ hεDisjoint Clim hCenterTendsto
      Glim hGlim hAmplitudeTendsto
  have hObjectiveContDiff : ContDiff ℝ 2 (orbit.realizedObjective Clim Glim) := by
    simpa only [orbit] using hSmoothAt ε₀ hεSmooth Clim hCenterTendsto
      Glim hGlim hAmplitudeTendsto
  have hHessianBounds (z : EuclideanSpace ℝ (Fin 2)) :
      (EuclideanPlane.hessianMatrix (orbit.realizedObjective Clim Glim) z -
          (1 / 2 : ℝ) • 1).PosSemidef ∧
        ((3 / 2 : ℝ) • 1 -
          EuclideanPlane.hessianMatrix
            (orbit.realizedObjective Clim Glim) z).PosSemidef := by
    simpa only [orbit] using hHessianAt ε₀ hεHessian hHessianSmall
      Clim hCenterTendsto Glim hGlim hAmplitudeTendsto z
  have hArmijo (k : ℕ) :
      orbit.realizedObjective Clim Glim (orbit.endpoint (k + 1)) ≤
        orbit.realizedObjective Clim Glim (orbit.endpoint k) +
          (1 / 4 : ℝ) * inner ℝ (orbit.endpointGradient k)
            (orbit.endpoint (k + 1) - orbit.endpoint k) := by
    simpa only [orbit] using hArmijoAt ε₀ hεArmijo Clim hCenterTendsto
      Glim hRadius hDisjoint k
  have hOrbit := DFP.TwoPhaseOrbit.realizedObjective_isOrbit
    orbit Clim Glim hExact hRadius hDisjoint
  let f := orbit.realizedObjective Clim Glim
  let α := orbit.endpointStepLength hExact
  let x := orbit.endpoint
  let g := orbit.endpointGradient
  let H := orbit.endpointMetric
  have hOrbitData : DFP.IsOrbit f α x g H := by
    simpa only [f, α, x, g, H] using hOrbit
  have hGradients : DFP.gradients f x = g :=
    hOrbitData.gradients_eq
  have hPosDef (k : ℕ) : (H k).PosDef := by
    simpa only [H] using
      DFP.TwoPhaseOrbit.endpointMetric_posDef orbit hExact k
  have hSecantPositive (k : ℕ) :
      0 < inner ℝ (g (k + 1) - g k) (x (k + 1) - x k) := by
    simpa only [g, x] using
      DFP.TwoPhaseOrbit.endpointSecantCurvature_pos orbit hExact k
  have hSecantDenominator : ∀ k,
      WithLp.ofLp (DFP.steps α (DFP.directions H g) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges g k) ≠ 0 :=
    hOrbitData.secantDenominator_ne_of_secantCurvature_pos hSecantPositive
  have hWeakCurvature (k : ℕ) :
      (3 / 4 : ℝ) * inner ℝ (g k) (x (k + 1) - x k) ≤
        inner ℝ (g (k + 1)) (x (k + 1) - x k) := by
    exact LineSearch.Wolfe.isWeakCurvature_iff.mp (by
      simpa only [g, x] using
        DFP.TwoPhaseOrbit.endpointWeakCurvature orbit hExact k)
  have hWeakWolfe (k : ℕ) : LineSearch.IsWeakWolfe (1 / 4) (3 / 4)
      f (x k) (x (k + 1) - x k) := by
    have hnextPoint : x k + (x (k + 1) - x k) = x (k + 1) := by
      abel
    have hGradientNext : HasGradientAt f (g (k + 1))
        (x k + (x (k + 1) - x k)) := by
      rw [hnextPoint]
      exact hOrbitData.gradientAt (k + 1)
    have hArmijoData :
        f (x (k + 1)) ≤ f (x k) +
          (1 / 4 : ℝ) * inner ℝ (g k) (x (k + 1) - x k) := by
      simpa only [f, x, g] using hArmijo k
    have hArmijoForStep :
        f (x k + (x (k + 1) - x k)) ≤ f (x k) +
          (1 / 4 : ℝ) * inner ℝ (g k) (x (k + 1) - x k) := by
      rw [hnextPoint]
      exact hArmijoData
    exact LineSearch.IsWeakWolfe.ofHasGradientAtSelectedConstants
      (hOrbitData.gradientAt k) hGradientNext hArmijoForStep (hWeakCurvature k)
  have hGradientNormTendsto :
      Tendsto (fun k : ℕ ↦ ‖DFP.gradients f x k‖) atTop
        (𝓝 gradientLimit) := by
    rw [hGradients]
    simpa only [g] using hEndpointGradientTendsto
  let iteration : DFP.InverseIteration (Fin 2) :=
    hOrbitData.toInverseIteration hPosDef hSecantDenominator
  have hIterationContDiff : ContDiff ℝ 2 iteration.objective := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective, f] using
      hObjectiveContDiff
  have hIterationStepPos (k : ℕ) : 0 < iteration.stepLength k := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_stepLength] using
      hOrbitData.stepLengthPos k
  have hIterationHessianLower (z : EuclideanSpace ℝ (Fin 2)) :
      (EuclideanPlane.hessianMatrix iteration.objective z -
        (1 / 2 : ℝ) • 1).PosSemidef := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective, f] using
      (hHessianBounds z).1
  have hIterationHessianUpper (z : EuclideanSpace ℝ (Fin 2)) :
      ((3 / 2 : ℝ) • 1 -
        EuclideanPlane.hessianMatrix iteration.objective z).PosSemidef := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective, f] using
      (hHessianBounds z).2
  have hIterationHessianBounds :
      HasHessianBounds (1 / 2 : ℝ) (3 / 2 : ℝ) iteration.objective := by
    exact (EuclideanPlane.hasHessianBounds_iff_hessianMatrix
      hIterationContDiff).2 fun z ↦
        ⟨hIterationHessianLower z, hIterationHessianUpper z⟩
  have hIterationWeakWolfe (k : ℕ) :
      LineSearch.IsWeakWolfe (1 / 4) (3 / 4) iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective,
      DFP.IsOrbit.toInverseIteration_point] using hWeakWolfe k
  have hIterationGradientNormTendsto :
      Tendsto
        (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
        atTop (𝓝 gradientLimit) := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective,
      DFP.IsOrbit.toInverseIteration_point_eq] using
      hGradientNormTendsto
  let counterexample : PlanarWeakWolfeCounterexample :=
    DFP.WolfeCounterexample.ofIteration iteration gradientLimit
      hIterationContDiff hIterationStepPos hIterationHessianBounds
      hIterationWeakWolfe hGradientLimit
      hIterationGradientNormTendsto
  exact ⟨counterexample⟩

end DFP
