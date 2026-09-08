module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_2_3_Uniformly_convex_weak_Wolfe_DFP_counterexample_in_dimension_two
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_1_Isolation_radii_and_pairwise_disjoint_interpolation_balls
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_5_12a_Global_Hessian_bounds
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Proposition_5_14_The_realized_endpoint_sequence_is_the_exact_classical_DFP_orbit
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_6_7a_Master_choice_of_one_initial_scale_satisfying_all_smallness_requireme
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterConvergence
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Iteration
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ParameterizedWolfe
public import ReasLib.Optimization.DFP.StrongWolfeCounterexample
import Mathlib.Tactic.Abel

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP

/-- Helper for TASK-08: the planar strong-Wolfe certificate with fixed
quadratic bounds and symbolic line-search coefficients. -/
abbrev PlanarStrongWolfeCounterexample (c₁ c₂ : ℝ) :=
  DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂

/-- TASK-08: Parameterized planar strong-Wolfe assembly. The invariant
slow-curve construction supplies a planar certificate for every admissible
pair of symbolic Wolfe coefficients. -/
theorem existsPlanarStrongWolfeCounterexample
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁)
    (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    Nonempty (PlanarStrongWolfeCounterexample c₁ c₂) := by
  have hc₁_lt_c₂ : c₁ < c₂ :=
    lt_of_lt_of_le hc₁_lt_two_thirds hc₂_ge_two_thirds
  obtain ⟨p, h, _, _, _, h_invariant, h_pJet, h_hJet, _⟩ :=
    DFP.TwoLeg.exists_localForwardInvariantSlowCurve
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
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
  obtain ⟨ηArmijo, hηArmijo, hArmijoCurveAt⟩ :=
    DFP.TwoLeg.SlowCurve.endpointArmijo_of_lt_two_thirds curve
      hc₁_pos hc₁_lt_two_thirds
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
  have hεExact : ε₀ ∈ Set.Ioc 0 ηExact := ⟨hε₀.1, hεExactLe⟩
  have hεCenter : ε₀ ∈ Set.Ioc 0 ηCenter := ⟨hε₀.1, hεCenterLe⟩
  have hεAmplitude : ε₀ ∈ Set.Ioc 0 ηAmplitude := ⟨hε₀.1, hεAmplitudeLe⟩
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient := ⟨hε₀.1, hεGradientLe⟩
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius := ⟨hε₀.1, hεRadiusLe⟩
  have hεDisjoint : ε₀ ∈ Set.Ioc 0 ηDisjoint := ⟨hε₀.1, hεDisjointLe⟩
  have hεSmooth : ε₀ ∈ Set.Ioc 0 ηSmooth := ⟨hε₀.1, hεSmoothLe⟩
  have hεHessian : ε₀ ∈ Set.Ioc 0 ηHessian := ⟨hε₀.1, hεHessianLe⟩
  have hεArmijo : ε₀ ∈ Set.Ioc 0 ηArmijo := ⟨hε₀.1, hεArmijoLe⟩
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
          c₁ * inner ℝ (orbit.endpointGradient k)
            (orbit.endpoint (k + 1) - orbit.endpoint k) := by
    let orbitCurve :=
      DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
    have hCenterTendstoCurve :
        Tendsto
          (fun j : ℕ ↦ (orbitCurve.state j).center)
          atTop (𝓝 Clim) := by
      simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
        DFP.TwoLeg.SlowCurve.ofAsymptotics_high, orbitCurve] using
        hCenterTendsto
    have hRadiusCurve :
        ∀ n : ℕ,
          0 < (orbitCurve.interpolationRadius Clim Glim n) := by
      intro n
      simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
        DFP.TwoLeg.SlowCurve.ofAsymptotics_high, orbitCurve] using hRadius n
    have hDisjointCurve :
        Set.univ.PairwiseDisjoint (fun n : ℕ ↦
          Metric.closedBall (orbitCurve.endpoint n)
            (orbitCurve.interpolationRadius Clim Glim n)) := by
      simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
        DFP.TwoLeg.SlowCurve.ofAsymptotics_high, orbitCurve] using hDisjoint
    have hraw := hArmijoCurveAt ε₀ hεArmijo Clim hCenterTendstoCurve Glim
      hRadiusCurve hDisjointCurve k
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high,
      LineSearch.Wolfe.isArmijo_iff, orbit] using hraw
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
  have hGradient (k : ℕ) :
      HasGradientAt f (g k) (x k) := by
    simpa only [f, x, g] using
      DFP.TwoPhaseOrbit.realizedObjective_hasEndpointGradientAt
        orbit Clim Glim hRadius hDisjoint k
  have hEndpointWeakWolfe (k : ℕ) :
      LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k) := by
    have hraw :=
      DFP.TwoPhaseOrbit.endpointWeakWolfe_of_endpointData orbit hExact
        hc₁_pos hc₁_lt_c₂ hc₂_lt_one hc₂_ge_two_thirds
          Clim Glim hRadius hDisjoint hArmijo k
    simpa only [f, x] using hraw
  have hEndpointStrongWolfe (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ f (x k) (x (k + 1) - x k) := by
    have hraw :=
      DFP.TwoPhaseOrbit.endpointStrongWolfe_of_endpointData orbit hExact
        hc₁_pos hc₁_lt_c₂ hc₂_lt_one hGradient hArmijo
          hc₂_ge_two_thirds k
    simpa only [f, x] using hraw
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
      LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective,
      DFP.IsOrbit.toInverseIteration_point] using hEndpointWeakWolfe k
  have hIterationStrongWolfe (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ iteration.objective
        (iteration.point k) (iteration.point (k + 1) - iteration.point k) := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective,
      DFP.IsOrbit.toInverseIteration_point] using hEndpointStrongWolfe k
  have hIterationGradientNormTendsto :
      Tendsto
        (fun k ↦ ‖DFP.gradients iteration.objective iteration.point k‖)
        atTop (𝓝 gradientLimit) := by
    simpa only [iteration, DFP.IsOrbit.toInverseIteration_objective,
      DFP.IsOrbit.toInverseIteration_point_eq] using
      hGradientNormTendsto
  let weak : DFP.WolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂ :=
    { iteration := iteration
      gradientLimit := gradientLimit
      objectiveContDiff := hIterationContDiff
      stepLengthPos := hIterationStepPos
      hessianBounds := hIterationHessianBounds
      weakWolfe := hIterationWeakWolfe
      gradientLimitPos := hGradientLimit
      gradientNormTendsto := hIterationGradientNormTendsto }
  have hStrongForWeak (k : ℕ) :
      LineSearch.IsStrongWolfe c₁ c₂ weak.iteration.objective
        (weak.iteration.point k)
        (weak.iteration.point (k + 1) - weak.iteration.point k) := by
    simpa only [weak] using
      hIterationStrongWolfe k
  have strong : DFP.StrongWolfeCounterexample
      (Fin 2) (1 / 2) (3 / 2) c₁ c₂ :=
    DFP.StrongWolfeCounterexample.ofWeak weak hStrongForWeak
  exact ⟨strong⟩

end DFP
