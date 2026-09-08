module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Wolfe
public import ReasLib.Optimization.DFP.AbstractSecantStep.Wolfe.DiscreteRatio
public import ReasLib.Optimization.LineSearch
import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport

/-!
# Parameterized Wolfe endpoint certificates

The Armijo estimate below uses the existing uniform error bounds with a scale
chosen from the positive margin `2 / 3 - c₁`; it therefore retains the
two-thirds asymptotic limit rather than reducing to the old fixed coefficient.
The curvature transport is exact because each phase ratio is exactly `1 / 3`
or `2 / 3`.
-/

public section

noncomputable section

open Filter
open scoped Matrix
open scoped Asymptotics Topology

namespace DFP.TwoLeg.SlowCurve

/-- Infrastructure I.16a: the realized decrease ratio approaches the two-phase
limit from below uniformly for every first Wolfe coefficient strictly below
`2 / 3`. -/
theorem phaseDecreaseRatioLowerBound_of_lt_two_thirds
    (curve : DFP.TwoLeg.SlowCurve) {c₁ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ G : ℝ,
            (∀ n : ℕ, 0 < orbit.interpolationRadius Clim G n) →
              Set.univ.PairwiseDisjoint (fun n : ℕ ↦
                Metric.closedBall (orbit.endpoint n)
                  (orbit.interpolationRadius Clim G n)) →
                ∀ j : ℕ, ∀ i : Fin 2,
                  let k := 2 * j + i.val
                  let s := orbit.endpoint (k + 1) - orbit.endpoint k
                  let q := -inner ℝ (orbit.endpointGradient k) s
                  0 < q ∧
                    c₁ ≤
                      (orbit.realizedObjective Clim G (orbit.endpoint k) -
                        orbit.realizedObjective Clim G (orbit.endpoint (k + 1))) / q := by
  obtain ⟨ηQ, hηQ, cQ, hcQ, CQ, hCQ, hQ⟩ :=
    DFP.TwoLeg.SlowCurve.phasePredictedDecreaseUniformBounds curve
  obtain ⟨ηRatio, hηRatio, Kratio, hKratio, hRatio⟩ :=
    DFP.TwoLeg.SlowCurve.phaseStepRatioUniformBound curve
  obtain ⟨ηCorr, hηCorr, Kcorr, hKcorr, hCorr⟩ :=
    DFP.TwoLeg.SlowCurve.phaseCorrectionRatioUniformBound curve
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph curve.shape curve.high
      curve.isInvariant curve.shapeRemainder curve.highRemainder
  let margin : ℝ := 2 / 3 - c₁
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith
  let errorCoeff : ℝ := Kratio / 2 + Kcorr
  have htwoPos : (0 : ℝ) < 2 := by norm_num
  have hhalfKratio : 0 < Kratio / 2 := div_pos hKratio htwoPos
  have herrorCoeff : 0 < errorCoeff := by
    dsimp only [errorCoeff]
    exact add_pos hhalfKratio hKcorr
  let ηErr : ℝ := margin / errorCoeff
  have hηErr : 0 < ηErr := by
    dsimp only [ηErr]
    exact div_pos hmargin herrorCoeff
  let εbar := min ηQ (min ηRatio (min ηCorr (min ηGraph ηErr)))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηQ.1
      (lt_min hηRatio.1 (lt_min hηCorr.1 (lt_min hηGraph.1 hηErr)))
  have hεbarLt : εbar < 1 / 4 :=
    (min_le_left _ _).trans_lt hηQ.2
  have hεbarQ : εbar ≤ ηQ := min_le_left _ _
  have hεbarRatio : εbar ≤ ηRatio :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεbarCorr : εbar ≤ ηCorr :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarGraph : εbar ≤ ηGraph :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarErr : εbar ≤ ηErr :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεQ : ε₀ ∈ Set.Ioc (0 : ℝ) ηQ :=
    ⟨hε₀.1, hε₀.2.trans hεbarQ⟩
  have hεRatio : ε₀ ∈ Set.Ioc (0 : ℝ) ηRatio :=
    ⟨hε₀.1, hε₀.2.trans hεbarRatio⟩
  have hεCorr : ε₀ ∈ Set.Ioc (0 : ℝ) ηCorr :=
    ⟨hε₀.1, hε₀.2.trans hεbarCorr⟩
  have hεGraph : ε₀ ∈ Set.Ioc (0 : ℝ) ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbarGraph⟩
  have hεErr : ε₀ ≤ ηErr := hε₀.2.trans hεbarErr
  intro Clim hClim G hRadius hDisjoint j i
  let k := 2 * j + i.val
  let s := orbit.endpoint (k + 1) - orbit.endpoint k
  let q := -inner ℝ (orbit.endpointGradient k) s
  let r := orbit.endpointRadius k
  let εj := (orbit.state j).ε
  have hcoord :
      (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, curve.shape ε₀, curve.high ε₀) := by
    simpa only [orbit] using
      DFP.TwoPhaseOrbit.ofSlowCurve_coordinates curve.shape curve.high ε₀ j
  have hεeq :
      εj = (DFP.TwoLeg.stateMap^[j] (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    dsimp only [εj]
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hcoord
  have hεjMem : εj ∈ Set.Ioc (0 : ℝ) ε₀ := by
    rw [hεeq]
    exact (hGraph ε₀ hεGraph j).2
  have hεjErr : εj ≤ ηErr := hεjMem.2.trans hεErr
  have hkdiv : k / 2 = j := by
    dsimp only [k]
    fin_cases i
    · omega
    · omega
  have hr : r = εj ^ 2 := by
    dsimp only [r, εj]
    rw [DFP.TwoPhaseOrbit.endpointRadius_def, hkdiv]
  have hqBounds :
      q ∈ Set.Icc (cQ * r ^ 2) (CQ * r ^ 2) := by
    have hraw := hQ ε₀ hεQ j i
    simpa only [orbit, k, s, q, r] using hraw
  have hrPos : 0 < r := by
    rw [hr]
    exact pow_pos hεjMem.1 2
  have hqPos : 0 < q :=
    (mul_pos hcQ (pow_pos hrPos 2)).trans_le hqBounds.1
  have hstepRatio :
      |‖s‖ ^ 2 / q - (TwoPhaseControls.phase εj i).tau| ≤ Kratio * εj := by
    have hraw := hRatio ε₀ hεRatio j i
    simpa only [orbit, k, s, q, εj] using hraw
  have hcorrRatio :
      |inner ℝ (orbit.endpointCorrection Clim k) s / q| ≤ Kcorr * εj := by
    have hraw := hCorr ε₀ hεCorr Clim hClim j i
    simpa only [orbit, k, s, q, εj] using hraw
  have hidentity :
      (orbit.realizedObjective Clim G (orbit.endpoint k) -
          orbit.realizedObjective Clim G (orbit.endpoint (k + 1))) / q =
        1 - ‖s‖ ^ 2 / (2 * q) +
          inner ℝ (orbit.endpointCorrection Clim k) s / q := by
    simpa only [s, q] using
      DFP.TwoPhaseOrbit.realizedObjective_decreaseRatio
        orbit Clim G hRadius hDisjoint k hqPos
  have hhalf :
      ‖s‖ ^ 2 / (2 * q) = (1 / 2 : ℝ) * (‖s‖ ^ 2 / q) := by
    field_simp [ne_of_gt hqPos]
  have hstepUpper := (abs_le.mp hstepRatio).2
  have hcorrLower := (abs_le.mp hcorrRatio).1
  have htau : (TwoPhaseControls.phase εj i).tau ≤ (2 / 3 : ℝ) := by
    rcases TwoPhaseControls.phase_tau_mem εj i with hτ | hτ
    · rw [hτ]
    · rw [hτ]
      norm_num
  have herr : errorCoeff * εj ≤ margin := by
    calc
      errorCoeff * εj ≤ errorCoeff * ηErr :=
        mul_le_mul_of_nonneg_left hεjErr herrorCoeff.le
      _ = margin := by
        dsimp only [ηErr]
        field_simp [ne_of_gt herrorCoeff]
  have herr' : (Kratio / 2 + Kcorr) * εj ≤ margin := by
    simpa only [errorCoeff] using herr
  have herrExpanded : Kratio / 2 * εj + Kcorr * εj ≤ margin := by
    calc
      Kratio / 2 * εj + Kcorr * εj = (Kratio / 2 + Kcorr) * εj := by ring
      _ ≤ margin := herr'
  dsimp only [margin] at herrExpanded
  have hstepHalf :
      (1 / 2 : ℝ) * (‖s‖ ^ 2 / q) ≤
        (1 / 2 : ℝ) * (TwoPhaseControls.phase εj i).tau + Kratio / 2 * εj := by
    nlinarith [hstepUpper]
  have htauHalf :
      (1 / 2 : ℝ) * (TwoPhaseControls.phase εj i).tau ≤ 1 / 3 := by
    linarith [htau]
  constructor
  · exact hqPos
  · rw [hidentity, hhalf]
    linarith [hstepHalf, htauHalf, hcorrLower, herrExpanded, hc₁_pos]

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoPhaseOrbit

/-- Helper for Infrastructure I.16a: special-orthogonal phase transport preserves
the Euclidean pairings used by the endpoint Wolfe certificates. -/
theorem inner_toLp_mulVec_eq_of_specialOrthogonal
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (u v : Fin 2 → ℝ) :
    inner ℝ (WithLp.toLp 2 (R *ᵥ u)) (WithLp.toLp 2 (R *ᵥ v)) = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using
    Matrix.dotProduct_mulVec_eq_of_mem_specialOrthogonalGroup R hR v u

/-- Helper for Infrastructure I.16a: the two physical endpoint pairings of a
phase are the slope and next-slope of its abstract secant step. -/
theorem endpointPhaseSlope_transport
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ) (i : Fin 2)
    (h : State.ExactCycle (orbit.state j)) :
    let k := 2 * j + i.val
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    inner ℝ (orbit.endpointGradient k) d = (h.step i).slope ∧
      inner ℝ (orbit.endpointGradient (k + 1)) d = (h.step i).nextSlope := by
  dsimp only
  constructor
  · rw [endpointGradient_eq_exactStepTransport orbit j i h,
      endpointStep_eq_exactStepTransport orbit j i h]
    rw [DFP.AbstractSecantStep.slope_def]
    exact inner_toLp_mulVec_eq_of_specialOrthogonal
      ((orbit.state j).phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).gradient (h.step i).displacement
  · rw [endpointGradient_succ_eq_exactStepTransport orbit j i h,
      endpointStep_eq_exactStepTransport orbit j i h]
    rw [DFP.AbstractSecantStep.nextSlope_def]
    exact inner_toLp_mulVec_eq_of_specialOrthogonal
      ((orbit.state j).phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).nextGradient (h.step i).displacement

/-- Infrastructure I.16a: every exact phase has strong-Wolfe curvature for any
`c₂` with `2 / 3 ≤ c₂`, using the exact phase ratios. -/
theorem endpointPhaseStrongCurvature_of_ge_two_thirds
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ) (i : Fin 2)
    (h : State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) :
    let k := 2 * j + i.val
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsStrongCurvature c₂
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  dsimp only
  obtain ⟨hstart, hnext⟩ := endpointPhaseSlope_transport orbit j i h
  rw [hstart, hnext]
  exact DFP.AbstractSecantStep.strongCurvature_of_tau_values
    (h.step i) (h.step_tau_mem i) hc₂

/-- Infrastructure I.16a: every exact phase has weak-Wolfe curvature for any
`c₂` in the paper's range, again using the exact phase ratios. -/
theorem endpointPhaseWeakCurvature_of_ge_two_thirds
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ) (i : Fin 2)
    (h : State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) :
    let k := 2 * j + i.val
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature c₂
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  dsimp only
  obtain ⟨hstart, hnext⟩ := endpointPhaseSlope_transport orbit j i h
  rw [hstart, hnext]
  apply (h.step i).weakCurvature
  rcases h.step_tau_mem i with hτ | hτ
  · rw [hτ]
    linarith
  · rw [hτ]
    linarith

/-- Infrastructure I.16a: every flattened exact-cycle endpoint has strong-Wolfe
curvature for all coefficients `c₂ ≥ 2 / 3`. -/
theorem endpointStrongCurvature_of_ge_two_thirds
    (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsStrongCurvature c₂
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa only [Fin.val_zero, add_zero] using
      endpointPhaseStrongCurvature_of_ge_two_thirds orbit j (0 : Fin 2)
        (h_exact j) hc₂
  · simpa only [Fin.val_one] using
      endpointPhaseStrongCurvature_of_ge_two_thirds orbit j (1 : Fin 2)
        (h_exact j) hc₂

/-- Infrastructure I.16a: every flattened exact-cycle endpoint has weak-Wolfe
curvature for all coefficients `c₂ ≥ 2 / 3`. -/
theorem endpointWeakCurvature_of_ge_two_thirds
    (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature c₂
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa only [Fin.val_zero, add_zero] using
      endpointPhaseWeakCurvature_of_ge_two_thirds orbit j (0 : Fin 2)
        (h_exact j) hc₂
  · simpa only [Fin.val_one] using
      endpointPhaseWeakCurvature_of_ge_two_thirds orbit j (1 : Fin 2)
        (h_exact j) hc₂

/-- Infrastructure I.16a: the endpoint strong/weak curvature certificates are
available together for every `c₂ ≥ 2 / 3`. -/
theorem endpointCurvatureCertificates_of_ge_two_thirds
    (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsStrongCurvature c₂
        (inner ℝ (orbit.endpointGradient k) d)
        (inner ℝ (orbit.endpointGradient (k + 1)) d) ∧
      LineSearch.Wolfe.IsWeakCurvature c₂
        (inner ℝ (orbit.endpointGradient k) d)
        (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  constructor
  · exact endpointStrongCurvature_of_ge_two_thirds orbit h_exact hc₂ k
  · exact endpointWeakCurvature_of_ge_two_thirds orbit h_exact hc₂ k

/-- Helper for Infrastructure I.16a: the flattened strong-curvature theorem in
the absolute-inequality form consumed by gradient-facing strong-Wolfe APIs. -/
theorem endpointStrongCurvature_inequality_of_ge_two_thirds
    (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) {c₂ : ℝ}
    (hc₂ : (2 / 3 : ℝ) ≤ c₂) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    |inner ℝ (orbit.endpointGradient (k + 1)) d| ≤
      c₂ * |inner ℝ (orbit.endpointGradient k) d| := by
  exact LineSearch.Wolfe.isStrongCurvature_iff.mp
    (endpointStrongCurvature_of_ge_two_thirds orbit h_exact hc₂ k)

/-- Helper for Infrastructure I.16a: the endpoint gradient certificate of the
realized objective can be expressed with the orbit's prescribed gradient. -/
theorem realizedObjective_hasEndpointGradientAt
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n)
        (orbit.interpolationRadius C G n))) (k : ℕ) :
    HasGradientAt (orbit.realizedObjective C G) (orbit.endpointGradient k)
      (orbit.endpoint k) := by
  have hraw := realizedObjective_hasGradientAt_endpoint orbit C G
    h_radius h_disjoint k
  have hvector :
      orbit.endpoint k - C + orbit.endpointCorrection C k =
        orbit.endpointGradient k := by
    rw [endpointCorrection_def]
    abel
  rw [hvector] at hraw
  exact hraw

/-- Infrastructure I.16a: an endpoint Armijo inequality together with the
parameterized exact-cycle curvature certificate constructs the gradient-facing
weak-Wolfe predicate used by downstream iteration consumers. -/
theorem endpointWeakWolfe_of_endpointData
    (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j))
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁) (hc₁_lt_c₂ : c₁ < c₂)
    (hc₂_lt_one : c₂ < 1) (hc₂ : (2 / 3 : ℝ) ≤ c₂)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (h_radius : ∀ n : ℕ, 0 < orbit.interpolationRadius C G n)
    (h_disjoint : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall (orbit.endpoint n)
        (orbit.interpolationRadius C G n)))
    (hArmijo : ∀ k : ℕ,
      orbit.realizedObjective C G (orbit.endpoint (k + 1)) ≤
        orbit.realizedObjective C G (orbit.endpoint k) +
          c₁ * inner ℝ (orbit.endpointGradient k)
            (orbit.endpoint (k + 1) - orbit.endpoint k))
    (k : ℕ) :
    LineSearch.IsWeakWolfe c₁ c₂ (orbit.realizedObjective C G)
      (orbit.endpoint k) (orbit.endpoint (k + 1) - orbit.endpoint k) := by
  have hsum : orbit.endpoint k +
      (orbit.endpoint (k + 1) - orbit.endpoint k) = orbit.endpoint (k + 1) := by
    abel
  have hgradient : HasGradientAt (orbit.realizedObjective C G)
      (orbit.endpointGradient k) (orbit.endpoint k) :=
    realizedObjective_hasEndpointGradientAt orbit C G h_radius h_disjoint k
  have hgradientNext : HasGradientAt (orbit.realizedObjective C G)
      (orbit.endpointGradient (k + 1))
      (orbit.endpoint k + (orbit.endpoint (k + 1) - orbit.endpoint k)) := by
    rw [hsum]
    exact realizedObjective_hasEndpointGradientAt orbit C G h_radius h_disjoint (k + 1)
  have hcurvature :
      LineSearch.Wolfe.IsWeakCurvature c₂
        (inner ℝ (orbit.endpointGradient k)
          (orbit.endpoint (k + 1) - orbit.endpoint k))
        (inner ℝ (orbit.endpointGradient (k + 1))
          (orbit.endpoint (k + 1) - orbit.endpoint k)) :=
    endpointWeakCurvature_of_ge_two_thirds orbit h_exact hc₂ k
  apply LineSearch.IsWeakWolfe.ofHasGradientAt
    hc₁_pos hc₁_lt_c₂ hc₂_lt_one hgradient hgradientNext
  · simpa only [hsum] using hArmijo k
  · exact LineSearch.Wolfe.isWeakCurvature_iff.mp hcurvature

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Infrastructure I.16a: the endpoint Armijo inequality inherits any coefficient
`c₁` in the open interval `(0, 2 / 3)` from the uniform phase estimate. -/
theorem endpointArmijo_of_lt_two_thirds
    (curve : DFP.TwoLeg.SlowCurve) {c₁ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ G : ℝ,
            (∀ n : ℕ, 0 < orbit.interpolationRadius Clim G n) →
              Set.univ.PairwiseDisjoint (fun n : ℕ ↦
                Metric.closedBall (orbit.endpoint n)
                  (orbit.interpolationRadius Clim G n)) →
                ∀ k : ℕ,
                  let s := orbit.endpoint (k + 1) - orbit.endpoint k
                  LineSearch.Wolfe.IsArmijo c₁
                    (orbit.realizedObjective Clim G (orbit.endpoint k))
                    (orbit.realizedObjective Clim G (orbit.endpoint (k + 1)))
                    (inner ℝ (orbit.endpointGradient k) s) := by
  obtain ⟨εbar, hεbar, hRatio⟩ :=
    DFP.TwoLeg.SlowCurve.phaseDecreaseRatioLowerBound_of_lt_two_thirds
      curve hc₁_pos hc₁_lt_two_thirds
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim G hRadius hDisjoint k
  have hphase :
      let s := orbit.endpoint (k + 1) - orbit.endpoint k
      let q := -inner ℝ (orbit.endpointGradient k) s
      0 < q ∧ c₁ ≤
        (orbit.realizedObjective Clim G (orbit.endpoint k) -
          orbit.realizedObjective Clim G (orbit.endpoint (k + 1))) / q := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simpa only [Fin.val_zero, add_zero] using
        hRatio ε₀ hε₀ Clim hClim G hRadius hDisjoint j (0 : Fin 2)
    · simpa only [Fin.val_one] using
        hRatio ε₀ hε₀ Clim hClim G hRadius hDisjoint j (1 : Fin 2)
  dsimp only at hphase ⊢
  apply LineSearch.Wolfe.IsArmijo.of_decreaseRatio
  · linarith [hphase.1]
  · exact hphase.2

end DFP.TwoLeg.SlowCurve
