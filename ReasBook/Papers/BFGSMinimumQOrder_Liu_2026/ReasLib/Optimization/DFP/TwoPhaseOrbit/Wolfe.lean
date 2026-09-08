module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Wolfe
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle.Transport
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective.DecreaseRatio
public import ReasLib.Optimization.DFP.TwoPhaseControls.LineRatio
import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport

public section

noncomputable section

open Filter
open scoped Matrix
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit.State.ExactCycle

/-- Every phase of an exact cycle satisfies the weak-Wolfe curvature condition
with curvature constant `3 / 4`. -/
theorem step_weakCurvature {s : State} (h : ExactCycle s) (i : Fin 2) :
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
      (h.step i).slope (h.step i).nextSlope := by
  rcases h.step_tau_mem i with hτ | hτ
  · apply (h.step i).weakCurvature
    rw [hτ]
    norm_num
  · apply (h.step i).weakCurvature
    rw [hτ]
    norm_num

end DFP.TwoPhaseOrbit.State.ExactCycle

namespace DFP.TwoPhaseOrbit

/-- Orthogonal transport preserves the Euclidean inner product of two
coordinate vectors. -/
private theorem inner_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (u v : Fin 2 → ℝ) :
    inner ℝ (WithLp.toLp 2 (R *ᵥ u)) (WithLp.toLp 2 (R *ᵥ v)) = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using
    Matrix.dotProduct_mulVec_eq_of_mem_specialOrthogonalGroup R hR v u

/-- A selected exact phase transports its abstract weak-Wolfe and positive
secant-curvature certificates to the corresponding physical endpoint step. -/
private theorem endpointPhaseCurvatureCertificates
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ) (i : Fin 2)
    (h : State.ExactCycle (orbit.state j)) :
    let k := 2 * j + i.val
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
        (inner ℝ (orbit.endpointGradient k) d)
        (inner ℝ (orbit.endpointGradient (k + 1)) d) ∧
      0 < inner ℝ
        (orbit.endpointGradient (k + 1) - orbit.endpointGradient k) d := by
  dsimp only
  have hstart :
      inner ℝ (orbit.endpointGradient (2 * j + i.val))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)) =
        (h.step i).slope := by
    rw [endpointGradient_eq_exactStepTransport orbit j i h,
      endpointStep_eq_exactStepTransport orbit j i h]
    rw [DFP.AbstractSecantStep.slope_def]
    exact inner_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
      ((orbit.state j).phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).gradient (h.step i).displacement
  have hnext :
      inner ℝ (orbit.endpointGradient (2 * j + i.val + 1))
          (orbit.endpoint (2 * j + i.val + 1) -
            orbit.endpoint (2 * j + i.val)) =
        (h.step i).nextSlope := by
    rw [endpointGradient_succ_eq_exactStepTransport orbit j i h,
      endpointStep_eq_exactStepTransport orbit j i h]
    rw [DFP.AbstractSecantStep.nextSlope_def]
    exact inner_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
      ((orbit.state j).phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).nextGradient (h.step i).displacement
  have hnextEq :
      (h.step i).nextSlope =
        (h.step i).slope + (h.step i).secantCurvature := by
    exact (h.step i).nextSlope_eq_add_secantCurvature
  constructor
  · rw [hstart, hnext]
    exact h.step_weakCurvature i
  · rw [inner_sub_left, hnext, hstart, hnextEq]
    simpa only [add_sub_cancel_left] using (h.step i).secantCurvature_pos

/-- Every flattened physical endpoint step of an exact two-phase orbit
satisfies weak curvature with `c₂ = 3 / 4` and has positive secant curvature. -/
theorem endpointCurvatureCertificates (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
        (inner ℝ (orbit.endpointGradient k) d)
        (inner ℝ (orbit.endpointGradient (k + 1)) d) ∧
      0 < inner ℝ
        (orbit.endpointGradient (k + 1) - orbit.endpointGradient k) d := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa only [Fin.val_zero, add_zero] using
      endpointPhaseCurvatureCertificates orbit j (0 : Fin 2) (h_exact j)
  · simpa only [Fin.val_one] using
      endpointPhaseCurvatureCertificates orbit j (1 : Fin 2) (h_exact j)

/-- Every flattened endpoint step of an exact two-phase orbit satisfies the
weak-Wolfe curvature condition with `c₂ = 3 / 4`. -/
theorem endpointWeakCurvature (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    LineSearch.Wolfe.IsWeakCurvature (3 / 4 : ℝ)
      (inner ℝ (orbit.endpointGradient k) d)
      (inner ℝ (orbit.endpointGradient (k + 1)) d) := by
  exact (endpointCurvatureCertificates orbit h_exact k).1

/-- Every flattened endpoint step of an exact two-phase orbit has positive
gradient-displacement secant curvature. -/
theorem endpointSecantCurvature_pos (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) (k : ℕ) :
    let d := orbit.endpoint (k + 1) - orbit.endpoint k
    0 < inner ℝ
      (orbit.endpointGradient (k + 1) - orbit.endpointGradient k) d := by
  exact (endpointCurvatureCertificates orbit h_exact k).2

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- A sufficiently small invariant slow-curve orbit has positive predicted
decrease and realized decrease ratio at least one half on both phases. -/
theorem phaseDecreaseRatioLowerBound (curve : DFP.TwoLeg.SlowCurve) :
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
                    (1 / 2 : ℝ) ≤
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
  let ηErr : ℝ := 1 / (12 * (Kratio + Kcorr))
  have hηErr : 0 < ηErr := by
    dsimp only [ηErr]
    positivity
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
    fin_cases i <;> omega
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
  have hsumPos : 0 < Kratio + Kcorr := add_pos hKratio hKcorr
  have herr :
      (Kratio + Kcorr) * εj ≤ (1 / 12 : ℝ) := by
    calc
      (Kratio + Kcorr) * εj ≤ (Kratio + Kcorr) * ηErr :=
        mul_le_mul_of_nonneg_left hεjErr hsumPos.le
      _ = 1 / 12 := by
        dsimp only [ηErr]
        field_simp [ne_of_gt hsumPos]
  have herr' :
      (Kratio / 2 + Kcorr) * εj ≤ (1 / 12 : ℝ) := by
    have hcoeff : Kratio / 2 + Kcorr ≤ Kratio + Kcorr := by
      linarith [hKratio]
    exact (mul_le_mul_of_nonneg_right hcoeff hεjMem.1.le).trans herr
  constructor
  · exact hqPos
  · rw [hidentity, hhalf]
    linarith

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoLeg.SlowCurve

/-- Every sufficiently small endpoint step of an invariant slow-curve orbit
satisfies the scalar Armijo condition with coefficient `1 / 4`. -/
theorem endpointArmijo (curve : DFP.TwoLeg.SlowCurve) :
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
                  LineSearch.Wolfe.IsArmijo (1 / 4 : ℝ)
                    (orbit.realizedObjective Clim G (orbit.endpoint k))
                    (orbit.realizedObjective Clim G (orbit.endpoint (k + 1)))
                    (inner ℝ (orbit.endpointGradient k) s) := by
  obtain ⟨εbar, hεbar, hRatio⟩ :=
    DFP.TwoLeg.SlowCurve.phaseDecreaseRatioLowerBound curve
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim G hRadius hDisjoint k
  have hphase :
      let s := orbit.endpoint (k + 1) - orbit.endpoint k
      let q := -inner ℝ (orbit.endpointGradient k) s
      0 < q ∧
        (1 / 2 : ℝ) ≤
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
  · calc
      (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
      _ ≤
          (orbit.realizedObjective Clim G (orbit.endpoint k) -
            orbit.realizedObjective Clim G (orbit.endpoint (k + 1))) /
            (-inner ℝ (orbit.endpointGradient k)
              (orbit.endpoint (k + 1) - orbit.endpoint k)) := by
        exact hphase.2

end DFP.TwoLeg.SlowCurve

namespace DFP.TwoPhaseOrbit

/-- The uniform decrease-ratio estimate for an unbundled slow-curve orbit. -/
theorem slowCurvePhaseDecreaseRatioLowerBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
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
                    (1 / 2 : ℝ) ≤
                      (orbit.realizedObjective Clim G (orbit.endpoint k) -
                        orbit.realizedObjective Clim G (orbit.endpoint (k + 1))) / q := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  have hBound := DFP.TwoLeg.SlowCurve.phaseDecreaseRatioLowerBound curve
  simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
    DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hBound

/-- The Armijo estimate for every endpoint step of an unbundled slow-curve orbit. -/
theorem slowCurveArmijo (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ G : ℝ,
            (∀ n : ℕ, 0 < orbit.interpolationRadius Clim G n) →
              Set.univ.PairwiseDisjoint (fun n : ℕ ↦
                Metric.closedBall (orbit.endpoint n)
                  (orbit.interpolationRadius Clim G n)) →
                ∀ k : ℕ,
                  let s := orbit.endpoint (k + 1) - orbit.endpoint k
                  orbit.realizedObjective Clim G (orbit.endpoint (k + 1)) ≤
                    orbit.realizedObjective Clim G (orbit.endpoint k) +
                      (1 / 4 : ℝ) *
                        inner ℝ (orbit.endpointGradient k) s := by
  let curve :=
    DFP.TwoLeg.SlowCurve.ofAsymptotics p h h_pJet h_hJet h_invariant
  obtain ⟨εbar, hεbar, hBound⟩ :=
    DFP.TwoLeg.SlowCurve.endpointArmijo curve
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim G hRadius hDisjoint k
  have hClim' :
      Tendsto
        (fun j : ℕ ↦
          ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).center)
        atTop (𝓝 Clim) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hClim
  have hRadius' :
      ∀ n : ℕ,
        0 < (DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).interpolationRadius
          Clim G n := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hRadius
  have hDisjoint' : Set.univ.PairwiseDisjoint (fun n : ℕ ↦
      Metric.closedBall
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).endpoint n)
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).interpolationRadius
          Clim G n)) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hDisjoint
  have hArmijo := hBound ε₀ hε₀ Clim hClim' G hRadius' hDisjoint' k
  have hArmijo' :
      LineSearch.Wolfe.IsArmijo (1 / 4 : ℝ)
        (orbit.realizedObjective Clim G (orbit.endpoint k))
        (orbit.realizedObjective Clim G (orbit.endpoint (k + 1)))
        (inner ℝ (orbit.endpointGradient k)
          (orbit.endpoint (k + 1) - orbit.endpoint k)) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high, orbit] using hArmijo
  exact LineSearch.Wolfe.isArmijo_iff.mp hArmijo'

end DFP.TwoPhaseOrbit
