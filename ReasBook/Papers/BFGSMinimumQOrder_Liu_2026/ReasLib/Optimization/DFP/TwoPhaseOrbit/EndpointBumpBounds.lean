module

public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump
public import ReasLib.Analysis.Calculus.EuclideanPlaneSmoothCutoff
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointCorrection
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.SlowCurve

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DFP.TwoLeg.SlowCurve

/-- A common threshold and positive constants uniformly control the value,
first derivative, and second derivative of every endpoint bump on its support
along an invariant slow curve. -/
theorem endpointBumpUniformBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4),
      ∃ Kvalue > 0, ∃ Kgradient > 0, ∃ Khessian > 0,
        ∀ ε₀ ∈ Ioc 0 εbar,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ Glim > 0,
                Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                  ∀ k : ℕ, ∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                      ‖orbit.endpointBump Clim Glim k z‖ ≤
                          Kvalue * (orbit.state (k / 2)).ε *
                            orbit.endpointRadius k ^ 2 ∧
                        ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ ≤
                          Kgradient * (orbit.state (k / 2)).ε *
                            orbit.endpointRadius k ∧
                        ‖fderiv ℝ (fderiv ℝ
                            (orbit.endpointBump Clim Glim k)) z‖ ≤
                          Khessian * (orbit.state (k / 2)).ε := by
  obtain ⟨ηRadius, hηRadius, cLower, hcLower, cUpper, hcUpper, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  obtain ⟨ηCorrection, hηCorrection, Kcorrection, hKcorrection, hCorrection⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointCorrectionUniformBound
      curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph
      curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
  let M₀ := EuclideanPlane.smoothCutoffDerivBound 0
  let M₁ := EuclideanPlane.smoothCutoffDerivBound 1
  let M₂ := EuclideanPlane.smoothCutoffDerivBound 2
  have hM₀ : 0 ≤ M₀ := by
    exact EuclideanPlane.smoothCutoffDerivBound_nonneg 0
  have hM₁ : 0 ≤ M₁ := by
    exact EuclideanPlane.smoothCutoffDerivBound_nonneg 1
  have hM₂ : 0 ≤ M₂ := by
    exact EuclideanPlane.smoothCutoffDerivBound_nonneg 2
  have htwo_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
    have htwo_nat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr htwo_nat
  have hcutoff : ContDiff ℝ 2 EuclideanPlane.smoothCutoff :=
    EuclideanPlane.contDiff_smoothCutoff.of_le htwo_le_infty
  let εbar := min ηRadius (min ηCorrection ηGraph)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηRadius.1 (lt_min hηCorrection.1 hηGraph.1)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRadius.2
  let Kvalue := M₀ * Kcorrection * cUpper + 1
  let Kgradient := (M₁ + M₀) * Kcorrection + 1
  let Khessian := (M₂ + 2 * M₁) * Kcorrection / cLower + 1
  have hKvalue : 0 < Kvalue := by
    dsimp only [Kvalue]
    positivity
  have hKgradient : 0 < Kgradient := by
    dsimp only [Kgradient]
    positivity
  have hKhessian : 0 < Khessian := by
    dsimp only [Khessian]
    positivity
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩,
    Kvalue, hKvalue, Kgradient, hKgradient, Khessian, hKhessian, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRadius : ε₀ ∈ Ioc 0 ηRadius := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact min_le_left _ _
  have hεCorrection : ε₀ ∈ Ioc 0 ηCorrection := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεGraph : ε₀ ∈ Ioc 0 ηGraph := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hc'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    have hs := (hGraph ε₀ hεGraph j).2.1
    rw [hcoord j]
    exact hs
  intro Clim hClim Glim hGlim hGlimTendsto k z hz
  have hRadiusData : orbit.interpolationRadius Clim Glim k ∈ Icc
      (cLower * orbit.endpointRadius k)
      (cUpper * orbit.endpointRadius k) := by
    simpa only [orbit] using
      hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto k
  have hCorrectionData :
      ‖orbit.endpointCorrection Clim k‖ ≤
        Kcorrection * (orbit.state (k / 2)).ε ^ 3 := by
    simpa only [orbit] using
      hCorrection ε₀ hεCorrection Clim hClim k
  let e := (orbit.state (k / 2)).ε
  let R := orbit.endpointRadius k
  let ρ := orbit.interpolationRadius Clim Glim k
  let a := orbit.endpointCorrection Clim k
  have he : 0 < e := by
    simpa only [e] using hscalePos (k / 2)
  have hR : R = e ^ 2 := by
    simpa only [R, e] using
      DFP.TwoPhaseOrbit.endpointRadius_def orbit k
  have hRpos : 0 < R := by
    rw [hR]
    positivity
  have hρBounds : ρ ∈ Icc (cLower * R) (cUpper * R) := by
    simpa only [ρ, R] using hRadiusData
  have hρLower : cLower * R ≤ ρ := hρBounds.1
  have hρUpper : ρ ≤ cUpper * R := hρBounds.2
  have hρ : 0 < ρ :=
    (mul_pos hcLower hRpos).trans_le hρLower
  have hCorrectionE : ‖a‖ ≤ Kcorrection * e ^ 3 := by
    simpa only [a, e] using hCorrectionData
  have hscaleRadius : e ^ 3 = e * R := by
    simpa only [e, R] using
      DFP.TwoPhaseOrbit.endpointScale_mul_radius orbit k
  have hCorrectionR : ‖a‖ ≤ Kcorrection * e * R := by
    calc
      ‖a‖ ≤ Kcorrection * e ^ 3 := hCorrectionE
      _ = Kcorrection * e * R := by rw [hscaleRadius]; ring
  rw [DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump] at hz
  have hvalueRaw := AffineBump.norm_scaledLinearBump_le
    EuclideanPlane.smoothCutoff hcutoff M₀
    EuclideanPlane.tsupport_smoothCutoff_subset
    EuclideanPlane.norm_smoothCutoff_le
    (orbit.endpoint k) ρ a z hρ hz
  have hgradientRaw := AffineBump.norm_fderiv_scaledLinearBump_le
    EuclideanPlane.smoothCutoff hcutoff M₀ M₁
    EuclideanPlane.tsupport_smoothCutoff_subset
    EuclideanPlane.norm_smoothCutoff_le
    EuclideanPlane.norm_fderiv_smoothCutoff_le
    (orbit.endpoint k) ρ a z hρ hz
  have hhessianRaw := AffineBump.norm_secondFDeriv_scaledLinearBump_le
    EuclideanPlane.smoothCutoff hcutoff M₁ M₂
    EuclideanPlane.tsupport_smoothCutoff_subset
    EuclideanPlane.norm_fderiv_smoothCutoff_le
    EuclideanPlane.norm_secondFDeriv_smoothCutoff_le
    (orbit.endpoint k) ρ a z hρ hz
  rw [← DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump
    orbit Clim Glim k] at hvalueRaw hgradientRaw hhessianRaw
  have hratio : R / ρ ≤ 1 / cLower := by
    apply (div_le_div_iff₀ hρ hcLower).2
    simpa only [one_mul, mul_comm] using hρLower
  refine ⟨?_, ?_, ?_⟩
  · change ‖orbit.endpointBump Clim Glim k z‖ ≤ Kvalue * e * R ^ 2
    calc
      ‖orbit.endpointBump Clim Glim k z‖ ≤ M₀ * ‖a‖ * ρ := hvalueRaw
      _ ≤ M₀ * (Kcorrection * e * R) * ρ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCorrectionR hM₀) hρ.le
      _ ≤ M₀ * (Kcorrection * e * R) * (cUpper * R) := by
        exact mul_le_mul_of_nonneg_left hρUpper
          (mul_nonneg hM₀
            (mul_nonneg (mul_nonneg hKcorrection.le he.le) hRpos.le))
      _ = (M₀ * Kcorrection * cUpper) * (e * R ^ 2) := by ring
      _ ≤ (M₀ * Kcorrection * cUpper + 1) * (e * R ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
          (mul_nonneg he.le (sq_nonneg R))
      _ = Kvalue * e * R ^ 2 := by
        dsimp only [Kvalue]
        ring
  · change ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ ≤
      Kgradient * e * R
    calc
      ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ ≤
          (M₁ + M₀) * ‖a‖ := hgradientRaw
      _ ≤ (M₁ + M₀) * (Kcorrection * e * R) :=
        mul_le_mul_of_nonneg_left hCorrectionR (add_nonneg hM₁ hM₀)
      _ = ((M₁ + M₀) * Kcorrection) * (e * R) := by ring
      _ ≤ ((M₁ + M₀) * Kcorrection + 1) * (e * R) := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
          (mul_nonneg he.le hRpos.le)
      _ = Kgradient * e * R := by
        dsimp only [Kgradient]
        ring
  · change ‖fderiv ℝ
      (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖ ≤ Khessian * e
    have hHcoef : 0 ≤ M₂ + 2 * M₁ :=
      add_nonneg hM₂ (mul_nonneg (by norm_num) hM₁)
    calc
      ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖ ≤
          (M₂ + 2 * M₁) * ‖a‖ / ρ := hhessianRaw
      _ ≤ (M₂ + 2 * M₁) * (Kcorrection * e * R) / ρ := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCorrectionR hHcoef) hρ.le
      _ = ((M₂ + 2 * M₁) * Kcorrection * e) * (R / ρ) := by ring
      _ ≤ ((M₂ + 2 * M₁) * Kcorrection * e) * (1 / cLower) := by
        exact mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (mul_nonneg hHcoef hKcorrection.le) he.le)
      _ = ((M₂ + 2 * M₁) * Kcorrection / cLower) * e := by ring
      _ ≤ ((M₂ + 2 * M₁) * Kcorrection / cLower + 1) * e := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) he.le
      _ = Khessian * e := by rfl

end DFP.TwoLeg.SlowCurve
