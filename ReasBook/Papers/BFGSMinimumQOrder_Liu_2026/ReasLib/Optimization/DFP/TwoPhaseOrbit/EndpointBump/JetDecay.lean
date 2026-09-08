module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBumpBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.SupportDistance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

noncomputable section

open Filter Set
open scoped Topology

namespace DFP.TwoLeg.SlowCurve

/-- Along an invariant slow curve, endpoint-bump values and first derivatives,
normalized by distance to the limiting circle, and second derivatives satisfy
uniform bounds at their respective powers of the cycle scale. -/
theorem endpointBumpNormalizedJetBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4),
      ∃ cSupport > 0, ∃ Cvalue > 0, ∃ Cgradient > 0, ∃ Chessian > 0,
        ∀ ε₀ ∈ Ioc 0 εbar,
          let orbit :=
            DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
          ∀ Clim : EuclideanSpace ℝ (Fin 2),
            Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
              ∀ Glim > 0,
                Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                  ∀ k : ℕ, ∀ z ∈ tsupport (orbit.endpointBump Clim Glim k),
                    let e := (orbit.state (k / 2)).ε
                    let d :=
                      Metric.infDist z
                        (DFP.TwoPhaseOrbit.limitCircle Clim Glim)
                    0 < e ∧ e ≤ 1 ∧ cSupport * e ≤ d ∧
                      ‖orbit.endpointBump Clim Glim k z‖ / d ^ 2 ≤
                          Cvalue * e ^ 3 ∧
                        ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ / d ≤
                          Cgradient * e ^ 2 ∧
                        ‖fderiv ℝ (fderiv ℝ
                          (orbit.endpointBump Clim Glim k)) z‖ ≤
                            Chessian * e := by
  obtain ⟨ηSupport, hηSupport, cSupport, hcSupport, hSupport⟩ :=
    curve.supportInfDistLinearLower
  obtain ⟨ηBounds, hηBounds, Kvalue, hKvalue, Kgradient, hKgradient,
      Khessian, hKhessian, hBounds⟩ := curve.endpointBumpUniformBounds
  let εbar := min ηSupport ηBounds
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηSupport.1 hηBounds.1
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηSupport.2
  let Cvalue := Kvalue / cSupport ^ 2
  let Cgradient := Kgradient / cSupport
  let Chessian := Khessian
  have hCvalue : 0 < Cvalue := by
    dsimp only [Cvalue]
    exact div_pos hKvalue (pow_pos hcSupport 2)
  have hCgradient : 0 < Cgradient := by
    dsimp only [Cgradient]
    exact div_pos hKgradient hcSupport
  have hChessian : 0 < Chessian := by
    simpa only [Chessian] using hKhessian
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cSupport, hcSupport,
    Cvalue, hCvalue, Cgradient, hCgradient, Chessian, hChessian, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεSupport : ε₀ ∈ Ioc 0 ηSupport :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεBounds : ε₀ ∈ Ioc 0 ηBounds :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hSupportData :=
    hSupport ε₀ hεSupport Clim hClim Glim hGlim hGlimTendsto
  have hBoundsData :=
    hBounds ε₀ hεBounds Clim hClim Glim hGlim hGlimTendsto
  let support : ℕ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun k ↦ tsupport (orbit.endpointBump Clim Glim k)
  have hSupportSubset (k : ℕ) : support k ⊆
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k) := by
    dsimp only [support]
    exact DFP.TwoPhaseOrbit.endpointBump_tsupport_subset_interpolationClosedBall
      orbit Clim Glim hSupportData.2.1 k
  intro k z hz
  let e := (orbit.state (k / 2)).ε
  let d := Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim)
  let R := orbit.endpointRadius k
  have he : 0 < e := by
    simpa only [e] using (hSupportData.1 (k / 2)).1
  have heOne : e ≤ 1 := by
    have hquarterLeOne : (1 / 4 : ℝ) ≤ 1 := by
      norm_num
    have heInitial : e ≤ ε₀ := by
      simpa only [e] using (hSupportData.1 (k / 2)).2
    exact heInitial.trans
      (hε₀.2.trans (hεbarLt.le.trans hquarterLeOne))
  have hdLower : cSupport * e ≤ d := by
    simpa only [support, d, e] using
      hSupportData.2.2 support hSupportSubset k z hz
  have hd : 0 < d := (mul_pos hcSupport he).trans_le hdLower
  have hR : R = e ^ 2 := by
    simpa only [R, e] using
      DFP.TwoPhaseOrbit.endpointRadius_def orbit k
  have hValueRaw : ‖orbit.endpointBump Clim Glim k z‖ ≤
      Kvalue * e * R ^ 2 := by
    simpa only [e, R] using (hBoundsData k z hz).1
  have hGradientRaw : ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ ≤
      Kgradient * e * R := by
    simpa only [e, R] using (hBoundsData k z hz).2.1
  have hHessianRaw : ‖fderiv ℝ (fderiv ℝ
      (orbit.endpointBump Clim Glim k)) z‖ ≤ Khessian * e := by
    simpa only [e] using (hBoundsData k z hz).2.2
  have hdenSq : (cSupport * e) ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hcSupport.le he.le) hdLower 2
  have hValueScaled : Kvalue * e * R ^ 2 ≤
      (Cvalue * e ^ 3) * d ^ 2 := by
    calc
      Kvalue * e * R ^ 2 = Kvalue * e ^ 5 := by
        rw [hR]
        ring
      _ = (Cvalue * e ^ 3) * (cSupport * e) ^ 2 := by
        dsimp only [Cvalue]
        field_simp [hcSupport.ne']
      _ ≤ (Cvalue * e ^ 3) * d ^ 2 := by
        exact mul_le_mul_of_nonneg_left hdenSq
          (mul_nonneg hCvalue.le (pow_nonneg he.le 3))
  have hValueQuotient : ‖orbit.endpointBump Clim Glim k z‖ / d ^ 2 ≤
      Cvalue * e ^ 3 := by
    apply (div_le_iff₀ (pow_pos hd 2)).2
    exact hValueRaw.trans hValueScaled
  have hGradientScaled : Kgradient * e * R ≤
      (Cgradient * e ^ 2) * d := by
    calc
      Kgradient * e * R = Kgradient * e ^ 3 := by
        rw [hR]
        ring
      _ = (Cgradient * e ^ 2) * (cSupport * e) := by
        dsimp only [Cgradient]
        field_simp [hcSupport.ne']
      _ ≤ (Cgradient * e ^ 2) * d := by
        exact mul_le_mul_of_nonneg_left hdLower
          (mul_nonneg hCgradient.le (sq_nonneg e))
  have hGradientQuotient :
      ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ / d ≤
        Cgradient * e ^ 2 := by
    apply (div_le_iff₀ hd).2
    exact hGradientRaw.trans hGradientScaled
  refine ⟨he, heOne, hdLower, hValueQuotient, hGradientQuotient, ?_⟩
  simpa only [Chessian] using hHessianRaw

/-- The normalized value, normalized first derivative, and second derivative
of endpoint bumps along an invariant slow curve vanish uniformly and
simultaneously as their supports approach the limiting circle. -/
theorem endpointBumpSecondOrderJetsVanish (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ η > 0, ∃ δ > 0, ∀ k : ℕ,
                ∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ tsupport (orbit.endpointBump Clim Glim k) →
                    Metric.infDist z
                        (DFP.TwoPhaseOrbit.limitCircle Clim Glim) < δ →
                      ‖orbit.endpointBump Clim Glim k z‖ /
                            Metric.infDist z
                              (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ^ 2 < η ∧
                        ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ /
                            Metric.infDist z
                              (DFP.TwoPhaseOrbit.limitCircle Clim Glim) < η ∧
                        ‖fderiv ℝ (fderiv ℝ
                          (orbit.endpointBump Clim Glim k)) z‖ < η := by
  obtain ⟨εbar, hεbar, cSupport, hcSupport, Cvalue, hCvalue,
      Cgradient, hCgradient, Chessian, hChessian, hBounds⟩ :=
    curve.endpointBumpNormalizedJetBounds
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  intro Clim hClim Glim hGlim hGlimTendsto η hη
  let Γ := DFP.TwoPhaseOrbit.limitCircle Clim Glim
  let support : ℕ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun k ↦ tsupport (orbit.endpointBump Clim Glim k)
  let scale : ℕ → ℝ := fun k ↦ (orbit.state (k / 2)).ε
  let valueQuantity : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun k z ↦ ‖orbit.endpointBump Clim Glim k z‖ /
      Metric.infDist z Γ ^ 2
  let gradientQuantity : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun k z ↦ ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ /
      Metric.infDist z Γ
  let hessianQuantity : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun k z ↦ ‖fderiv ℝ
      (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖
  have hDistance : ∀ k z, z ∈ support k →
      cSupport * scale k ≤ Metric.infDist z Γ := by
    intro k z hz
    simpa only [support, scale, Γ, orbit] using
      (hBounds ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz).2.2.1
  have hValueQuantity : ∀ k z, z ∈ support k →
      valueQuantity k z ≤ Cvalue * scale k := by
    intro k z hz
    have hJet :=
      hBounds ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz
    have heSqLe : scale k ^ 2 ≤ scale k := by
      dsimp only [scale]
      nlinarith [mul_nonneg hJet.1.le (sub_nonneg.mpr hJet.2.1)]
    have heCubeLe : scale k ^ 3 ≤ scale k := by
      calc
        scale k ^ 3 = scale k ^ 2 * scale k := by
          ring
        _ ≤ scale k ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hJet.2.1 (sq_nonneg (scale k))
        _ = scale k ^ 2 := by
          ring
        _ ≤ scale k := heSqLe
    exact hJet.2.2.2.1.trans
      (mul_le_mul_of_nonneg_left heCubeLe hCvalue.le)
  have hGradientQuantity : ∀ k z, z ∈ support k →
      gradientQuantity k z ≤ Cgradient * scale k := by
    intro k z hz
    have hJet :=
      hBounds ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz
    have heSqLe : scale k ^ 2 ≤ scale k := by
      dsimp only [scale]
      nlinarith [mul_nonneg hJet.1.le (sub_nonneg.mpr hJet.2.1)]
    exact hJet.2.2.2.2.1.trans
      (mul_le_mul_of_nonneg_left heSqLe hCgradient.le)
  have hHessianQuantity : ∀ k z, z ∈ support k →
      hessianQuantity k z ≤ Chessian * scale k := by
    intro k z hz
    simpa only [hessianQuantity, scale, support, orbit] using
      (hBounds ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto k z hz).2.2.2.2.2
  obtain ⟨δValue, hδValue, hValueDecay⟩ :=
    Metric.uniform_decay_of_le_scale_of_mul_scale_le_infDist
      Γ support scale valueQuantity cSupport Cvalue hcSupport hCvalue
        hDistance hValueQuantity η hη
  obtain ⟨δGradient, hδGradient, hGradientDecay⟩ :=
    Metric.uniform_decay_of_le_scale_of_mul_scale_le_infDist
      Γ support scale gradientQuantity cSupport Cgradient hcSupport hCgradient
        hDistance hGradientQuantity η hη
  obtain ⟨δHessian, hδHessian, hHessianDecay⟩ :=
    Metric.uniform_decay_of_le_scale_of_mul_scale_le_infDist
      Γ support scale hessianQuantity cSupport Chessian hcSupport hChessian
        hDistance hHessianQuantity η hη
  let δ := min δValue (min δGradient δHessian)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hδValue (lt_min hδGradient hδHessian)
  refine ⟨δ, hδ, ?_⟩
  intro k z hz hzδ
  have hzValue : Metric.infDist z Γ < δValue :=
    hzδ.trans_le (min_le_left _ _)
  have hzGradient : Metric.infDist z Γ < δGradient :=
    hzδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzHessian : Metric.infDist z Γ < δHessian :=
    hzδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [valueQuantity, support, Γ, orbit] using
      hValueDecay k z hz hzValue
  · simpa only [gradientQuantity, support, Γ, orbit] using
      hGradientDecay k z hz hzGradient
  · simpa only [hessianQuantity, support, orbit] using
      hHessianDecay k z hz hzHessian

end DFP.TwoLeg.SlowCurve
