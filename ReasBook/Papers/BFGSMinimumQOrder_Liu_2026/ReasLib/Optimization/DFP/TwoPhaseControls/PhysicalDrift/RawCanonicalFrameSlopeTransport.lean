module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.MixedCenterBracketBridge
public import ReasLib.Topology.Filter.UncurrySlice
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.MixedCenterBracketBridge

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion packages the punctured raw-frame chart hypotheses used by the
canonical slope bridge.  The certificate is deliberately pointwise: a source
calculation supplies its two signed frame choices and the two low-eigenvalue
normalizations, while the transport and the removable radius branch are shared.
-/

/-- Helper for Infrastructure I.16a: a punctured raw-frame point carries the two
signed frame choices and the low-eigenvalue identities needed to compare its
tangent coordinate with `canonicalFrameSlope`. -/
structure RawFrameSlopeData
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : Prop where
  firstFrame :
    mixedIndependentRawFirstFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        canonicalFirstFrame θ r ∨
    mixedIndependentRawFirstFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        -canonicalFirstFrame θ r
  secondFrame :
    mixedIndependentRawSecondFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        canonicalSecondFrame θ r ∨
    mixedIndependentRawSecondFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        -canonicalSecondFrame θ r
  firstLowDenom :
    RealSymmetric2.lowDenom
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2 ≠ 0
  secondLowDenom :
    RealSymmetric2.lowDenom
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0
  firstLow :
    RealSymmetric2.low
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2 =
      r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1
  secondLow :
    RealSymmetric2.low
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 =
      r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1

/-- Helper for Infrastructure I.16a: a predicate-indexed raw-frame package supplies
the same pointwise certificate on every point of its source domain. -/
abbrev RawFrameSlopeDataOn
    (D : (ℝ × ℝ × ℝ) → ℝ → Prop) : Prop :=
  ∀ θ r, D θ r → RawFrameSlopeData θ r

/- The projection-domain calculation fixes the first leg completely.  Keeping
   this interface separate lets a source proof supply only the genuinely
   second-leg frame and denominator data. -/

/-- Helper for Infrastructure I.16a: the punctured projection domain supplies
the first low-denominator and low-eigenvalue data. -/
theorem rawFirstLowData_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    RealSymmetric2.lowDenom
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2 ≠ 0 ∧
      RealSymmetric2.low
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1 := by
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  let t := independentFirstResiduals θ.1 r p h
  have hspectral : independentRadiusFirstSpectral (θ, r) =
      independentFirstSpectralFactors θ.1 r p h := by
    rfl
  have hgradientFactors : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenom : RealSymmetric2.lowDenom
      (r ^ 2 * t.1) (r * t.2.1) t.2.2 ≠ 0 := by
    intro hz
    apply hQ
    rw [hgradientFactors]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hz]
    simp
  have hhigh : RealSymmetric2.high
      (r ^ 2 * t.1) (r * t.2.1) t.2.2 ≠ 0 := by
    have hpos : 0 < RealSymmetric2.high
        (r ^ 2 * t.1) (r * t.2.1) t.2.2 := by
      simpa [hspectral, independentFirstSpectralFactors, t] using hH
    exact ne_of_gt hpos
  have hlow : RealSymmetric2.low
      (r ^ 2 * t.1) (r * t.2.1) t.2.2 =
      r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1 := by
    rw [low_eq_radiusSq_mul_detFactor r t.1 t.2.1 t.2.2 hhigh]
    simp [hspectral, independentFirstSpectralFactors, t]
  constructor
  · simpa [independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
      input, p, h, t] using hdenom
  · simpa [independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
      input, p, h, t, hspectral] using hlow

/-- Helper for Infrastructure I.16a: the punctured projection domain supplies the
first signed-frame choice and the first low-eigenvalue normalization. -/
theorem rawFirstFrameData_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    (mixedIndependentRawFirstFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        canonicalFirstFrame θ r ∨
      mixedIndependentRawFirstFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        -canonicalFirstFrame θ r) ∧
      RealSymmetric2.lowDenom
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2 ≠ 0 ∧
      RealSymmetric2.low
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1 := by
  have hfirst := mixedRawFirstCanonicalFrameData θ r hdomain
  have hlowData := rawFirstLowData_of_projectionDomain θ r hdomain
  dsimp only at hfirst
  rcases hfirst with ⟨hframe, _, _⟩ | ⟨hframe, _, _⟩
  · have hframe' :
        mixedIndependentRawFirstFrame θ.1 r
            (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          canonicalFirstFrame θ r := by
      simpa [mixedIndependentRawFirstFrame, canonicalFirstFrame, input] using hframe
    exact ⟨Or.inl hframe', hlowData⟩
  · have hframe' :
        mixedIndependentRawFirstFrame θ.1 r
            (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          -canonicalFirstFrame θ r := by
      simpa [mixedIndependentRawFirstFrame, canonicalFirstFrame, input] using hframe
    exact ⟨Or.inr hframe', hlowData⟩

/- The second leg has the same determinant identity as the first leg, but its
   source-facing hypotheses are naturally a positivity statement for the first
   gradient coordinate and a nonvanishing high eigenvalue.  This helper keeps
   those hypotheses together before the frame certificate is assembled. -/

/-- Helper for Infrastructure I.16a: positive projection-domain data make the
second-leg high eigenvalue nonzero, so it need not be repeated as a source
hypothesis. -/
theorem rawSecondHigh_ne_zero_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    RealSymmetric2.high
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0 := by
  have hfirst := mixedRawFirstCanonicalFrameData θ r hdomain
  dsimp only at hfirst
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
      Matrix.diagonal ![r ^ 2 * L, H] := by
    rcases hfirst with ⟨hframeFirst, hdiagFirst, _⟩ |
      ⟨hframeFirst, hdiagFirst, _⟩
    · simpa [CenterRaw.secondMetric, L, H, hframeFirst] using hdiagFirst
    · simpa [CenterRaw.secondMetric, L, H, hframeFirst] using hdiagFirst
  have hdiagSecond : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (sq_pos_of_ne_zero hr) hL
    · exact hH
  have hgradientCanonicalNonzero :
      (![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    apply hQ
    simpa [Q] using hzeroFirst
  have hgradientSecondNonzero :
      ((1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
    simpa using hgradientCanonicalNonzero
  have hrawPos := independentRawStep_metric_posDef
    (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
    (TwoPhaseControls.second θ.1) hdiagSecond hcontrols.2
    (TwoPhaseControls.tau_pos θ.1 1) hgradientCanonicalNonzero
  let M₂ := independentSecondMetric θ.1 r L H Q U
  have hsecondRaw := independentRawStep_second_eq θ.1 r L H Q U 1
    hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
    hgradientSecondNonzero hr
  have hsecondRawCanonical :
      independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
          (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
        (M₂, independentSecondGradient θ.1 r L H Q U) := by
    simpa [M₂] using hsecondRaw
  have hmetricRaw :
      (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
        (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1)).1 = M₂ := by
    simpa using congrArg Prod.fst hsecondRawCanonical
  have hM₂pos : M₂.PosDef := by
    rw [← hmetricRaw]
    exact hrawPos
  have hM₂matrix : M₂ = RealSymmetric2.matrix
      (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
      (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
      (independentSecondResiduals θ.1 r L H Q U).2.2 := by
    ext i j
    fin_cases i
    · fin_cases j
      · rfl
      · rfl
    · fin_cases j
      · rfl
      · rfl
  have hhighPos : 0 < RealSymmetric2.high
      (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
      (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
      (independentSecondResiduals θ.1 r L H Q U).2.2 := by
    apply realSymmetric2_high_pos_of_posDef
    rw [← hM₂matrix]
    simpa [M₂, independentSecondMetric]
  have hhigh : RealSymmetric2.high
      (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
      (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
      (independentSecondResiduals θ.1 r L H Q U).2.2 ≠ 0 :=
    ne_of_gt hhighPos
  simpa [independentRadiusSecondMetricTriple, L, H, Q, U] using hhigh

/-- Helper for Infrastructure I.16a: the projection-domain identities determine
the second raw frame up to the canonical global sign. -/
theorem rawSecondFrame_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    mixedIndependentRawSecondFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        canonicalSecondFrame θ r ∨
      mixedIndependentRawSecondFrame θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
        -canonicalSecondFrame θ r := by
  have hfirst := mixedRawFirstCanonicalFrameData θ r hdomain
  dsimp only at hfirst
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  rcases hfirst with ⟨hframeFirst, hdiagFirst, hgradFirst⟩ |
    ⟨hframeFirst, hdiagFirst, hgradFirst⟩
  · have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
        Matrix.diagonal ![r ^ 2 * L, H] := by
      simpa [CenterRaw.secondMetric, L, H, hframeFirst] using hdiagFirst
    have hgradientSecond : CenterRaw.secondGradient θ.1 (input θ r) =
        (1 : ℝ) • ![Q, r * U] := by
      simpa [CenterRaw.secondGradient, Q, U, hframeFirst] using hgradFirst
    have hdiagSecond : (Matrix.diagonal ![r ^ 2 * L, H] :
        Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
      apply Matrix.PosDef.diagonal
      intro i
      fin_cases i
      · exact mul_pos (sq_pos_of_ne_zero hr) hL
      · exact hH
    have hgradientCanonicalNonzero :
        (![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      intro hzero
      have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
      apply hQ
      simpa [Q] using hzeroFirst
    have hgradientSecondNonzero :
        ((1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      simpa using hgradientCanonicalNonzero
    have hsecondRaw := independentRawStep_second_eq θ.1 r L H Q U 1
      hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
      hgradientSecondNonzero hr
    let M₂ := independentSecondMetric θ.1 r L H Q U
    let v₂ := independentSecondGradient θ.1 r L H Q U
    have hsecondRawCanonical :
        independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
          (M₂, v₂) := by
      simpa [M₂, v₂] using hsecondRaw
    have hM₂pos : M₂.PosDef := by
      have hrawPos := independentRawStep_metric_posDef
        (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
        (TwoPhaseControls.second θ.1) hdiagSecond hcontrols.2
        (TwoPhaseControls.tau_pos θ.1 1) hgradientCanonicalNonzero
      have hmetricRaw :
          (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1)).1 = M₂ := by
        simpa using congrArg Prod.fst hsecondRawCanonical
      rw [← hmetricRaw]
      exact hrawPos
    have hM₂matrix : M₂ = RealSymmetric2.matrix
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 := by
      ext i j
      fin_cases i
      · fin_cases j
        · rfl
        · rfl
      · fin_cases j
        · rfl
        · rfl
    have hhighSecondPos : 0 < RealSymmetric2.high
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 := by
      apply realSymmetric2_high_pos_of_posDef
      rw [← hM₂matrix]
      simpa [M₂, independentSecondMetric]
    have hhighSecond : RealSymmetric2.high
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 ≠ 0 :=
      ne_of_gt hhighSecondPos
    have hspectralSecond : independentRadiusSecondSpectral (θ, r) =
        independentSecondSpectralFactors θ.1 r L H Q U := by
      rfl
    have hlowSecond := low_eq_radiusSq_mul_detFactor r
      (independentSecondResiduals θ.1 r L H Q U).1
      (independentSecondResiduals θ.1 r L H Q U).2.1
      (independentSecondResiduals θ.1 r L H Q U).2.2 hhighSecond
    have hlowSecond' : RealSymmetric2.low
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 =
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1 := by
      rw [hlowSecond]
      simp [hspectralSecond, independentSecondSpectralFactors]
    have hsecondFrame := orientedEigenframe_eq_fixed_or_neg
      (M₂ 0 0) (M₂ 0 1) (M₂ 1 1) (WithLp.toLp 2 v₂)
    have hrawMetric :
        (CenterRaw.secondStep θ.1 (input θ r)).1 =
          (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1)).1 := by
      simpa [CenterRaw.secondStep, hmetricSecond, hgradientSecond] using
        mixedRawObservableStep_metric_eq
          (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
          (TwoPhaseControls.second θ.1)
    have hrawGradient :
        (CenterRaw.secondStep θ.1 (input θ r)).2.1 =
          (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1)).2 := by
      simpa [CenterRaw.secondStep, hmetricSecond, hgradientSecond] using
        mixedRawObservableStep_gradient_eq
          (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
          (TwoPhaseControls.second θ.1)
    have hinput : input θ r =
        (r, 2 + θ.2.1 * θ.1 * r, 1 + θ.2.2 * θ.1 * r) := by
      exact input_apply θ.1 θ.2.1 θ.2.2 r
    have hrawFrame :
        mixedIndependentRawSecondFrame θ.1 r
            (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          OrientedEigenframe.frame (M₂ 0 0) (M₂ 0 1) (M₂ 1 1)
            (WithLp.toLp 2 v₂) := by
      unfold mixedIndependentRawSecondFrame
      dsimp only
      rw [← hinput, hrawMetric, hrawGradient, hsecondRawCanonical]
    rcases hsecondFrame with hsecondFrame | hsecondFrame
    · left
      rw [hrawFrame]
      simpa [M₂, v₂,
        canonicalSecondFrame, independentRadiusSecondMetricTriple,
        independentSecondMetric, hlowSecond', hspectralSecond,
        independentSecondSpectralFactors] using hsecondFrame
    · right
      rw [hrawFrame]
      simpa [M₂, v₂,
        canonicalSecondFrame, independentRadiusSecondMetricTriple,
        independentSecondMetric, hlowSecond', hspectralSecond,
        independentSecondSpectralFactors] using hsecondFrame
  · have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
        Matrix.diagonal ![r ^ 2 * L, H] := by
      simpa [CenterRaw.secondMetric, L, H, hframeFirst] using hdiagFirst
    have hgradientSecond : CenterRaw.secondGradient θ.1 (input θ r) =
        (-1 : ℝ) • ![Q, r * U] := by
      simpa [CenterRaw.secondGradient, Q, U, hframeFirst, neg_smul] using hgradFirst
    have hdiagSecond : (Matrix.diagonal ![r ^ 2 * L, H] :
        Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
      apply Matrix.PosDef.diagonal
      intro i
      fin_cases i
      · exact mul_pos (sq_pos_of_ne_zero hr) hL
      · exact hH
    have hgradientCanonicalNonzero :
        (![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      intro hzero
      have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
      apply hQ
      simpa [Q] using hzeroFirst
    have hgradientSecondNonzero :
        ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      simpa using hgradientCanonicalNonzero
    have hsecondRaw := independentRawStep_second_eq θ.1 r L H Q U (-1)
      hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
      hgradientSecondNonzero hr
    let M₂ := independentSecondMetric θ.1 r L H Q U
    let v₂ := independentSecondGradient θ.1 r L H Q U
    have hsecondRawCanonical :
        independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
          (M₂, -v₂) := by
      simpa [M₂, v₂] using hsecondRaw
    have hM₂pos : M₂.PosDef := by
      have hrawPos := independentRawStep_metric_posDef
        (Matrix.diagonal ![r ^ 2 * L, H])
        ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ)
        (TwoPhaseControls.second θ.1) hdiagSecond hcontrols.2
        (TwoPhaseControls.tau_pos θ.1 1) hgradientSecondNonzero
      have hmetricRaw :
          (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ)
            (TwoPhaseControls.second θ.1)).1 = M₂ := by
        simpa using congrArg Prod.fst hsecondRawCanonical
      rw [← hmetricRaw]
      exact hrawPos
    have hM₂matrix : M₂ = RealSymmetric2.matrix
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 := by
      ext i j
      fin_cases i
      · fin_cases j
        · rfl
        · rfl
      · fin_cases j
        · rfl
        · rfl
    have hhighSecondPos : 0 < RealSymmetric2.high
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 := by
      apply realSymmetric2_high_pos_of_posDef
      rw [← hM₂matrix]
      simpa [M₂, independentSecondMetric]
    have hhighSecond : RealSymmetric2.high
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 ≠ 0 :=
      ne_of_gt hhighSecondPos
    have hspectralSecond : independentRadiusSecondSpectral (θ, r) =
        independentSecondSpectralFactors θ.1 r L H Q U := by
      rfl
    have hlowSecond := low_eq_radiusSq_mul_detFactor r
      (independentSecondResiduals θ.1 r L H Q U).1
      (independentSecondResiduals θ.1 r L H Q U).2.1
      (independentSecondResiduals θ.1 r L H Q U).2.2 hhighSecond
    have hlowSecond' : RealSymmetric2.low
        (r ^ 2 * (independentSecondResiduals θ.1 r L H Q U).1)
        (r * (independentSecondResiduals θ.1 r L H Q U).2.1)
        (independentSecondResiduals θ.1 r L H Q U).2.2 =
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1 := by
      rw [hlowSecond]
      simp [hspectralSecond, independentSecondSpectralFactors]
    have hinput : input θ r =
        (r, 2 + θ.2.1 * θ.1 * r, 1 + θ.2.2 * θ.1 * r) := by
      exact input_apply θ.1 θ.2.1 θ.2.2 r
    have hrawMetric :
        (CenterRaw.secondStep θ.1 (input θ r)).1 =
          (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ)
              (TwoPhaseControls.second θ.1)).1 := by
      simpa [CenterRaw.secondStep, hmetricSecond, hgradientSecond] using
        mixedRawObservableStep_metric_eq
          (Matrix.diagonal ![r ^ 2 * L, H])
          ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ)
          (TwoPhaseControls.second θ.1)
    have hrawGradient :
        (CenterRaw.secondStep θ.1 (input θ r)).2.1 =
          (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ)
              (TwoPhaseControls.second θ.1)).2 := by
      simpa [CenterRaw.secondStep, hmetricSecond, hgradientSecond] using
        mixedRawObservableStep_gradient_eq
          (Matrix.diagonal ![r ^ 2 * L, H])
          ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ)
          (TwoPhaseControls.second θ.1)
    have hrawFrame :
        mixedIndependentRawSecondFrame θ.1 r
            (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          OrientedEigenframe.frame (M₂ 0 0) (M₂ 0 1) (M₂ 1 1)
            (WithLp.toLp 2 (-v₂)) := by
      unfold mixedIndependentRawSecondFrame
      dsimp only
      rw [← hinput, hrawMetric, hrawGradient, hsecondRawCanonical]
    have hsecondFrame := orientedEigenframe_eq_fixed_or_neg
      (M₂ 0 0) (M₂ 0 1) (M₂ 1 1) (WithLp.toLp 2 (-v₂))
    rcases hsecondFrame with hsecondFrame | hsecondFrame
    · left
      rw [hrawFrame]
      simpa [M₂, v₂,
        canonicalSecondFrame, independentRadiusSecondMetricTriple,
        independentSecondMetric, hlowSecond', hspectralSecond,
        independentSecondSpectralFactors] using hsecondFrame
    · right
      rw [hrawFrame]
      simpa [M₂, v₂,
        canonicalSecondFrame, independentRadiusSecondMetricTriple,
        independentSecondMetric, hlowSecond', hspectralSecond,
        independentSecondSpectralFactors] using hsecondFrame

/-- Helper for Infrastructure I.16a: positivity of the second-leg gradient and
the nonvanishing high eigenvalue force the second low denominator and its
radius-scaled low-eigenvalue identity. -/
theorem rawSecondLowData_of_high_ne_zero
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hGlo : 0 < (independentRadiusSecondGradient (θ, r)).1)
    (hhigh :
      RealSymmetric2.high
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0) :
    RealSymmetric2.lowDenom
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0 ∧
      RealSymmetric2.low
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1 := by
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  let t := independentSecondResiduals θ.1 r L H Q U
  have hspectral : independentRadiusSecondSpectral (θ, r) =
      independentSecondSpectralFactors θ.1 r L H Q U := by
    rfl
  have hgradient : independentRadiusSecondGradient (θ, r) =
      independentSecondGradientFactors θ.1 r L H Q U := by
    rfl
  have hdenom : RealSymmetric2.lowDenom
      (r ^ 2 * t.1) (r * t.2.1) t.2.2 ≠ 0 := by
    intro hz
    have hGloEq : (independentRadiusSecondGradient (θ, r)).1 = 0 := by
      rw [hgradient]
      unfold independentSecondGradientFactors
      dsimp only
      rw [hz]
      simp
    exact (ne_of_gt hGlo) hGloEq
  have hhigh' : RealSymmetric2.high
      (r ^ 2 * t.1) (r * t.2.1) t.2.2 ≠ 0 := by
    simpa [independentRadiusSecondMetricTriple,
      t, L, H, Q, U] using hhigh
  have hlow : RealSymmetric2.low
      (r ^ 2 * t.1) (r * t.2.1) t.2.2 =
      r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1 := by
    rw [low_eq_radiusSq_mul_detFactor r t.1 t.2.1 t.2.2 hhigh']
    simp [hspectral, independentSecondSpectralFactors, t]
  constructor
  · simpa [independentRadiusSecondMetricTriple,
      t, L, H, Q, U] using hdenom
  · simpa [independentRadiusSecondMetricTriple,
      t, L, H, Q, U, hspectral] using hlow

/-- Helper for Infrastructure I.16a: after the projection-domain calculation, a
source-supplied second-frame certificate completes the raw slope certificate. -/
theorem RawFrameSlopeData.of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r)
    (hsecondFrame :
      mixedIndependentRawSecondFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          canonicalSecondFrame θ r ∨
      mixedIndependentRawSecondFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          -canonicalSecondFrame θ r)
    (hsecondLowDenom :
      RealSymmetric2.lowDenom
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0)
    (hsecondLow :
      RealSymmetric2.low
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1) :
    RawFrameSlopeData θ r := by
  have hfirst := rawFirstFrameData_of_projectionDomain θ r hdomain
  refine
    { firstFrame := ?_
      secondFrame := hsecondFrame
      firstLowDenom := ?_
      secondLowDenom := hsecondLowDenom
      firstLow := ?_
      secondLow := hsecondLow }
  · exact hfirst.1
  · exact hfirst.2.1
  · exact hfirst.2.2

/-- Helper for Infrastructure I.16a: a second-frame orientation together with
the natural second-leg positivity conditions completes the raw slope certificate. -/
theorem RawFrameSlopeData.of_projectionDomain_of_high
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r)
    (hsecondFrame :
      mixedIndependentRawSecondFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          canonicalSecondFrame θ r ∨
      mixedIndependentRawSecondFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          -canonicalSecondFrame θ r)
    (hGlo : 0 < (independentRadiusSecondGradient (θ, r)).1)
    (hhigh :
      RealSymmetric2.high
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0) :
    RawFrameSlopeData θ r := by
  have hsecond := rawSecondLowData_of_high_ne_zero θ r hGlo hhigh
  exact RawFrameSlopeData.of_projectionDomain θ r hdomain hsecondFrame
    hsecond.1 hsecond.2

/-- Helper for Infrastructure I.16a: projection-domain data and the second-leg
positivity hypotheses alone assemble the complete raw slope certificate. -/
theorem RawFrameSlopeData.of_projectionDomain_and_high
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r)
    (hGlo : 0 < (independentRadiusSecondGradient (θ, r)).1)
    (hhigh :
      RealSymmetric2.high
        (independentRadiusSecondMetricTriple (θ, r)).1
        (independentRadiusSecondMetricTriple (θ, r)).2.1
        (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0) :
    RawFrameSlopeData θ r := by
  have hsecondFrame := rawSecondFrame_of_projectionDomain θ r hdomain
  exact RawFrameSlopeData.of_projectionDomain_of_high θ r hdomain
    hsecondFrame hGlo hhigh

/-- Helper for Infrastructure I.16a: a projection-domain point and positive
second-leg gradient already determine the complete raw slope certificate. -/
theorem RawFrameSlopeData.of_projectionDomain_and_gradient
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r)
  (hGlo : 0 < (independentRadiusSecondGradient (θ, r)).1) :
    RawFrameSlopeData θ r := by
  have hhigh := rawSecondHigh_ne_zero_of_projectionDomain θ r hdomain
  exact RawFrameSlopeData.of_projectionDomain_and_high θ r hdomain hGlo hhigh

/-- Helper for Infrastructure I.16a: a domain map into the projection region and
pointwise second-gradient positivity produce a reusable slope certificate family. -/
theorem rawFrameSlopeDataOn_of_projectionDomain
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hD : ∀ θ r, D θ r → mixedRawProjectionDomain θ r)
    (hGlo : ∀ θ r, D θ r → 0 < (independentRadiusSecondGradient (θ, r)).1) :
    RawFrameSlopeDataOn D := by
  intro θ r hpoint
  exact RawFrameSlopeData.of_projectionDomain_and_gradient θ r
    (hD θ r hpoint) (hGlo θ r hpoint)

/-- Helper for Infrastructure I.16a: a punctured projection-domain point supplies
    the canonical frame/displacement certificate used by the center bracket. -/
theorem CanonicalCenterFrameData.of_projectionDomain
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hdomain : mixedRawProjectionDomain θ r) :
    CanonicalCenterFrameData θ r := by
  have hfirst := rawFirstFrameData_of_projectionDomain θ r hdomain
  have horthRaw := mixedRawFirstFrame_mul_transpose_of_projectionDomain θ r hdomain
  have horthRaw' :
      mixedIndependentRawFirstFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) *
        (mixedIndependentRawFirstFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)).transpose = 1 := by
    simpa [mixedIndependentRawFirstFrame, CenterRaw.firstFrame,
      CenterRaw.firstStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
      input] using horthRaw
  have horth : canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1 := by
    rcases hfirst.1 with hframe | hframe
    · rw [← hframe]
      exact horthRaw'
    · have hraw' :
          (-canonicalFirstFrame θ r) * (-canonicalFirstFrame θ r).transpose = 1 := by
        simpa [hframe] using horthRaw'
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hraw'
  have hsecond := mixedRawSecondDisplacement_eq_signedCanonical θ r hdomain
  have hfirstDisp :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r := by
    have hdenom : 0 < 1 + 2 * θ.1 * r + r ^ 2 :=
      mixedFirstDisplacement_denominator_pos hdomain
    rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hden :
        (input θ r).2.2 ^ 2 * (input θ r).2.1 ^ 2 * r ^ 2 *
          (1 + 2 * θ.1 * r + r ^ 2) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hh))
          (pow_ne_zero 2 (ne_of_gt hp))) (pow_ne_zero 2 hr))
        (ne_of_gt hdenom)
    simpa [canonicalFirstNormalizedDisplacement, input,
      CenterRaw.firstStep, CenterRaw.initialMetric, CenterRaw.initialGradient] using
      CenterRaw.firstStep_displacement_eq_radius_smul θ.1 r
        (input θ r).2.1 (input θ r).2.2 hden
  refine { orthogonal := horth, branch := ?_, firstDisplacement := hfirstDisp }
  simpa [canonicalFirstFrame, canonicalSecondNormalizedDisplacement,
    centerSecondDisplacementLow, centerSecondDisplacementHigh,
    centerSecondDisplacementGradientLow, centerSecondDisplacementGradientHigh,
    CenterRaw.secondNormalizedDisplacement] using hsecond

/-- Helper for Infrastructure I.16a: a projection-domain family and a canonical
    bracket kernel identity assemble the reusable frame-kernel certificate. -/
theorem CanonicalFrameKernelDataOn.of_projectionDomain
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hD : ∀ θ r, D θ r → mixedRawProjectionDomain θ r)
    (hkernel : ∀ θ r, D θ r →
      canonicalCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r) :
    CanonicalFrameKernelDataOn K D := by
  refine
    { orthogonal := ?_
      branch := ?_
      firstDisplacement := ?_
      bracketValue := ?_
      bracketKernel := ?_ }
  · intro θ r hpoint
    exact (CanonicalCenterFrameData.of_projectionDomain
      (hD θ r hpoint)).orthogonal
  · intro θ r hpoint
    exact (CanonicalCenterFrameData.of_projectionDomain
      (hD θ r hpoint)).branch
  · intro θ r hpoint
    exact (CanonicalCenterFrameData.of_projectionDomain
      (hD θ r hpoint)).firstDisplacement
  · intro θ r hpoint
    rfl
  · intro θ r hpoint
    exact hkernel θ r hpoint

/-- Helper for Infrastructure I.16a: the mixed-bracket kernel form is transported
    to the canonical frame-kernel package by the shared bracket identity. -/
theorem CanonicalFrameKernelDataOn.of_projectionDomain_of_mixedKernel
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hD : ∀ θ r, D θ r → mixedRawProjectionDomain θ r)
    (hkernel : ∀ θ r, D θ r →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r) :
    CanonicalFrameKernelDataOn K D := by
  apply CanonicalFrameKernelDataOn.of_projectionDomain hD
  intro θ r hpoint
  rw [← mixedCenterBracket_eq_canonicalCenterBracket]
  exact hkernel θ r hpoint

/-- Helper for Infrastructure I.16a: a slope certificate transports the raw
relative-frame tangent to the canonical frame-coordinate quotient. -/
theorem RawFrameSlopeData.slope_eq
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (data : RawFrameSlopeData θ r) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ r =
      canonicalFrameSlope θ r := by
  exact mixedIndependentRawFrameAngleSlope_eq_canonicalFrameSlope_of_signedFrameData
    θ r data.firstFrame data.secondFrame data.firstLowDenom data.secondLowDenom
    data.firstLow data.secondLow

/-- Helper for Infrastructure I.16a: the same certificate transports the raw
frame-angle evaluator through its arctangent chart. -/
theorem RawFrameSlopeData.angle_eq
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (data : RawFrameSlopeData θ r) :
    mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
      Real.arctan (canonicalFrameSlope θ r) := by
  rw [mixedIndependentRawFrameAngleAlongInput_eq_arctan_slope]
  rw [data.slope_eq]

/-- Helper for Infrastructure I.16a: a domain certificate gives the canonical slope
at every point where its source predicate holds. -/
theorem RawFrameSlopeDataOn.slope_eq
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hD : D θ r) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ r =
      canonicalFrameSlope θ r := by
  exact (data θ r hD).slope_eq

/-- Helper for Infrastructure I.16a: a domain certificate gives the canonical
frame-angle coordinate at every point where its source predicate holds. -/
theorem RawFrameSlopeDataOn.angle_eq
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hD : D θ r) :
    mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
      Real.arctan (canonicalFrameSlope θ r) := by
  exact (data θ r hD).angle_eq

/-- Helper for Infrastructure I.16a: the raw tangent and canonical slope agree
at the removable radius without invoking any low-denominator hypothesis. -/
theorem rawFrameSlope_eq_canonical_of_zero
    (θ : ℝ × ℝ × ℝ) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ 0 =
      canonicalFrameSlope θ 0 := by
  exact mixedIndependentRawFrameAngleSlopeAlongInput_zero_eq_canonicalFrameSlope θ

/-- Helper for Infrastructure I.16a: the raw frame-angle evaluator and its
canonical arctangent agree at the removable radius. -/
theorem rawFrameAngle_eq_canonical_of_zero
    (θ : ℝ × ℝ × ℝ) :
    mixedIndependentRawFrameAngle θ.1 0 2 1 =
      Real.arctan (canonicalFrameSlope θ 0) := by
  have hangle := mixedIndependentRawFrameAngleAlongInput_eq_arctan_slope θ 0
  rw [mixedIndependentRawFrameAngleSlopeAlongInput_zero] at hangle
  simpa [canonicalFrameSlope_zero] using hangle

/-- Helper for Infrastructure I.16a: a zero-radius or punctured certificate
gives one pointwise raw-to-canonical slope equality. -/
theorem rawFrameSlope_eq_canonical_of_zero_or
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hdata : r = 0 ∨ RawFrameSlopeData θ r) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ r =
      canonicalFrameSlope θ r := by
  rcases hdata with hr | data
  · subst r
    exact rawFrameSlope_eq_canonical_of_zero θ
  · exact data.slope_eq

/-- Helper for Infrastructure I.16a: a zero-radius or punctured certificate
gives one pointwise raw-to-canonical frame-angle equality. -/
theorem rawFrameAngle_eq_canonical_of_zero_or
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hdata : r = 0 ∨ RawFrameSlopeData θ r) :
    mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
      Real.arctan (canonicalFrameSlope θ r) := by
  rcases hdata with hr | data
  · subst r
    simpa only [mul_zero, add_zero] using rawFrameAngle_eq_canonical_of_zero θ
  · exact data.angle_eq

/-- Helper for Infrastructure I.16a: a local zero-radius/punctured cover gives the
uncurried raw slope equality consumed by an independent-radius germ proof. -/
theorem rawFrameSlope_uncurry_eventuallyEq_canonical_of_cover
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2) :
    Function.uncurry mixedIndependentRawFrameAngleSlopeAlongInput =ᶠ[𝓝 (θ, 0)]
      Function.uncurry canonicalFrameSlope := by
  filter_upwards [hcover] with z hz
  change mixedIndependentRawFrameAngleSlopeAlongInput z.1 z.2 =
    canonicalFrameSlope z.1 z.2
  exact rawFrameSlope_eq_canonical_of_zero_or hz

/-- Helper for Infrastructure I.16a: a joint raw-to-canonical slope equality
restricts to the radius slice at a fixed parameter. -/
theorem rawFrameSlope_eventuallyEq_canonical_of_cover
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ =ᶠ[𝓝 (0 : ℝ)]
      canonicalFrameSlope θ := by
  exact (rawFrameSlope_uncurry_eventuallyEq_canonical_of_cover hcover).uncurry_slice

/-- Helper for Infrastructure I.16a: the same local cover transports the raw
frame-angle evaluator to the canonical arctangent coordinate. -/
theorem rawFrameAngle_uncurry_eventuallyEq_canonical_of_cover
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2) :
    Function.uncurry
          (fun η r ↦ mixedIndependentRawFrameAngle η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) =ᶠ[𝓝 (θ, 0)]
      Function.uncurry (fun η r ↦ Real.arctan (canonicalFrameSlope η r)) := by
  filter_upwards [hcover] with z hz
  change mixedIndependentRawFrameAngle z.1.1 z.2
      (2 + z.1.2.1 * z.1.1 * z.2)
      (1 + z.1.2.2 * z.1.1 * z.2) =
    Real.arctan (canonicalFrameSlope z.1 z.2)
  exact rawFrameAngle_eq_canonical_of_zero_or hz

/-- Helper for Infrastructure I.16a: a joint raw-to-canonical angle equality
restricts to the radius slice at a fixed parameter. -/
theorem rawFrameAngle_eventuallyEq_canonical_of_cover
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2) :
    (fun r ↦ mixedIndependentRawFrameAngle θ.1 r
      (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r ↦ Real.arctan (canonicalFrameSlope θ r)) := by
  exact (rawFrameAngle_uncurry_eventuallyEq_canonical_of_cover hcover).uncurry_slice

/-- Helper for Infrastructure I.16a: a zero-radius or domain cover transports a raw slope
family to the canonical frame slope without exposing the certificate fields. -/
theorem rawFrameSlope_uncurry_eventuallyEq_canonical_of_domainCover
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ D z.1 z.2) :
    Function.uncurry mixedIndependentRawFrameAngleSlopeAlongInput =ᶠ[𝓝 (θ, 0)]
      Function.uncurry canonicalFrameSlope := by
  have hcertificate : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2 := by
    filter_upwards [hcover] with z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (data z.1 z.2 hz)
  exact rawFrameSlope_uncurry_eventuallyEq_canonical_of_cover hcertificate

/-- Helper for Infrastructure I.16a: a domain-cover slope equality restricts
to the radius slice at a fixed parameter. -/
theorem rawFrameSlope_eventuallyEq_canonical_of_domainCover
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ D z.1 z.2) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ =ᶠ[𝓝 (0 : ℝ)]
      canonicalFrameSlope θ := by
  exact (rawFrameSlope_uncurry_eventuallyEq_canonical_of_domainCover data hcover).uncurry_slice

/-- Helper for Infrastructure I.16a: the standard parameter-set projection tube and the
    positive second-gradient slice automatically provide the raw/canonical
    slope equality near every removable-radius base point. -/
theorem rawFrameSlope_uncurry_eventuallyEq_canonical_of_parameterSet
    (β B : ℝ) (hβ_small : β < 1 / 4)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B) :
    Function.uncurry mixedIndependentRawFrameAngleSlopeAlongInput =ᶠ[𝓝 (θ, 0)]
      Function.uncurry canonicalFrameSlope := by
  have hdomain := mixedRawProjectionDomain_eventually β B hβ_small hθ
  have hGloCont : ContinuousAt
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondGradient z).1) (θ, 0) :=
    continuousAt_fst.comp (independentRadiusSecondGradient_analyticAt θ).continuousAt
  have hGlo : ∀ᶠ z : ((ℝ × ℝ × ℝ) × ℝ) in 𝓝 (θ, 0),
      0 < (independentRadiusSecondGradient z).1 := by
    apply hGloCont.eventually
    have hbase :
        (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
          (independentRadiusSecondGradient z).1) (θ, 0) = 1 := by
      exact congrArg Prod.fst (independentRadiusSecondGradient_zero θ)
    have hone : (0 : ℝ) < 1 := by norm_num
    rw [hbase]
    exact Ioi_mem_nhds hone
  have hcertificate : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2 := by
    filter_upwards [hdomain, hGlo] with z hz hGloz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (RawFrameSlopeData.of_projectionDomain_and_gradient
        z.1 z.2 hz hGloz)
  exact rawFrameSlope_uncurry_eventuallyEq_canonical_of_cover hcertificate

/-- Helper for Infrastructure I.16a: the parameter-set slope equality
restricts to the radius slice at a fixed parameter. -/
theorem rawFrameSlope_eventuallyEq_canonical_of_parameterSet
    (β B : ℝ) (hβ_small : β < 1 / 4)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ =ᶠ[𝓝 (0 : ℝ)]
      canonicalFrameSlope θ := by
  exact (rawFrameSlope_uncurry_eventuallyEq_canonical_of_parameterSet
    β B hβ_small hθ).uncurry_slice

/-- Helper for Infrastructure I.16a: the standard parameter-set projection tube
    transports the raw frame-angle evaluator to the canonical arctangent chart. -/
theorem rawFrameAngle_uncurry_eventuallyEq_canonical_of_parameterSet
    (β B : ℝ) (hβ_small : β < 1 / 4)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B) :
    Function.uncurry
          (fun η r ↦ mixedIndependentRawFrameAngle η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) =ᶠ[𝓝 (θ, 0)]
      Function.uncurry (fun η r ↦ Real.arctan (canonicalFrameSlope η r)) := by
  have hsl := rawFrameSlope_uncurry_eventuallyEq_canonical_of_parameterSet
    β B hβ_small hθ
  filter_upwards [hsl] with z hz
  change mixedIndependentRawFrameAngle z.1.1 z.2
      (2 + z.1.2.1 * z.1.1 * z.2)
      (1 + z.1.2.2 * z.1.1 * z.2) =
    Real.arctan (canonicalFrameSlope z.1 z.2)
  rw [mixedIndependentRawFrameAngleAlongInput_eq_arctan_slope]
  exact congrArg Real.arctan hz

/-- Helper for Infrastructure I.16a: the parameter-set angle equality
restricts to the radius slice at a fixed parameter. -/
theorem rawFrameAngle_eventuallyEq_canonical_of_parameterSet
    (β B : ℝ) (hβ_small : β < 1 / 4)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B) :
    (fun r ↦ mixedIndependentRawFrameAngle θ.1 r
      (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r ↦ Real.arctan (canonicalFrameSlope θ r)) := by
  exact (rawFrameAngle_uncurry_eventuallyEq_canonical_of_parameterSet
    β B hβ_small hθ).uncurry_slice

/-- Helper for Infrastructure I.16a: the parameter-set projection tube gives the
    canonical `[0, -3]` truncated germ for the raw frame-angle evaluator. -/
theorem rawFrameAngle_truncatedGerm_of_parameterSet
    (β B : ℝ) (hβ_small : β < 1 / 4) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r))
      (parameterSet β B) 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hcanonical :
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ Real.arctan (canonicalFrameSlope θ r))
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
    apply independentRadiusTruncatedGerm_of_arctan_zero_slope
      (f := canonicalFrameSlope) (K := parameterSet β B)
      (a := fun _θ ↦ (-3 : ℝ))
    · intro θ hθ
      exact (canonicalFrameSlope_analyticAt θ).contDiffAt
    · intro θ hθ
      exact canonicalFrameSlope_zero θ
    · intro θ hθ
      simpa only [iteratedDeriv_one] using
        (canonicalFrameSlope_contDiffAt_and_deriv θ).2
  exact observableScalarGerm_of_uncurry_eventuallyEq
    (fun θ hθ => rawFrameAngle_uncurry_eventuallyEq_canonical_of_parameterSet
      β B hβ_small hθ) hcanonical

/-- Helper for Infrastructure I.16a: the parameter-set projection tube gives the
    canonical `[0, -3]` truncated germ for the raw relative-frame slope. -/
theorem rawFrameSlope_truncatedGerm_of_parameterSet
    (β B : ℝ) (hβ_small : β < 1 / 4) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ mixedIndependentRawFrameAngleSlopeAlongInput θ r)
      (parameterSet β B) 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hcanonical :
      IndependentRadiusTruncatedGerm canonicalFrameSlope (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
    apply independentRadiusTruncatedGerm_of_twoDerivativeData
    · intro θ hθ
      exact (canonicalFrameSlope_analyticAt θ).contDiffAt
    · intro θ hθ
      exact canonicalFrameSlope_zero θ
    · intro θ hθ
      simpa only [iteratedDeriv_one] using
        (canonicalFrameSlope_contDiffAt_and_deriv θ).2
  exact observableScalarGerm_of_uncurry_eventuallyEq
    (fun θ hθ => rawFrameSlope_uncurry_eventuallyEq_canonical_of_parameterSet
      β B hβ_small hθ) hcanonical

/-- Helper for Infrastructure I.16a: the same zero-radius or domain cover transports
    the raw frame-angle family through the canonical arctangent coordinate. -/
theorem rawFrameAngle_uncurry_eventuallyEq_canonical_of_domainCover
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ D z.1 z.2) :
    Function.uncurry
          (fun η r ↦ mixedIndependentRawFrameAngle η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) =ᶠ[𝓝 (θ, 0)]
      Function.uncurry (fun η r ↦ Real.arctan (canonicalFrameSlope η r)) := by
  have hcertificate : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ RawFrameSlopeData z.1 z.2 := by
    filter_upwards [hcover] with z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (data z.1 z.2 hz)
  exact rawFrameAngle_uncurry_eventuallyEq_canonical_of_cover hcertificate

/-- Helper for Infrastructure I.16a: a domain-cover angle equality restricts
to the radius slice at a fixed parameter. -/
theorem rawFrameAngle_eventuallyEq_canonical_of_domainCover
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    {θ : ℝ × ℝ × ℝ}
    (hcover : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ D z.1 z.2) :
    (fun r ↦ mixedIndependentRawFrameAngle θ.1 r
      (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r ↦ Real.arctan (canonicalFrameSlope θ r)) := by
  exact (rawFrameAngle_uncurry_eventuallyEq_canonical_of_domainCover data hcover).uncurry_slice

/-
  The pointwise frame certificate and the canonical analytic germ are separate
  interfaces.  The theorem below is the stable composition point for source
  calculations: once a domain cover is supplied, no arctangent or slice-filter
  plumbing remains at the call site.
-/

/-- Helper for Infrastructure I.16a: a zero-radius/punctured raw-frame cover transports the
    canonical `[0, -3]` frame-angle germ to the physical raw evaluator. -/
theorem rawFrameAngle_truncatedGerm_of_domainCover
    {K : Set (ℝ × ℝ × ℝ)}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    (hcover : ∀ θ, θ ∈ K →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) K 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hcanonical :
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ Real.arctan (canonicalFrameSlope θ r)) K 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
    apply independentRadiusTruncatedGerm_of_arctan_zero_slope
      (f := canonicalFrameSlope) (K := K) (a := fun _θ ↦ (-3 : ℝ))
    · intro θ hθ
      exact (canonicalFrameSlope_analyticAt θ).contDiffAt
    · intro θ hθ
      exact canonicalFrameSlope_zero θ
    · intro θ hθ
      simpa only [iteratedDeriv_one] using
        (canonicalFrameSlope_contDiffAt_and_deriv θ).2
  exact observableScalarGerm_of_uncurry_eventuallyEq
    (fun θ hθ => rawFrameAngle_uncurry_eventuallyEq_canonical_of_domainCover
      data (hcover θ hθ)) hcanonical

/-
  The slope itself is useful to source calculations that postpone the arctangent
  chart.  It has the same removable-radius transport, with coefficients obtained
  directly from the two-derivative germ interface.
-/

/-- Helper for Infrastructure I.16a: a zero-radius/punctured raw-frame cover transports the
    canonical `[0, -3]` slope germ before applying the arctangent chart. -/
theorem rawFrameSlope_truncatedGerm_of_domainCover
    {K : Set (ℝ × ℝ × ℝ)}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : RawFrameSlopeDataOn D)
    (hcover : ∀ θ, θ ∈ K →
      ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
        z.2 = 0 ∨ D z.1 z.2) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ mixedIndependentRawFrameAngleSlopeAlongInput θ r) K 2
      (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
  have hcanonical :
      IndependentRadiusTruncatedGerm canonicalFrameSlope K 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
    apply independentRadiusTruncatedGerm_of_twoDerivativeData
    · intro θ hθ
      exact (canonicalFrameSlope_analyticAt θ).contDiffAt
    · intro θ hθ
      exact canonicalFrameSlope_zero θ
    · intro θ hθ
      simpa only [iteratedDeriv_one] using
        (canonicalFrameSlope_contDiffAt_and_deriv θ).2
  exact observableScalarGerm_of_uncurry_eventuallyEq
    (fun θ hθ => rawFrameSlope_uncurry_eventuallyEq_canonical_of_domainCover
      data (hcover θ hθ)) hcanonical

end DFP.TwoLeg.Mixed
