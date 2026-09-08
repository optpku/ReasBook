module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ZeroRadiusObservables
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ZeroRadiusObservables
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
The quotient factorization in Appendix Lemma A.6 has two removable branches.  This
companion gives the radius-zero rewrite outright and keeps the zero-control branch
as an explicit raw-observable certificate, so the parent proof does not unfold the
full two-leg evaluator while deciding which branch it is in.
-/

/-- Helper for Appendix Lemma A.6: the concrete center residual vanishes on the
    removable zero-radius branch. -/
theorem centerResidual_zeroRadius (θ : ℝ × ℝ × ℝ) :
    (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * (0 : ℝ) ^ 2 = 0 := by
  have hinput : input θ 0 = (0, 2, 1) := by
    simp [input]
  rw [hinput, observableMap_zeroRadius_fullCenterDisplacement]
  simp

/-- Helper for Appendix Lemma A.6: zero control scale removes the parameter
    correction from the canonical input, leaving the base shape `(r,2,1)`. -/
theorem input_eq_baseShape_of_zeroScale
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hθ : θ.1 = 0) :
    input θ r = (r, 2, 1) := by
  simp [input, hθ]

/-- Helper for Appendix Lemma A.6: a supplied zero-scale raw-center certificate
    closes the center residual branch without making an unsupported claim about
    the evaluator at arbitrary radius. -/
theorem centerResidual_zeroScale_of_rawCertificate
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hθ : θ.1 = 0)
    (hraw : (observableMap 0 (input θ r)).fullCenterDisplacement 0 = 0) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 = 0 := by
  have hobs :
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 = 0 := by
    simpa [hθ] using hraw
  rw [hobs]
  simp [centerDriftCoefficient, hθ]

/-- Helper for Appendix Lemma A.6: the same zero-scale certificate can be supplied
    on the reduced base-shape input and transported to the canonical mixed input. -/
theorem centerResidual_zeroScale_of_baseShapeCertificate
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hθ : θ.1 = 0)
    (hbase : (observableMap 0 (r, 2, 1)).fullCenterDisplacement 0 = 0) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 = 0 := by
  apply centerResidual_zeroScale_of_rawCertificate θ r hθ
  rw [input_eq_baseShape_of_zeroScale θ r hθ]
  exact hbase

end DFP.TwoLeg.Mixed
