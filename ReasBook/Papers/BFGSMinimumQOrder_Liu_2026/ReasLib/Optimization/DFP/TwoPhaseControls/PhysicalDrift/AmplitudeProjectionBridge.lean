module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondJetConcrete
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
# Orientation bridge for the physical amplitude projection

The observable amplitude uses the oriented low eigenframe, whereas the independent-radius
calculation uses the canonical low frame.  A positive first coordinate is the exact condition
that identifies these two choices.  Keeping this fact here gives the physical-drift proof a
small geometric interface instead of unfolding either evaluator.
-/

/-- Helper for Appendix Lemma A.6: a positive canonical low-frame coordinate selects the oriented
eigenframe without a global sign change. -/
theorem orientedEigenframe_eq_fixedFrame_of_positive_coordinate
    (a b d q u : ℝ) (v : Fin 2 → ℝ)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![q, u]) (hq : 0 < q) :
    OrientedEigenframe.frame a b d (WithLp.toLp 2 v) =
      EuclideanPlane.frame (RealSymmetric2.lowVector a b d) := by
  have hinner : inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) = q := by
    have hzero := congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
      EuclideanPlane.frame, PiLp.inner_apply, mul_comm] using hzero
  have hinnerPos : 0 < inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) := by
    rwa [hinner]
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  split_ifs with hif
  · rfl
  · exfalso
    apply (not_lt_of_ge (le_of_not_gt hif))
    exact hinnerPos

/-- Appendix Lemma A.6 companion: the first oriented output coordinate equals its positive
canonical low-frame coordinate. -/
theorem orientedEigenframe_lowCoordinate_eq_of_positive_coordinate
    (a b d q u : ℝ) (v : Fin 2 → ℝ)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![q, u]) (hq : 0 < q) :
    (OrientedEigenframe.frame a b d (WithLp.toLp 2 v)).transpose.mulVec v 0 = q := by
  have hframe := orientedEigenframe_eq_fixedFrame_of_positive_coordinate
    a b d q u v hcoords hq
  rw [hframe]
  exact congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords

/-- Helper for Appendix Lemma A.6: the same orientation bridge is stable under a simultaneous
negation of the incoming vector and its canonical coordinates. -/
theorem orientedEigenframe_lowCoordinate_eq_of_positive_negated_coordinate
    (a b d q u : ℝ) (v : Fin 2 → ℝ)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![q, u]) (hq : 0 < q) :
    (OrientedEigenframe.frame a b d (WithLp.toLp 2 (-v))).transpose.mulVec (-v) 0 = q := by
  have hinner : inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) = q := by
    have hzero := congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
      EuclideanPlane.frame, PiLp.inner_apply, mul_comm] using hzero
  have hinnerPos : 0 < inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) := by
    rwa [hinner]
  have hinnerNe : inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) ≠ 0 := ne_of_gt hinnerPos
  rw [WithLp.toLp_neg,
    orientedEigenframe_frame_negate_gradient_of_inner_ne_zero a b d
      (WithLp.toLp 2 v) hinnerNe]
  simp only [Matrix.transpose_neg, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
  exact orientedEigenframe_lowCoordinate_eq_of_positive_coordinate
    a b d q u v hcoords hq

end DFP.TwoLeg.Mixed
