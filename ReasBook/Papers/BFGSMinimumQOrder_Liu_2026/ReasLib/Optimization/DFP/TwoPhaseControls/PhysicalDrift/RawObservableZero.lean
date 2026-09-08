module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
# Zero branches of the physical raw observable

These finite identities keep the removable zero-radius calculations out of the
physical-drift germ and residual proofs.
-/

/-- Helper for Appendix Lemma A.6: a raw observable step whose incoming metric
    annihilates the gradient leaves the metric and gradient fixed and has zero displacement. -/
theorem rawObservableStep_eq_of_mulVec_eq_zero
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) (hzero : H *ᵥ g = 0) :
    rawObservableStep H g control = (H, g, 0) := by
  unfold rawObservableStep
  rw [hzero]
  simp [Matrix.inverseDFPUpdate]

/-- Helper for Appendix Lemma A.6: at zero radius the singular diagonal metric
    annihilates the canonical low gradient, so every controlled raw step is stationary. -/
theorem rawObservableStep_zeroRadius_base (control : PlanarDFPControl) :
    rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control =
      (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
  apply rawObservableStep_eq_of_mulVec_eq_zero
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/- A scalar diagonal entry is harmless in the zero-radius branch; retaining it
   makes the bridge stable under the parameterized input normal form. -/

/-- Helper for Appendix Lemma A.6: a diagonal metric with zero low entry fixes the
    canonical low gradient under every raw control. -/
theorem rawObservableStep_zeroRadius_diagonal (d : ℝ) (control : PlanarDFPControl) :
    rawObservableStep (Matrix.diagonal ![(0 : ℝ), d]) ![(1 : ℝ), 0] control =
      (Matrix.diagonal ![(0 : ℝ), d], ![(1 : ℝ), 0], 0) := by
  apply rawObservableStep_eq_of_mulVec_eq_zero
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper for Appendix Lemma A.6: scalar zero-radius substitutions reduce to the
    diagonal bridge without unfolding the raw DFP quotient. -/
theorem rawObservableStep_zeroRadius_scaled
    (a d p : ℝ) (control : PlanarDFPControl) :
    rawObservableStep (Matrix.diagonal ![a * (0 : ℝ) ^ 2, d]) ![(1 : ℝ), p * 0] control =
      (Matrix.diagonal ![(0 : ℝ), d], ![(1 : ℝ), 0], 0) := by
  have hH : Matrix.diagonal ![a * (0 : ℝ) ^ 2, d] =
      Matrix.diagonal ![(0 : ℝ), d] := by
    congr 1
    norm_num
  have hg : ![(1 : ℝ), p * 0] = ![(1 : ℝ), 0] := by
    congr 1
    norm_num
  rw [hH, hg]
  exact rawObservableStep_zeroRadius_diagonal d control

/-- Helper for Appendix Lemma A.6: conjugating a raw step by identity leaves its
    metric, gradient, and displacement tuple unchanged. -/
theorem rawObservableStep_identity_conjugation
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    rawObservableStep ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose * H * 1)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ g) control =
      rawObservableStep H g control := by
  simp

/- The zero-radius raw-step calculation uses the gradient-oriented frame rather
   than the canonical frame.  This pointwise identity is the normalization
   bridge needed before projecting the physical observable. -/

/-- Helper for Appendix Lemma A.6: the oriented low eigenframe at the diagonal
    zero-radius base point is the identity matrix. -/
theorem orientedEigenframe_zeroRadius_frame :
    OrientedEigenframe.frame 0 0 1
      (WithLp.toLp 2 (!₂[(1 : ℝ), 0])) = 1 := by
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  have hinner :
      0 < inner ℝ (RealSymmetric2.lowVector 0 0 1)
        (WithLp.toLp 2 (!₂[(1 : ℝ), 0])) := by
    rw [RealSymmetric2.lowVector_diag]
    norm_num [PiLp.inner_apply]
  rw [if_pos hinner]
  exact RealSymmetric2.frame_diag

/-- Helper for Appendix Lemma A.6: the first oriented frame produced from a stationary
    zero-radius raw step is the identity. -/
theorem rawObservableStep_zeroRadius_frame (control : PlanarDFPControl) :
    OrientedEigenframe.frame
        ((rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).1 0 0)
        ((rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).1 0 1)
        ((rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).1 1 1)
        (WithLp.toLp 2
          (rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).2.1) = 1 := by
  rw [rawObservableStep_zeroRadius_base]
  exact orientedEigenframe_zeroRadius_frame

/-- Helper for Appendix Lemma A.6: the scaled zero-radius input produces the same
    identity oriented frame, with all scalar substitutions hidden in one rewrite. -/
theorem rawObservableStep_zeroRadius_scaled_frame
    (a p : ℝ) (control : PlanarDFPControl) :
    OrientedEigenframe.frame
        ((rawObservableStep
          (Matrix.diagonal ![a * (0 : ℝ) ^ 2, 1]) ![(1 : ℝ), p * 0] control).1 0 0)
        ((rawObservableStep
          (Matrix.diagonal ![a * (0 : ℝ) ^ 2, 1]) ![(1 : ℝ), p * 0] control).1 0 1)
        ((rawObservableStep
          (Matrix.diagonal ![a * (0 : ℝ) ^ 2, 1]) ![(1 : ℝ), p * 0] control).1 1 1)
        (WithLp.toLp 2
          (rawObservableStep
            (Matrix.diagonal ![a * (0 : ℝ) ^ 2, 1]) ![(1 : ℝ), p * 0] control).2.1) = 1 := by
  rw [rawObservableStep_zeroRadius_scaled]
  exact orientedEigenframe_zeroRadius_frame

end DFP.TwoLeg.Mixed
