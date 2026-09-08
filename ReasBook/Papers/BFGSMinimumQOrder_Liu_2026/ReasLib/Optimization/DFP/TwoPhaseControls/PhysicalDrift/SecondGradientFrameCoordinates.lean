module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-!
The second normalized gradient is represented in the fixed low-eigenvector frame by
the same quotient formulas used to define `independentSecondGradientFactors`.  These
lemmas expose that coordinate identity without making any claim about the sign chosen
by the physical oriented frame.
-/

/-- Helper for Appendix Lemma A.6: the fixed low-frame coordinates of the normalized
    second gradient are its factor pair, with the radius carried by the high coordinate. -/
theorem independentSecondGradient_fixedFrame_coordinates
    (b r L H Q U : ℝ) :
    (EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (r ^ 2 * (independentSecondResiduals b r L H Q U).1)
        (r * (independentSecondResiduals b r L H Q U).2.1)
        (independentSecondResiduals b r L H Q U).2.2)).transpose.mulVec
      (independentSecondGradient b r L H Q U) =
      ![(independentSecondGradientFactors b r L H Q U).1,
        r * (independentSecondGradientFactors b r L H Q U).2] := by
  unfold independentSecondGradient
  dsimp only
  rw [lowFrame_transpose_mulVec]
  ext i
  fin_cases i
  · simp [independentSecondGradientFactors]
    ring
  · simp [independentSecondGradientFactors]
    ring

/-- Helper for Appendix Lemma A.6: along the mixed independent-radius path, the
    canonical second-frame coordinates are `(Gₗ, r * Gₕ)`. -/
theorem independentRadiusSecondGradient_fixedFrame_coordinates
    (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    (EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (r ^ 2 * (independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).1)
        (r * (independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).2.1)
        (independentSecondResiduals θ.1 r
          (independentRadiusFirstSpectral (θ, r)).1
          (independentRadiusFirstSpectral (θ, r)).2
          (independentRadiusFirstGradient (θ, r)).1
          (independentRadiusFirstGradient (θ, r)).2).2.2)).transpose.mulVec
      (independentSecondGradient θ.1 r
        (independentRadiusFirstSpectral (θ, r)).1
        (independentRadiusFirstSpectral (θ, r)).2
        (independentRadiusFirstGradient (θ, r)).1
        (independentRadiusFirstGradient (θ, r)).2) =
      ![(independentRadiusSecondGradient (θ, r)).1,
        r * (independentRadiusSecondGradient (θ, r)).2] := by
  simpa only [independentRadiusSecondGradient] using
    independentSecondGradient_fixedFrame_coordinates θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2

/-- Helper for Appendix Lemma A.6: a paired frame/sign certificate turns canonical
    low coordinates into the oriented low coordinate without reopening the frame test. -/
theorem orientedLowCoordinate_eq_of_signedFrameCertificate
    (a b d q u : ℝ) (v : Fin 2 → ℝ)
    (F : Matrix (Fin 2) (Fin 2) ℝ)
    (hcertificate :
      (F = EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∧
        (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
          ![q, u]) ∨
      (F = -EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∧
        (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
          -![q, u])) :
    F.transpose.mulVec v 0 = q := by
  rcases hcertificate with ⟨hF, hcoords⟩ | ⟨hF, hcoords⟩
  · rw [hF]
    have hzero := congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords
    simpa using hzero
  · rw [hF, Matrix.transpose_neg, Matrix.neg_mulVec, hcoords]
    simp

end DFP.TwoLeg.Mixed
