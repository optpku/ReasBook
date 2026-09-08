module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawObservableZero
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawObservableZero

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: the first control at zero scale is the identity
matrix with ratio `2 / 3`. -/
theorem firstControl_zero_scale :
    TwoPhaseControls.first 0 =
      ({ matrix := (1 : Matrix (Fin 2) (Fin 2) ℝ), tau := 2 / 3 } : PlanarDFPControl) := by
  simpa [TwoPhaseControls.first, RealSymmetric2.matrix] using
    (Matrix.one_fin_two (α := ℝ)).symm

/-- Helper for Appendix Lemma A.6: the second control at zero scale is the identity
matrix with ratio `1 / 3`. -/
theorem secondControl_zero_scale :
    TwoPhaseControls.second 0 =
      ({ matrix := (1 : Matrix (Fin 2) (Fin 2) ℝ), tau := 1 / 3 } : PlanarDFPControl) := by
  simpa [TwoPhaseControls.second, RealSymmetric2.matrix] using
    (Matrix.one_fin_two (α := ℝ)).symm

/-- Helper for Appendix Lemma A.6: the independent raw evaluator is stationary on a
zero-radius diagonal input, with the diagonal's second entry left symbolic. -/
theorem independentRawStep_zeroRadius_diagonal
    (d : ℝ) (p : ℝ) (control : PlanarDFPControl) :
    independentRawStep (Matrix.diagonal ![(0 : ℝ), d]) ![(1 : ℝ), p * 0] control =
      (Matrix.diagonal ![(0 : ℝ), d], ![(1 : ℝ), 0]) := by
  have hzero : (Matrix.diagonal ![(0 : ℝ), d]) *ᵥ (![(1 : ℝ), p * 0] : Fin 2 → ℝ) = 0 := by
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  unfold independentRawStep
  rw [hzero]
  simp [Matrix.inverseDFPUpdate]

/-- Helper for Appendix Lemma A.6: scalar substitutions in the zero-radius independent
raw evaluator reduce to the symbolic diagonal bridge. -/
theorem independentRawStep_zeroRadius_scaled
    (a d p : ℝ) (control : PlanarDFPControl) :
    independentRawStep
        (Matrix.diagonal ![a * (0 : ℝ) ^ 2, d]) ![(1 : ℝ), p * 0] control =
      (Matrix.diagonal ![(0 : ℝ), d], ![(1 : ℝ), 0]) := by
  have hmatrix :
      Matrix.diagonal ![a * (0 : ℝ) ^ 2, d] = Matrix.diagonal ![(0 : ℝ), d] := by
    congr 1
    norm_num
  rw [hmatrix]
  exact independentRawStep_zeroRadius_diagonal d p control

end DFP.TwoLeg.Mixed
