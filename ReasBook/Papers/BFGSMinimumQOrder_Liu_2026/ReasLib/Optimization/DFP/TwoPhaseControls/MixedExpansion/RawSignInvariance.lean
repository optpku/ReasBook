module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.InverseUpdate.Scaling
public import ReasLib.Optimization.DFP.SpectralRecovery
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.InverseUpdate.Scaling
import all ReasLib.Optimization.DFP.SpectralRecovery

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-!
The raw two-leg evaluator has an oriented-frame ambiguity.  This file isolates the
algebraic part of that ambiguity: negating an incoming gradient negates the updated
gradient but leaves the DFP inverse-Hessian update unchanged, and the recovery quotients
are invariant under simultaneous negation of both gradient coordinates.
-/

/-- One DFP raw step is equivariant under negating its
incoming gradient; its updated matrix is unchanged and its updated gradient is negated. -/
theorem independentRawStep_negate_gradient
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    independentRawStep H (-g) control =
      ((independentRawStep H g control).1,
        -(independentRawStep H g control).2) := by
  let v : Fin 2 → ℝ := H *ᵥ g
  let α : ℝ := control.tau * (g ⬝ᵥ v) / (v ⬝ᵥ (control.matrix *ᵥ v))
  let s : Fin 2 → ℝ := -(α • v)
  let y : Fin 2 → ℝ := control.matrix *ᵥ s
  have hraw : independentRawStep H g control =
      (Matrix.inverseDFPUpdate H s y, g + y) := by
    simp only [independentRawStep, v, α, s, y]
  have hnegv : H *ᵥ (-g) = -v := by
    simp only [v, Matrix.mulVec_neg]
  have hdotg : (-g) ⬝ᵥ (-v) = g ⬝ᵥ v := by
    rw [neg_dotProduct, dotProduct_neg]
    ring
  have hdotv : (-v) ⬝ᵥ (control.matrix *ᵥ (-v)) =
      v ⬝ᵥ (control.matrix *ᵥ v) := by
    rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg]
    ring
  have halpha : control.tau * ((-g) ⬝ᵥ (H *ᵥ (-g))) /
      ((H *ᵥ (-g)) ⬝ᵥ (control.matrix *ᵥ (H *ᵥ (-g)))) = α := by
    rw [hnegv, hdotg, hdotv]
  have halpha' : control.tau * ((-g) ⬝ᵥ (-v)) /
      ((-v) ⬝ᵥ (control.matrix *ᵥ (-v))) = α := by
    rw [hdotg, hdotv]
  have hs : -(α • (-v)) = -s := by
    simp [s]
  have hmulneg (w : Fin 2 → ℝ) : control.matrix *ᵥ (-w) =
      -(control.matrix *ᵥ w) := by
    exact Matrix.mulVec_neg w control.matrix
  have hy : control.matrix *ᵥ (-(α • (-v))) = -y := by
    rw [hs]
    simpa only [y] using hmulneg s
  have halpha'' : control.tau * ((-g) ⬝ᵥ (-v)) /
      ((-v) ⬝ᵥ (-(control.matrix *ᵥ v))) = α := by
    rw [← Matrix.mulVec_neg v control.matrix]
    exact halpha'
  have hy' : -(control.matrix *ᵥ (α • (-v))) = -y := by
    rw [← Matrix.mulVec_neg (α • (-v)) control.matrix]
    exact hy
  have hnegraw : independentRawStep H (-g) control =
      (Matrix.inverseDFPUpdate H (-s) (-y), -g + (-y)) := by
    simp only [independentRawStep, hnegv, Matrix.mulVec_neg]
    rw [halpha'', hs, hy']
  rw [hnegraw, hraw]
  have hupdate : Matrix.inverseDFPUpdate H (-s) (-y) =
      Matrix.inverseDFPUpdate H s y := by
    have hnegone : (-1 : ℝ) ≠ 0 := by norm_num
    have hscaled := Matrix.inverseDFPUpdate_smul_pair H s y
      (c := (-1 : ℝ)) hnegone
    have hsneg : (-1 : ℝ) • s = -s := by
      ext i
      simp
    have hyneg : (-1 : ℝ) • y = -y := by
      ext i
      simp
    rw [hsneg, hyneg] at hscaled
    exact hscaled
  rw [hupdate]
  apply Prod.ext
  · rfl
  · ext i
    simp [add_comm]

/-- Simultaneous negation of the two gradient coordinates
does not change the recovered radius quotient. -/
theorem recoveryRadius_neg_neg
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) :
    CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus (-gammaMinus) (-gammaPlus) =
      CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus := by
  unfold CycleBoundaryState.recoveryRadius
  ring

/-- Simultaneous negation of the two gradient coordinates
does not change the recovered shape quotient. -/
theorem recoveryShape_neg_neg
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) :
    CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus (-gammaMinus) (-gammaPlus) =
      CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus := by
  unfold CycleBoundaryState.recoveryShape
  ring

/-- A recovered triple is unchanged when both oriented
gradient coordinates are negated. -/
theorem recoveryTriple_neg_neg
    (lambdaMinus lambdaPlus gammaMinus gammaPlus : ℝ) :
    (CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus (-gammaMinus) (-gammaPlus),
      CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus (-gammaMinus) (-gammaPlus),
      lambdaPlus) =
    (CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus gammaMinus gammaPlus,
      CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus gammaMinus gammaPlus,
      lambdaPlus) := by
  rw [recoveryRadius_neg_neg, recoveryShape_neg_neg]

end DFP.TwoLeg.Mixed
