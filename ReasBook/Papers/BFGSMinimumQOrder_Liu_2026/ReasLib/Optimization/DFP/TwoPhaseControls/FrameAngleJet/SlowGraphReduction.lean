module

public import ReasLib.Analysis.Asymptotics.ArctanTaylor
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.Analysis.Asymptotics.ArctanTaylor
import all ReasLib.Geometry.Euclidean.Plane.SignedAngle
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables

/-!
# Slow-graph frame-angle reduction to one scalar germ

This companion isolates the scalar tangent-coordinate expansion needed for the
slow-graph frame-angle jet and accounts for the cubic arctangent correction.
-/

public section

noncomputable section

open Filter
open Asymptotics
open scoped Matrix Topology

namespace DFP.TwoLeg

/-- Tangent coordinate of the relative two-leg frame along the polynomial slow graph. -/
def slowGraphRelativeFrameSlope (ε : ℝ) : ℝ :=
  let x := slowGraphJetPath ε
  let M := DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
    DFP.SecondLeg.frame x.1 x.2.1 x.2.2
  M 1 0 / M 0 0

/-- Required sixth-order polynomial for the relative-frame tangent coordinate. -/
def slowGraphRelativeFrameSlopePolynomial (ε : ℝ) : ℝ :=
  -3 * ε ^ 2 - (196 / 5) * ε ^ 5 - (17 / 5) * ε ^ 6

/-- The slow-graph frame-angle observable is the arctangent of the relative-frame
slope. -/
theorem slowGraphFrameAngle_eq_arctan_relativeFrameSlope (ε : ℝ) :
    (observableMap (slowGraphJetPath ε)).frameAngleIncrement =
      Real.arctan (slowGraphRelativeFrameSlope ε) := by
  rw [slowGraphJetPath_apply, observableMap_frameAngleIncrement]
  simp only [slowGraphRelativeFrameSlope, slowGraphJetPath_apply,
    EuclideanPlane.SignedAngle.coordinate]

/-- Computing the single relative-frame slope germ through order six implies the
order-seven slow-graph frame-angle expansion. The raw sixth-order coefficient
`-17 / 5` combines with the cubic arctangent correction `9` to give `28 / 5`. -/
theorem slowGraphFrameAngleRemainder_of_relativeFrameSlope
    (hSlopeGerm : EqModPow 7 slowGraphRelativeFrameSlope
      slowGraphRelativeFrameSlopePolynomial) :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).frameAngleIncrement -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  have hSlope := EqModPow.to_isBigO hSlopeGerm
  let c : ℝ → ℝ := fun ε ↦ -3 - (196 / 5) * ε ^ 3 - (17 / 5) * ε ^ 4
  have hc : ContinuousAt c 0 := by
    dsimp [c]
    fun_prop
  have hPolynomial : slowGraphRelativeFrameSlopePolynomial =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    have hraw := (isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0)).mul hc.isBigO
    refine hraw.congr' ?_ ?_
    · exact Eventually.of_forall (fun ε ↦ by
        dsimp [slowGraphRelativeFrameSlopePolynomial, c]
        ring)
    · exact Eventually.of_forall (fun ε ↦ by simp)
  have hSlopeErrorOrderTwo := hSlope.trans_isLittleO
    (isLittleO_pow_pow (by norm_num : 2 < 7)) |>.isBigO
  have hSlopeOrder : slowGraphRelativeFrameSlope =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    have hsum := hSlopeErrorOrderTwo.add hPolynomial
    exact hsum.congr'
      (Eventually.of_forall fun ε ↦ by ring)
      (Eventually.of_forall fun _ ↦ rfl)
  have hpowTwo : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by fun_prop
    convert hcont.tendsto using 1
    all_goals norm_num
  have hSlopeTendsto : Tendsto slowGraphRelativeFrameSlope (𝓝 0) (𝓝 0) :=
    hSlopeOrder.trans_tendsto hpowTwo
  let cTail : ℝ → ℝ := fun ε ↦ -(196 / 5) - (17 / 5) * ε
  have hcTail : ContinuousAt cTail 0 := by
    dsimp [cTail]
    fun_prop
  have hPolynomialTail :
      (fun ε : ℝ ↦ slowGraphRelativeFrameSlopePolynomial ε - (-3 * ε ^ 2)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hraw := (isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).mul hcTail.isBigO
    refine hraw.congr' ?_ ?_
    · exact Eventually.of_forall (fun ε ↦ by
        dsimp [slowGraphRelativeFrameSlopePolynomial, cTail]
        ring)
    · exact Eventually.of_forall (fun ε ↦ by simp)
  have hSlopeDiff :
      (fun ε : ℝ ↦ slowGraphRelativeFrameSlope ε - (-3 * ε ^ 2)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum := hSlope.trans_isLittleO
      (isLittleO_pow_pow (by norm_num : 5 < 7)) |>.isBigO
      |>.add hPolynomialTail
    exact hsum.congr'
      (Eventually.of_forall fun ε ↦ by ring)
      (Eventually.of_forall fun _ ↦ rfl)
  have hSquare := hSlopeOrder.pow 2
  have hSquare' : (fun ε : ℝ ↦ slowGraphRelativeFrameSlope ε ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_mul, Nat.reduceMul] using hSquare
  have hScale : (fun ε : ℝ ↦ -3 * ε ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) :=
    (isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0)).const_mul_left (-3)
  have hMixed : (fun ε : ℝ ↦ slowGraphRelativeFrameSlope ε * (-3 * ε ^ 2)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_add, Nat.reduceAdd] using hSlopeOrder.mul hScale
  have hScaleSquare : (fun ε : ℝ ↦ (-3 * ε ^ 2) ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_mul, Nat.reduceMul] using hScale.pow 2
  have hCubeFactor :
      (fun ε : ℝ ↦ slowGraphRelativeFrameSlope ε ^ 2 +
        slowGraphRelativeFrameSlope ε * (-3 * ε ^ 2) + (-3 * ε ^ 2) ^ 2) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [add_assoc] using hSquare'.add (hMixed.add hScaleSquare)
  have hCubeDiffRaw := hSlopeDiff.mul hCubeFactor
  have hCubeDiffNine :
      (fun ε : ℝ ↦ slowGraphRelativeFrameSlope ε ^ 3 - (-3 * ε ^ 2) ^ 3) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 9) := by
    refine hCubeDiffRaw.congr' ?_ ?_
    · exact Eventually.of_forall (fun ε ↦ by ring)
    · exact Eventually.of_forall (fun ε ↦ by ring)
  have hCubeDiff :
      (fun ε : ℝ ↦ slowGraphRelativeFrameSlope ε ^ 3 - (-3 * ε ^ 2) ^ 3) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hCubeDiffNine.trans_isLittleO
      (isLittleO_pow_pow (by norm_num : 7 < 9)) |>.isBigO
  have hArctanEight :
      (fun ε : ℝ ↦ Real.arctan (slowGraphRelativeFrameSlope ε) -
        (slowGraphRelativeFrameSlope ε - slowGraphRelativeFrameSlope ε ^ 3 / 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) := by
    simpa using Real.arctan_comp_sub_cubic_isBigO hSlopeTendsto hSlopeOrder
  have hArctan := hArctanEight.trans_isLittleO
    (isLittleO_pow_pow (by norm_num : 7 < 8)) |>.isBigO
  have hCubeCorrection := hCubeDiff.const_mul_left (-(1 / 3))
  have hArctanPolynomial :
      (fun ε : ℝ ↦ Real.arctan (slowGraphRelativeFrameSlope ε) -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 7) := by
    have hsum := hArctan.add (hSlope.add hCubeCorrection)
    exact hsum.congr'
      (Eventually.of_forall fun ε ↦ by
        dsimp [slowGraphRelativeFrameSlopePolynomial]
        ring)
      (Eventually.of_forall fun _ ↦ rfl)
  simpa only [slowGraphFrameAngle_eq_arctan_relativeFrameSlope] using
    hArctanPolynomial

end DFP.TwoLeg
