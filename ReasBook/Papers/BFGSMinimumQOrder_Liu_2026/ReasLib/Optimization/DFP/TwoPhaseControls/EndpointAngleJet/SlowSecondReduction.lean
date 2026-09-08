module

public import ReasLib.Analysis.Asymptotics.ArctanTaylor
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.CoordinateReductionAtBase
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.Analysis.Asymptotics.ArctanTaylor
import all ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.CoordinateReductionAtBase
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

/-!
# Reduction of the slow second endpoint angle to scalar slopes

This companion isolates the two scalar germ estimates that remain after canceling the
common eigenframe and accounting for the cubic arctangent correction.
-/

public section

noncomputable section

open Filter
open Asymptotics
open scoped Topology

namespace DFP.TwoLeg.EndpointAngleJet

/-- Intermediate gradient slope in the first-leg eigenframe along the slow graph. -/
def slowIntermediateSlope (ε : ℝ) : ℝ :=
  let x := DFP.TwoLeg.slowGraphJetPath ε
  ε ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2 /
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1

/-- Final gradient slope in the first-leg eigenframe along the slow graph. -/
def slowFinalSlope (ε : ℝ) : ℝ :=
  let x := DFP.TwoLeg.slowGraphJetPath ε
  DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 1 /
    DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 0

/-- The final slope written in the removable first-leg spectral and gradient
factors used by the second-leg update. -/
theorem slowFinalSlope_apply (ε : ℝ) :
    slowFinalSlope ε =
      let x := DFP.TwoLeg.slowGraphJetPath ε
      let spectral := DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2
      let gradient := DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2
      let L := spectral.1
      let H := spectral.2
      let Q := gradient.1
      let U := gradient.2
      let w₁ := ε * L * Q - 2 * H * U
      let w₂ := H * U - 2 * ε ^ 3 * L * Q
      let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
      let delta := L * Q ^ 2 + H * U ^ 2
      let q := Q - ε ^ 3 * delta * w₁ / (3 * beta)
      let v := U - delta * w₂ / (3 * beta)
      ε ^ 2 * v / q := by
  rfl

/-- Required sixth-order polynomial for the intermediate slope. -/
def slowIntermediateSlopePolynomial (ε : ℝ) : ℝ :=
  ε ^ 2 + (66 / 5) * ε ^ 5 + (7 / 5) * ε ^ 6

/-- Required sixth-order polynomial for the final slope. -/
def slowFinalSlopePolynomial (ε : ℝ) : ℝ :=
  -(38 / 5) * ε ^ 5 + (29 / 5) * ε ^ 6

/-- Evaluation formula for the sixth-order final-slope polynomial. -/
theorem slowFinalSlopePolynomial_apply (ε : ℝ) :
    slowFinalSlopePolynomial ε = -(38 / 5) * ε ^ 5 + (29 / 5) * ε ^ 6 := by
  rfl

theorem slowSecondEndpointAngle_eq_arctan_sub_eventually :
    ∀ᶠ ε in 𝓝 (0 : ℝ),
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).secondEndpointAngleIncrement.toReal =
        Real.arctan (slowFinalSlope ε) -
          Real.arctan (slowIntermediateSlope ε) := by
  have hpath : Tendsto DFP.TwoLeg.slowGraphJetPath (𝓝 (0 : ℝ))
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hcont : ContinuousAt DFP.TwoLeg.slowGraphJetPath 0 := by
      unfold DFP.TwoLeg.slowGraphJetPath DFP.TwoLeg.graphJetPath
      fun_prop
    have hzero : DFP.TwoLeg.slowGraphJetPath 0 =
        ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      norm_num [DFP.TwoLeg.slowGraphJetPath, DFP.TwoLeg.graphJetPath]
    rw [← hzero]
    exact hcont
  have h := hpath.eventually
    DFP.TwoLeg.secondEndpointAngleIncrement_toReal_eq_arctan_sub_eventually
  simpa [slowIntermediateSlope, slowFinalSlope,
    DFP.TwoLeg.slowGraphJetPath_apply] using h

/-- The two seventh-order scalar slope remainders imply the full `slowSecond` remainder. -/
theorem slowSecond_of_slope_remainders
    (hIntermediate :
      (fun ε : ℝ ↦ slowIntermediateSlope ε -
        slowIntermediateSlopePolynomial ε) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 7))
    (hFinal :
      (fun ε : ℝ ↦ slowFinalSlope ε -
        slowFinalSlopePolynomial ε) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 7)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).secondEndpointAngleIncrement.toReal -
        (-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let cI : ℝ → ℝ := fun ε ↦ 1 + (66 / 5) * ε ^ 3 + (7 / 5) * ε ^ 4
  have hcI : ContinuousAt cI 0 := by
    dsimp [cI]
    fun_prop
  have hIntermediatePolynomial : slowIntermediateSlopePolynomial =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    have hraw := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0)).mul
      hcI.isBigO
    refine hraw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall (fun ε ↦ by
        dsimp [slowIntermediateSlopePolynomial, cI]
        ring)
    · exact Filter.Eventually.of_forall (fun ε ↦ by simp)
  have hIntermediateErrorOrderTwo := hIntermediate.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 7)) |>.isBigO
  have hIntermediateOrder : slowIntermediateSlope =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    have hsum := hIntermediateErrorOrderTwo.add hIntermediatePolynomial
    exact hsum.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hpowTwo : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by fun_prop
    convert hcont.tendsto using 1
    all_goals norm_num
  have hIntermediateTendsto : Tendsto slowIntermediateSlope (𝓝 0) (𝓝 0) :=
    hIntermediateOrder.trans_tendsto hpowTwo
  let cF : ℝ → ℝ := fun ε ↦ -(38 / 5) + (29 / 5) * ε
  have hcF : ContinuousAt cF 0 := by
    dsimp [cF]
    fun_prop
  have hFinalPolynomial : slowFinalSlopePolynomial =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hraw := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).mul
      hcF.isBigO
    refine hraw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall (fun ε ↦ by
        dsimp [slowFinalSlopePolynomial, cF]
        ring)
    · exact Filter.Eventually.of_forall (fun ε ↦ by simp)
  have hFinalErrorOrderFive := hFinal.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 7)) |>.isBigO
  have hFinalOrder : slowFinalSlope =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum := hFinalErrorOrderFive.add hFinalPolynomial
    exact hsum.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by fun_prop
    convert hcont.tendsto using 1
    all_goals norm_num
  have hFinalTendsto : Tendsto slowFinalSlope (𝓝 0) (𝓝 0) :=
    hFinalOrder.trans_tendsto hpowFive
  let cTail : ℝ → ℝ := fun ε ↦ 66 / 5 + (7 / 5) * ε
  have hcTail : ContinuousAt cTail 0 := by
    dsimp [cTail]
    fun_prop
  have hIntermediateTail :
      (fun ε : ℝ ↦ slowIntermediateSlopePolynomial ε - ε ^ 2) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hraw := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).mul
      hcTail.isBigO
    refine hraw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall (fun ε ↦ by
        dsimp [slowIntermediateSlopePolynomial, cTail]
        ring)
    · exact Filter.Eventually.of_forall (fun ε ↦ by simp)
  have hIntermediateDiff :
      (fun ε : ℝ ↦ slowIntermediateSlope ε - ε ^ 2) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum := hIntermediate.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 7)) |>.isBigO
      |>.add hIntermediateTail
    exact hsum.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hSquare := hIntermediateOrder.pow 2
  have hSquare' : (fun ε : ℝ ↦ slowIntermediateSlope ε ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_mul, Nat.reduceMul] using hSquare
  have hScale : (fun ε : ℝ ↦ ε ^ 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) :=
    Asymptotics.isBigO_refl _ _
  have hMixed : (fun ε : ℝ ↦ slowIntermediateSlope ε * ε ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_add, Nat.reduceAdd] using hIntermediateOrder.mul hScale
  have hScaleSquare : (fun ε : ℝ ↦ (ε ^ 2) ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_mul, Nat.reduceMul] using hScale.pow 2
  have hCubeFactor :
      (fun ε : ℝ ↦ slowIntermediateSlope ε ^ 2 +
        slowIntermediateSlope ε * ε ^ 2 + (ε ^ 2) ^ 2) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [add_assoc] using hSquare'.add (hMixed.add hScaleSquare)
  have hCubeDiffRaw := hIntermediateDiff.mul hCubeFactor
  have hCubeDiffNine :
      (fun ε : ℝ ↦ slowIntermediateSlope ε ^ 3 - ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 9) := by
    refine hCubeDiffRaw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall (fun ε ↦ by ring)
    · exact Filter.Eventually.of_forall (fun ε ↦ by ring)
  have hCubeDiff :
      (fun ε : ℝ ↦ slowIntermediateSlope ε ^ 3 - ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hCubeDiffNine.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 9)) |>.isBigO
  have hArctanIntermediateEight :
      (fun ε : ℝ ↦ Real.arctan (slowIntermediateSlope ε) -
        (slowIntermediateSlope ε - slowIntermediateSlope ε ^ 3 / 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) := by
    simpa using Real.arctan_comp_sub_cubic_isBigO
      hIntermediateTendsto hIntermediateOrder
  have hArctanIntermediate := hArctanIntermediateEight.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 8)) |>.isBigO
  have hCubeCorrection := hCubeDiff.const_mul_left (-(1 / 3))
  have hArctanIntermediatePolynomial :
      (fun ε : ℝ ↦ Real.arctan (slowIntermediateSlope ε) -
        (slowIntermediateSlopePolynomial ε - (1 / 3) * ε ^ 6)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 7) := by
    have hsum := hArctanIntermediate.add (hIntermediate.add hCubeCorrection)
    exact hsum.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hArctanFinalTwenty :
      (fun ε : ℝ ↦ Real.arctan (slowFinalSlope ε) -
        (slowFinalSlope ε - slowFinalSlope ε ^ 3 / 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 20) := by
    simpa using Real.arctan_comp_sub_cubic_isBigO hFinalTendsto hFinalOrder
  have hArctanFinal := hArctanFinalTwenty.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 20)) |>.isBigO
  have hFinalCubeFifteen : (fun ε : ℝ ↦ slowFinalSlope ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 15) := by
    simpa only [← pow_mul, Nat.reduceMul] using hFinalOrder.pow 3
  have hFinalCube := hFinalCubeFifteen.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 15)) |>.isBigO
  have hFinalCubeCorrection := hFinalCube.const_mul_left (-(1 / 3))
  have hArctanFinalPolynomial :
      (fun ε : ℝ ↦ Real.arctan (slowFinalSlope ε) -
        slowFinalSlopePolynomial ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 7) := by
    have hsum := hArctanFinal.add (hFinal.add hFinalCubeCorrection)
    exact hsum.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hDifference := hArctanFinalPolynomial.add hArctanIntermediatePolynomial.neg_left
  have hTarget :
      (fun ε : ℝ ↦ Real.arctan (slowFinalSlope ε) -
          Real.arctan (slowIntermediateSlope ε) -
        (-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 7) := by
    refine hDifference.congr' ?_ ?_
    · exact Filter.Eventually.of_forall (fun ε ↦ by
        dsimp [slowIntermediateSlopePolynomial, slowFinalSlopePolynomial]
        ring)
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  refine hTarget.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [slowSecondEndpointAngle_eq_arctan_sub_eventually] with ε hε
  rw [hε]

end DFP.TwoLeg.EndpointAngleJet
