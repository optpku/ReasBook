module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoLeg.NormJet

/-- Along any real coordinate path with the polynomial slow-graph shape jet, the normalized
first-leg decrease of the gradient norm is asymptotic to `2 * ε ^ 3` from the right. -/
theorem firstLegGradientNormDrop (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) ~[𝓝[>] 0]
      (fun ε : ℝ ↦ 2 * ε ^ 3) := by
  have hInitial := slowInitialGradientRemainder p h h_pJet
  have hIntermediate := slowIntermediateGradientRemainder p h h_pJet
  have hFourSix : (4 : ℕ) < 6 := by
    norm_num
  have hSixFour :
      (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourSix).isBigO
  have hInitialFour :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (1 + 2 * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    hInitial.trans hSixFour
  have hFourSeven : (4 : ℕ) < 7 := by
    norm_num
  have hSevenFour :
      (fun ε : ℝ ↦ ε ^ 7) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourSeven).isBigO
  have hIntermediateFour :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
          (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hIntermediate.trans hSevenFour
  have hRemainderDifference := hInitialFour.sub hIntermediateFour
  have hFourthTerm :
      (fun ε : ℝ ↦ (4 : ℝ) * ε ^ 4) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 4) (𝓝 0)).const_mul_left 4
  have hSixthTerm :
      (fun ε : ℝ ↦ (112 / 5 : ℝ) * ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hSixFour.const_mul_left (112 / 5 : ℝ)
  have hPolynomial := hFourthTerm.add hSixthTerm
  have hCombined := hRemainderDifference.add hPolynomial
  have hIdentity (ε : ℝ) :
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (1 + 2 * ε ^ 4) -
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
          (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6))) +
          (4 * ε ^ 4 + (112 / 5) * ε ^ 6) =
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3 := by
    ring
  have hFourthOrder :
      (fun ε : ℝ ↦
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    hCombined.congr_left hIdentity
  have hThreeFour : (3 : ℕ) < 4 := by
    norm_num
  have hThirdOrderLittle :
      (fun ε : ℝ ↦
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    hFourthOrder.trans_isLittleO (Asymptotics.isLittleO_pow_pow hThreeFour)
  have hThirdOrderLittleRight :
      (fun ε : ℝ ↦
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3) =o[𝓝[>] 0] (fun ε : ℝ ↦ ε ^ 3) :=
    hThirdOrderLittle.mono inf_le_left
  have hTwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  have hScaled := hThirdOrderLittleRight.const_mul_right hTwoNe
  have hFunctionDifference :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
          (fun ε : ℝ ↦ 2 * ε ^ 3) =
        (fun ε : ℝ ↦
          ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
            (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
              2 * ε ^ 3) := by
    rfl
  unfold Asymptotics.IsEquivalent
  rw [hFunctionDifference]
  exact hScaled

/-- Along any real coordinate path with the polynomial slow-graph shape and high-eigenvalue
jets, the normalized second-leg increase of the gradient norm is asymptotic to `2 * ε ^ 3`
from the right. -/
theorem secondLegGradientNormRise (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) ~[𝓝[>] 0]
      (fun ε : ℝ ↦ 2 * ε ^ 3) := by
  have hFinal := slowFinalGradientRemainder p h h_pJet h_hJet
  have hIntermediate := slowIntermediateGradientRemainder p h h_pJet
  have hFourSeven : (4 : ℕ) < 7 := by
    norm_num
  have hSevenFour :
      (fun ε : ℝ ↦ ε ^ 7) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourSeven).isBigO
  have hFinalFour :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hFinal.trans hSevenFour
  have hIntermediateFour :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
          (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hIntermediate.trans hSevenFour
  have hRemainderDifference := hFinalFour.sub hIntermediateFour
  have hFourthTerm :
      (fun ε : ℝ ↦ (-5 / 2 : ℝ) * ε ^ 4) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 4) (𝓝 0)).const_mul_left
      (-5 / 2 : ℝ)
  have hFourSix : (4 : ℕ) < 6 := by
    norm_num
  have hSixFour :
      (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hFourSix).isBigO
  have hSixthTerm :
      (fun ε : ℝ ↦ (228 / 5 : ℝ) * ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) :=
    hSixFour.const_mul_left (228 / 5 : ℝ)
  have hPolynomial := hFourthTerm.add hSixthTerm
  have hCombined := hRemainderDifference.add hPolynomial
  have hIdentity (ε : ℝ) :
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6) -
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
          (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6))) +
          ((-5 / 2) * ε ^ 4 + (228 / 5) * ε ^ 6) =
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3 := by
    ring
  have hFourthOrder :
      (fun ε : ℝ ↦
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    hCombined.congr_left hIdentity
  have hThreeFour : (3 : ℕ) < 4 := by
    norm_num
  have hThirdOrderLittle :
      (fun ε : ℝ ↦
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    hFourthOrder.trans_isLittleO (Asymptotics.isLittleO_pow_pow hThreeFour)
  have hThirdOrderLittleRight :
      (fun ε : ℝ ↦
        ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
            2 * ε ^ 3) =o[𝓝[>] 0] (fun ε : ℝ ↦ ε ^ 3) :=
    hThirdOrderLittle.mono inf_le_left
  have hTwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  have hScaled := hThirdOrderLittleRight.const_mul_right hTwoNe
  have hFunctionDifference :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
          (fun ε : ℝ ↦ 2 * ε ^ 3) =
        (fun ε : ℝ ↦
          ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
            (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) -
              2 * ε ^ 3) := by
    rfl
  unfold Asymptotics.IsEquivalent
  rw [hFunctionDifference]
  exact hScaled

/-- Along any real coordinate path with the polynomial slow-graph coordinate jets, every
sufficiently small positive point has a strict gradient-norm valley, also after scaling all
three norms by any positive amplitude. -/
theorem eventuallyStrictGradientNormValley (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε ↦ ε ^ 5)) :
    ∀ᶠ ε in 𝓝[>] 0, ∀ G : ℝ, 0 < G →
      G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm <
          G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm ∧
        G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm <
          G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm := by
  have h_drop := firstLegGradientNormDrop p h h_pJet
  have h_rise := secondLegGradientNormRise p h h_pJet h_hJet
  have hTwoPos : (0 : ℝ) < 2 := by
    norm_num
  have h_positive : ∀ᶠ ε in 𝓝[>] 0, 0 < (2 : ℝ) * ε ^ 3 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos hTwoPos (pow_pos hε 3)
  have h_drop_pos := h_drop.eventually_pos h_positive
  have h_rise_pos := h_rise.eventually_pos h_positive
  filter_upwards [h_drop_pos, h_rise_pos] with ε hdrop hrise
  intro G hG
  constructor
  · exact mul_lt_mul_of_pos_left (sub_pos.mp hdrop) hG
  · exact mul_lt_mul_of_pos_left (sub_pos.mp hrise) hG

end DFP.TwoLeg.NormJet
