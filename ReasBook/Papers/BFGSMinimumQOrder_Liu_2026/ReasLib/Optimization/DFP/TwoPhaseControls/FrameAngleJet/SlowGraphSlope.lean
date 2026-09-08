module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet.SlowGraphReduction
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.QuotientGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Continuity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Continuity
import all ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
import all ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet.SlowGraphReduction
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.QuotientGerm

/-!
# The scalar slow-graph frame slope

This companion combines the independently verified raw frame-entry germs, cancels
the two eigenvector normalizations, and proves the scalar slope germ required by
`SlowGraphReduction`.
-/

public section

noncomputable section

open Filter
open Asymptotics
open scoped Matrix Topology

namespace DFP.TwoLeg

/-- Four compatible raw frame-entry germs determine the order-eight germ of their
relative-frame tangent quotient. -/
theorem rawFrameQuotient_algebra
    (E₁ X₁ E₂ X₂ : ℝ → ℝ)
    (hE₁ : EqModPow 8 E₁
      (fun ε => ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6))
    (hX₁ : EqModPow 8 X₁
      (fun ε => 1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7))
    (hE₂ : EqModPow 8 E₂
      (fun ε => 2 * ε ^ 2 + (286 / 5) * ε ^ 5 - (73 / 5) * ε ^ 6))
    (hX₂ : EqModPow 8 X₂
      (fun ε => 1 + 8 * ε ^ 3 - 6 * ε ^ 4 + (1104 / 5) * ε ^ 6 -
        (1414 / 5) * ε ^ 7))
    (hE₁Cont : ContinuousAt E₁ 0) (hX₁Cont : ContinuousAt X₁ 0)
    (hE₂Cont : ContinuousAt E₂ 0) (hX₂Cont : ContinuousAt X₂ 0) :
    EqModPow 8
      (fun ε => -(E₁ ε * X₂ ε + X₁ ε * E₂ ε) /
        (X₁ ε * X₂ ε - E₁ ε * E₂ ε))
      (fun ε => -3 * ε ^ 2 - (196 / 5) * ε ^ 5 - (17 / 5) * ε ^ 6) := by
  let E₁P : ℝ → ℝ := fun ε => ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6
  let X₁P : ℝ → ℝ := fun ε =>
    1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7
  let E₂P : ℝ → ℝ := fun ε =>
    2 * ε ^ 2 + (286 / 5) * ε ^ 5 - (73 / 5) * ε ^ 6
  let X₂P : ℝ → ℝ := fun ε =>
    1 + 8 * ε ^ 3 - 6 * ε ^ 4 + (1104 / 5) * ε ^ 6 - (1414 / 5) * ε ^ 7
  let num : ℝ → ℝ := fun ε => -(E₁ ε * X₂ ε + X₁ ε * E₂ ε)
  let den : ℝ → ℝ := fun ε => X₁ ε * X₂ ε - E₁ ε * E₂ ε
  let numFullP : ℝ → ℝ := fun ε => -(E₁P ε * X₂P ε + X₁P ε * E₂P ε)
  let denFullP : ℝ → ℝ := fun ε => X₁P ε * X₂P ε - E₁P ε * E₂P ε
  let numP : ℝ → ℝ := fun ε =>
    -3 * ε ^ 2 - (286 / 5) * ε ^ 5 + (148 / 5) * ε ^ 6
  let denP : ℝ → ℝ := fun ε =>
    1 + 6 * ε ^ 3 - 11 * ε ^ 4 + (1054 / 5) * ε ^ 6 - (1978 / 5) * ε ^ 7
  let slopeP : ℝ → ℝ := fun ε =>
    -3 * ε ^ 2 - (196 / 5) * ε ^ 5 - (17 / 5) * ε ^ 6
  have hE₁PCont : ContinuousAt E₁P 0 := by fun_prop
  have hX₁PCont : ContinuousAt X₁P 0 := by fun_prop
  have hE₂PCont : ContinuousAt E₂P 0 := by fun_prop
  have hX₂PCont : ContinuousAt X₂P 0 := by fun_prop
  have hnumFull : EqModPow 8 num numFullP := by
    have hleft := hE₁.mul hX₂ hE₁PCont hX₂Cont
    have hright := hX₁.mul hE₂ hX₁PCont hE₂Cont
    exact (hleft.add hright).neg.congr (fun _ => rfl) (fun _ => rfl)
  have hdenFull : EqModPow 8 den denFullP := by
    have hleft := hX₁.mul hX₂ hX₁PCont hX₂Cont
    have hright := hE₁.mul hE₂ hE₁PCont hE₂Cont
    exact (hleft.sub hright).congr (fun _ => rfl) (fun _ => rfl)
  have hnumTrunc : EqModPow 8 numFullP numP := by
    apply EqModPow.of_factor
      (q := fun ε =>
        -(432 / 5) + (2642 / 5) * ε - (309 / 5) * ε ^ 2 + 540 * ε ^ 3 +
          (64258 / 25) * ε ^ 4 - (40044 / 25) * ε ^ 5)
    · fun_prop
    · intro ε
      dsimp only [numFullP, numP, E₁P, X₁P, E₂P, X₂P]
      ring
  have hdenTrunc : EqModPow 8 denFullP denP := by
    apply EqModPow.of_factor
      (q := fun ε =>
        193 / 5 - (1968 / 5) * ε - (1584 / 5) * ε ^ 2 +
          (6356 / 5) * ε ^ 3 + 1281 * ε ^ 4 - (327252 / 25) * ε ^ 5 +
          (364812 / 25) * ε ^ 6)
    · fun_prop
    · intro ε
      dsimp only [denFullP, denP, E₁P, X₁P, E₂P, X₂P]
      ring
  have hnum : EqModPow 8 num numP := hnumFull.trans hnumTrunc
  have hden : EqModPow 8 den denP := hdenFull.trans hdenTrunc
  have hpoly : EqModPow 8 numP (fun ε => denP ε * slopeP ε) := by
    apply EqModPow.of_factor
      (q := fun ε =>
        (21690 - 39940 * ε - 935 * ε ^ 2 + 206584 * ε ^ 3 -
          369770 * ε ^ 4 - 33626 * ε ^ 5) / 25)
    · fun_prop
    · intro ε
      dsimp only [numP, denP, slopeP]
      ring
  have hdenPCont : ContinuousAt denP 0 := by fun_prop
  have hslopePCont : ContinuousAt slopeP 0 := by fun_prop
  have hdenCont : ContinuousAt den 0 :=
    (hX₁Cont.mul hX₂Cont).sub (hE₁Cont.mul hE₂Cont)
  have hE₁Zero := EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hE₁
  have hX₁Zero := EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hX₁
  have hE₂Zero := EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hE₂
  have hX₂Zero := EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hX₂
  have hdenZero : den 0 ≠ 0 := by
    norm_num [den, E₁P, X₁P, E₂P, X₂P] at hE₁Zero hX₁Zero hE₂Zero hX₂Zero ⊢
    simp [hE₁Zero, hX₁Zero, hE₂Zero, hX₂Zero]
  have hquot := EqModPow.div_approx hnum hden hpoly hdenPCont
    hslopePCont hdenCont hdenZero
  simpa only [num, den, slopeP] using hquot

/-- The normalization of the two canonical low eigenvectors cancels from the
tangent coordinate of their frame product. -/
private theorem relativeFrameSlope_lowVector_mul (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ)
    (h₁ : RealSymmetric2.lowDenom a₁ b₁ d₁ ≠ 0)
    (h₂ : RealSymmetric2.lowDenom a₂ b₂ d₂ ≠ 0) :
    (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
        EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) 1 0 /
      (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
        EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) 0 0 =
      -(b₁ * (d₂ - RealSymmetric2.low a₂ b₂ d₂) +
          (d₁ - RealSymmetric2.low a₁ b₁ d₁) * b₂) /
        ((d₁ - RealSymmetric2.low a₁ b₁ d₁) *
            (d₂ - RealSymmetric2.low a₂ b₂ d₂) - b₁ * b₂) := by
  unfold EuclideanPlane.frame
  simp only [Matrix.mul_apply, Fin.sum_univ_two, EuclideanPlane.perp_apply,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, PiLp.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  field_simp [h₁, h₂]
  ring

/-- Along the polynomial slow graph, the relative-frame tangent coordinate has
the stated order-seven germ. -/
theorem slowGraphRelativeFrameSlopeGerm :
    EqModPow 7 slowGraphRelativeFrameSlope slowGraphRelativeFrameSlopePolynomial := by
  let A₁ : ℝ → ℝ := fun ε =>
    let x := slowGraphJetPath ε
    DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0
  let E₁ : ℝ → ℝ := fun ε =>
    let x := slowGraphJetPath ε
    DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1
  let D₁ : ℝ → ℝ := fun ε =>
    let x := slowGraphJetPath ε
    DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1
  let X₁ : ℝ → ℝ := fun ε =>
    D₁ ε - RealSymmetric2.low (A₁ ε) (E₁ ε) (D₁ ε)
  let A₂ : ℝ → ℝ := fun ε =>
    let x := slowGraphJetPath ε
    DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0
  let E₂ : ℝ → ℝ := fun ε =>
    let x := slowGraphJetPath ε
    DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1
  let D₂ : ℝ → ℝ := fun ε =>
    let x := slowGraphJetPath ε
    DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1
  let X₂ : ℝ → ℝ := fun ε =>
    D₂ ε - RealSymmetric2.low (A₂ ε) (E₂ ε) (D₂ ε)
  rcases slowGraphRawFrameGerms with ⟨hE₁, hX₁, hE₂, hX₂⟩
  have hpathCont : ContinuousAt slowGraphJetPath 0 := by
    unfold slowGraphJetPath graphJetPath
    fun_prop
  have hpathZero : slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [slowGraphJetPath_apply]
    norm_num
  have hfirstEntry (i j : Fin 2) : ContinuousAt
      (fun ε =>
        let x := slowGraphJetPath ε
        DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 i j) 0 := by
    have houter := DFP.FirstLeg.outputMetricEntry_continuousAt i j
    rw [← hpathZero] at houter
    simpa only [Function.comp_def] using houter.comp hpathCont
  have hsecondEntry (i j : Fin 2) : ContinuousAt
      (fun ε =>
        let x := slowGraphJetPath ε
        DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 i j) 0 := by
    have houter := DFP.SecondLeg.outputMetricEntry_continuousAt i j
    rw [← hpathZero] at houter
    simpa only [Function.comp_def] using houter.comp hpathCont
  have hA₁Cont : ContinuousAt A₁ 0 := by simpa only [A₁] using hfirstEntry 0 0
  have hE₁Cont : ContinuousAt E₁ 0 := by simpa only [E₁] using hfirstEntry 0 1
  have hD₁Cont : ContinuousAt D₁ 0 := by simpa only [D₁] using hfirstEntry 1 1
  have hA₂Cont : ContinuousAt A₂ 0 := by simpa only [A₂] using hsecondEntry 0 0
  have hE₂Cont : ContinuousAt E₂ 0 := by simpa only [E₂] using hsecondEntry 0 1
  have hD₂Cont : ContinuousAt D₂ 0 := by simpa only [D₂] using hsecondEntry 1 1
  have hX₁Cont : ContinuousAt X₁ 0 := by
    dsimp only [X₁, RealSymmetric2.low, RealSymmetric2.gap]
    fun_prop
  have hX₂Cont : ContinuousAt X₂ 0 := by
    dsimp only [X₂, RealSymmetric2.low, RealSymmetric2.gap]
    fun_prop
  have hE₁' : EqModPow 8 E₁
      (fun ε => ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6) := by
    simpa only [E₁] using hE₁
  have hX₁' : EqModPow 8 X₁
      (fun ε => 1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7) := by
    simpa only [A₁, E₁, D₁, X₁] using hX₁
  have hE₂' : EqModPow 8 E₂
      (fun ε => 2 * ε ^ 2 + (286 / 5) * ε ^ 5 - (73 / 5) * ε ^ 6) := by
    simpa only [E₂] using hE₂
  have hX₂' : EqModPow 8 X₂
      (fun ε => 1 + 8 * ε ^ 3 - 6 * ε ^ 4 + (1104 / 5) * ε ^ 6 -
        (1414 / 5) * ε ^ 7) := by
    simpa only [A₂, E₂, D₂, X₂] using hX₂
  have hraw := rawFrameQuotient_algebra E₁ X₁ E₂ X₂
    hE₁' hX₁' hE₂' hX₂' hE₁Cont hX₁Cont hE₂Cont hX₂Cont
  let N₁ : ℝ → ℝ := fun ε => Real.sqrt (X₁ ε ^ 2 + E₁ ε ^ 2)
  let N₂ : ℝ → ℝ := fun ε => Real.sqrt (X₂ ε ^ 2 + E₂ ε ^ 2)
  have hN₁Cont : ContinuousAt N₁ 0 := by
    dsimp only [N₁]
    fun_prop
  have hN₂Cont : ContinuousAt N₂ 0 := by
    dsimp only [N₂]
    fun_prop
  have hE₁Zero : E₁ 0 = 0 := by
    simpa using EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hE₁'
  have hX₁Zero : X₁ 0 = 1 := by
    simpa using EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hX₁'
  have hE₂Zero : E₂ 0 = 0 := by
    simpa using EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hE₂'
  have hX₂Zero : X₂ 0 = 1 := by
    simpa using EqModPow.eq_at_zero_of_pos (by norm_num : 0 < 8) hX₂'
  have hN₁Zero : N₁ 0 ≠ 0 := by
    simp [N₁, hE₁Zero, hX₁Zero]
  have hN₂Zero : N₂ 0 ≠ 0 := by
    simp [N₂, hE₂Zero, hX₂Zero]
  have hslopeEq : ∀ᶠ ε in 𝓝 (0 : ℝ),
      slowGraphRelativeFrameSlope ε =
        -(E₁ ε * X₂ ε + X₁ ε * E₂ ε) /
          (X₁ ε * X₂ ε - E₁ ε * E₂ ε) := by
    filter_upwards [hN₁Cont.eventually_ne hN₁Zero,
      hN₂Cont.eventually_ne hN₂Zero] with ε hN₁ hN₂
    have hden₁ : RealSymmetric2.lowDenom (A₁ ε) (E₁ ε) (D₁ ε) ≠ 0 := by
      change N₁ ε ≠ 0
      exact hN₁
    have hden₂ : RealSymmetric2.lowDenom (A₂ ε) (E₂ ε) (D₂ ε) ≠ 0 := by
      change N₂ ε ≠ 0
      exact hN₂
    have hformula := relativeFrameSlope_lowVector_mul
      (A₁ ε) (E₁ ε) (D₁ ε) (A₂ ε) (E₂ ε) (D₂ ε) hden₁ hden₂
    simpa only [slowGraphRelativeFrameSlope, DFP.FirstLeg.frame, DFP.SecondLeg.frame,
      A₁, E₁, D₁, X₁, A₂, E₂, D₂, X₂] using hformula
  have hslopeEightRaw : EqModPow 8 slowGraphRelativeFrameSlope
      (fun ε => -3 * ε ^ 2 - (196 / 5) * ε ^ 5 - (17 / 5) * ε ^ 6) := by
    apply EqModPow.of_isBigO
    refine hraw.to_isBigO.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hslopeEq] with ε hε
    rw [hε]
  change EqModPow 7 slowGraphRelativeFrameSlope
    (fun ε => -3 * ε ^ 2 - (196 / 5) * ε ^ 5 - (17 / 5) * ε ^ 6)
  exact hslopeEightRaw.mono (by norm_num : 7 ≤ 8)

/-- The slow-graph frame-angle expansion follows unconditionally from the clean
raw-frame germ computation and the scalar arctangent reduction. -/
theorem slowGraphFrameAngleRemainder_viaSlope :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).frameAngleIncrement -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
  slowGraphFrameAngleRemainder_of_relativeFrameSlope slowGraphRelativeFrameSlopeGerm

end DFP.TwoLeg
