module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Smoothness
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- Pointwise equal real-valued functions determine the same finite-order germ. -/
private theorem eqModPow_of_eq (n : ℕ) {f g : ℝ → ℝ}
    (h : ∀ ε, f ε = g ε) : EqModPow n f g := by
  apply EqModPow.congr (EqModPow.refl n f)
  · intro ε
    rfl
  · intro ε
    exact (h ε).symm

/-- Compatible finite-order numerator and denominator germs yield the corresponding
quotient approximation. -/
private theorem eqModPow_div_approx {n : ℕ}
    {num den numP denP q : ℝ → ℝ}
    (hnum : EqModPow n num numP) (hden : EqModPow n den denP)
    (hpoly : EqModPow n numP (fun ε ↦ denP ε * q ε))
    (hdenP : ContinuousAt denP 0) (hq : ContinuousAt q 0)
    (hdenCont : ContinuousAt den 0) (hden0 : den 0 ≠ 0) :
    EqModPow n (fun ε ↦ num ε / den ε) q := by
  have hqRefl : EqModPow n q q := EqModPow.refl n q
  have hdenMul : EqModPow n (fun ε ↦ den ε * q ε)
      (fun ε ↦ denP ε * q ε) :=
    hden.mul hqRefl hdenP hq
  exact EqModPow.div_of_eq_mul
    (hnum.trans (hpoly.trans hdenMul.symm)) hdenCont hden0

set_option maxHeartbeats 1000000 in
-- The explicit first-leg rational and square-root normalization has a large elaboration term.
/-- The four first-leg spectral and gradient factors have their stated order-seven
germs on the polynomial slow graph. -/
private theorem slowGraphFirstLegAllGerms :
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.spectralFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).1)
        (fun ε : ℝ ↦
          2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4 +
            418 * ε ^ 6 + (128 / 5) * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.spectralFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).2)
        (fun ε : ℝ ↦ 1 - 2 * ε ^ 3 + 6 * ε ^ 6 + 2 * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.gradientFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).1)
        (fun ε : ℝ ↦
          1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 - (112 / 5) * ε ^ 6 -
            (157 / 5) * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.gradientFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).2)
        (fun ε : ℝ ↦
          1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4 - (278 / 5) * ε ^ 6 -
            (9 / 5) * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.outputMetric ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)) 0 1)
        (fun ε : ℝ ↦ ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          let M := DFP.FirstLeg.outputMetric ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)
          M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1))
        (fun ε : ℝ ↦
          1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7) := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let one : ℝ → ℝ := fun _ ↦ 1
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  let C : ℝ → ℝ := fun ε ↦
    (1 + ε ^ 3) ^ 2 + p ε * ε ^ 6 * (1 + ε) ^ 2
  let CP : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + 3 * ε ^ 6 + 4 * ε ^ 7
  let invBP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - ε ^ 4 + 4 * ε ^ 6 + 4 * ε ^ 7
  let invCP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 + ε ^ 6 - 4 * ε ^ 7
  have hBcont : ContinuousAt B 0 := by
    dsimp only [B]
    fun_prop
  have hCcont : ContinuousAt C 0 := by
    dsimp only [C, p]
    fun_prop
  have hCPcont : ContinuousAt CP 0 := by
    dsimp only [CP]
    fun_prop
  have hinvBPcont : ContinuousAt invBP 0 := by
    dsimp only [invBP]
    fun_prop
  have hinvCPcont : ContinuousAt invCP 0 := by
    dsimp only [invCP]
    fun_prop
  have hBzero : B 0 ≠ 0 := by
    norm_num [B]
  have hCzero : C 0 ≠ 0 := by
    norm_num [C, p]
  have hC : EqModPow 8 C CP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(9 * ε ^ 4 - 180 * ε ^ 3 - 387 * ε ^ 2 - 198 * ε - 10) / 5)
    · fun_prop
    · intro ε
      dsimp only [C, CP, p]
      ring
  have hInvBPoly : EqModPow 8 one (fun ε ↦ B ε * invBP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -4 * ε ^ 3 - 12 * ε ^ 2 - 8 * ε + 1)
    · fun_prop
    · intro ε
      dsimp only [one, B, invBP]
      ring
  have hInvB : EqModPow 8 (fun ε ↦ 1 / B ε) invBP := by
    have honeRefl : EqModPow 8 one one := EqModPow.refl 8 one
    have hBRefl : EqModPow 8 B B := EqModPow.refl 8 B
    exact eqModPow_div_approx honeRefl hBRefl hInvBPoly hBcont hinvBPcont
      hBcont hBzero
  have hInvCPoly : EqModPow 8 one (fun ε ↦ CP ε * invCP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        ε * (16 * ε ^ 5 + 8 * ε ^ 4 - 3 * ε ^ 3 + 16 * ε + 4))
    · fun_prop
    · intro ε
      dsimp only [one, CP, invCP]
      ring
  have hInvC : EqModPow 8 (fun ε ↦ 1 / C ε) invCP := by
    have honeRefl : EqModPow 8 one one := EqModPow.refl 8 one
    exact eqModPow_div_approx honeRefl hC hInvCPoly hCPcont hinvCPcont
      hCcont hCzero
  let numA : ℝ → ℝ := fun ε ↦ h ε * (p ε) ^ 2 * ε ^ 6 * (1 + ε) ^ 2
  let termAP : ℝ → ℝ := fun ε ↦ 4 * ε ^ 6 * (2 * ε + 1)
  have hnumAcont : ContinuousAt numA 0 := by
    dsimp only [numA, p, h]
    fun_prop
  have htermAPcont : ContinuousAt termAP 0 := by
    dsimp only [termAP]
    fun_prop
  have htermAPoly : EqModPow 8 numA (fun ε ↦ CP ε * termAP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (2 * ε + 1) *
          (324 * ε ^ 10 - 13770 * ε ^ 9 + 135513 * ε ^ 8 +
            231660 * ε ^ 7 + 38565 * ε ^ 6 + 10796 * ε ^ 5 +
            62484 * ε ^ 4 + 3960 * ε ^ 3 + 220 * ε ^ 2 +
            4360 * ε + 100) / 25)
    · fun_prop
    · intro ε
      dsimp only [numA, termAP, CP, p, h]
      ring
  have htermA : EqModPow 8 (fun ε ↦ numA ε / C ε) termAP := by
    have hnumARefl : EqModPow 8 numA numA := EqModPow.refl 8 numA
    exact eqModPow_div_approx hnumARefl hC htermAPoly hCPcont
      htermAPcont hCcont hCzero
  let numB : ℝ → ℝ := fun ε ↦
    h ε * p ε * ε ^ 3 * (1 + ε) * (1 + ε ^ 3)
  let termBP : ℝ → ℝ := fun ε ↦
    ε ^ 3 * (259 * ε ^ 4 + 268 * ε ^ 3 + 10 * ε + 10) / 5
  have htermBPcont : ContinuousAt termBP 0 := by
    dsimp only [termBP]
    fun_prop
  have htermBPoly : EqModPow 8 numB (fun ε ↦ CP ε * termBP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(1108 * ε ^ 6 + 337 * ε ^ 5 - 780 * ε ^ 4 + 121 * ε ^ 3 -
          1193 * ε ^ 2 - 1296 * ε + 9) / 5)
    · fun_prop
    · intro ε
      dsimp only [numB, termBP, CP, p, h]
      ring
  have htermB : EqModPow 8 (fun ε ↦ numB ε / C ε) termBP := by
    have hnumBRefl : EqModPow 8 numB numB := EqModPow.refl 8 numB
    exact eqModPow_div_approx hnumBRefl hC htermBPoly hCPcont
      htermBPcont hCcont hCzero
  let numD : ℝ → ℝ := fun ε ↦ h ε * (1 + ε ^ 3) ^ 2
  let termDP : ℝ → ℝ := fun ε ↦
    -(2 * ε + 1) * (2 * ε ^ 6 - 4 * ε ^ 2 + 2 * ε - 1)
  have htermDPcont : ContinuousAt termDP 0 := by
    dsimp only [termDP]
    fun_prop
  have htermDPoly : EqModPow 8 numD (fun ε ↦ CP ε * termDP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ 2 * ε * (2 * ε + 1) *
        (4 * ε ^ 4 + 3 * ε ^ 3 - 6))
    · fun_prop
    · intro ε
      dsimp only [numD, termDP, CP, h]
      ring
  have htermD : EqModPow 8 (fun ε ↦ numD ε / C ε) termDP := by
    have hnumDRefl : EqModPow 8 numD numD := EqModPow.refl 8 numD
    exact eqModPow_div_approx hnumDRefl hC htermDPoly hCPcont
      htermDPcont hCcont hCzero
  let a : ℝ → ℝ := fun ε ↦
    h ε * p ε - numA ε / C ε + 1 / B ε
  let b : ℝ → ℝ := fun ε ↦ 1 / B ε - numB ε / C ε
  let d : ℝ → ℝ := fun ε ↦ h ε - numD ε / C ε + 1 / B ε
  let aP : ℝ → ℝ := fun ε ↦
    3 + (268 / 5) * ε ^ 3 - (14 / 5) * ε ^ 4 + (1584 / 5) * ε ^ 6 -
      (92 / 5) * ε ^ 7
  let bP : ℝ → ℝ := fun ε ↦
    1 - 4 * ε ^ 3 - 3 * ε ^ 4 - (248 / 5) * ε ^ 6 - (239 / 5) * ε ^ 7
  let dP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - ε ^ 4 + 6 * ε ^ 6 + 8 * ε ^ 7
  have hpMulCont : ContinuousAt (fun ε ↦ h ε * p ε) 0 := by
    dsimp only [p, h]
    fun_prop
  have hpMulRefl : EqModPow 8 (fun ε ↦ h ε * p ε)
      (fun ε ↦ h ε * p ε) := EqModPow.refl 8 _
  have haRaw := (hpMulRefl.sub htermA).add hInvB
  have ha : EqModPow 8 a aP := by
    apply EqModPow.congr haRaw
    · intro ε
      rfl
    · intro ε
      dsimp only [a, aP, p, h, termAP, invBP]
      ring
  have hbRaw := hInvB.sub htermB
  have hb : EqModPow 8 b bP := by
    apply EqModPow.congr hbRaw
    · intro ε
      rfl
    · intro ε
      dsimp only [b, bP, termBP, invBP]
      ring
  have hhRefl : EqModPow 8 h h := EqModPow.refl 8 h
  have hdRaw := (hhRefl.sub htermD).add hInvB
  have hd : EqModPow 8 d dP := by
    apply EqModPow.congr hdRaw
    · intro ε
      rfl
    · intro ε
      dsimp only [d, dP, h, termDP, invBP]
      ring
  have haPcont : ContinuousAt aP 0 := by
    dsimp only [aP]
    fun_prop
  have hbPcont : ContinuousAt bP 0 := by
    dsimp only [bP]
    fun_prop
  have hdPcont : ContinuousAt dP 0 := by
    dsimp only [dP]
    fun_prop
  have haCont : ContinuousAt a 0 := by
    dsimp only [a, numA, C, B, p, h]
    fun_prop
  have hbCont : ContinuousAt b 0 := by
    dsimp only [b, numB, C, B, p, h]
    fun_prop
  have hdCont : ContinuousAt d 0 := by
    dsimp only [d, numD, C, B, p, h]
    fun_prop
  let A : ℝ → ℝ := fun ε ↦ ε ^ 4 * a ε
  let E : ℝ → ℝ := fun ε ↦ ε ^ 2 * b ε
  let AP : ℝ → ℝ := fun ε ↦ ε ^ 4 * aP ε
  let EP : ℝ → ℝ := fun ε ↦ ε ^ 2 * bP ε
  have hpowFourCont : ContinuousAt (fun ε : ℝ ↦ ε ^ 4) 0 := by fun_prop
  have hpowTwoCont : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by fun_prop
  have hA : EqModPow 8 A AP := by
    simpa only [A, AP] using
      (EqModPow.refl 8 (fun ε : ℝ ↦ ε ^ 4)).mul ha hpowFourCont haCont
  have hE : EqModPow 8 E EP := by
    simpa only [E, EP] using
      (EqModPow.refl 8 (fun ε : ℝ ↦ ε ^ 2)).mul hb hpowTwoCont hbCont
  have hACont : ContinuousAt A 0 := hpowFourCont.mul haCont
  have hECont : ContinuousAt E 0 := hpowTwoCont.mul hbCont
  let rad : ℝ → ℝ := fun ε ↦ (d ε - A ε) ^ 2 + 4 * (E ε) ^ 2
  let radP : ℝ → ℝ := fun ε ↦ (dP ε - AP ε) ^ 2 + 4 * (EP ε) ^ 2
  have hAdPcont : ContinuousAt (fun ε ↦ dP ε - AP ε) 0 := by fun_prop
  have hEdPcont : ContinuousAt EP 0 := by
    dsimp only [EP, bP]
    fun_prop
  have hrad : EqModPow 8 rad radP := by
    have hAd := hd.sub hA
    have hAdCont : ContinuousAt (fun ε ↦ d ε - A ε) 0 := hdCont.sub hACont
    have hAdSq := hAd.mul hAd hAdPcont hAdCont
    have hESq := hE.mul hE hEdPcont hECont
    have hFour : EqModPow 8 (fun _ : ℝ ↦ (4 : ℝ)) (fun _ : ℝ ↦ (4 : ℝ)) :=
      EqModPow.refl 8 _
    have hFourCont : ContinuousAt (fun _ : ℝ ↦ (4 : ℝ)) 0 := continuousAt_const
    have hESqCont : ContinuousAt (fun ε ↦ E ε * E ε) 0 := hECont.mul hECont
    have hFourESq := hFour.mul hESq hFourCont hESqCont
    apply EqModPow.congr (hAdSq.add hFourESq)
    · intro ε
      dsimp only [rad]
      ring
    · intro ε
      dsimp only [radP]
      ring
  let gapP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 + 6 * ε ^ 6 - (288 / 5) * ε ^ 7
  have hgapSquare : EqModPow 8 radP (fun ε ↦ (gapP ε) ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        4 * (2116 * ε ^ 14 - 72864 * ε ^ 13 + 627264 * ε ^ 12 +
          644 * ε ^ 11 + 35545 * ε ^ 10 + 300500 * ε ^ 9 +
          37793 * ε ^ 8 + 4654 * ε ^ 7 + 24850 * ε ^ 6 +
          18740 * ε ^ 5 + 85 * ε ^ 4 - 790 * ε ^ 3 - 6490 * ε ^ 2 -
          40) / 25)
    · fun_prop
    · intro ε
      dsimp only [radP, AP, EP, aP, bP, dP, gapP]
      ring
  have hradCont : ContinuousAt rad 0 := by
    exact ((hdCont.sub hACont).pow 2).add ((hECont.pow 2).const_mul 4)
  have hradPcont : ContinuousAt radP 0 := by
    dsimp only [radP, AP, EP, aP, bP, dP]
    fun_prop
  have hgapPcont : ContinuousAt gapP 0 := by
    dsimp only [gapP]
    fun_prop
  have hradZero : 0 < rad 0 := by
    norm_num [rad, A, E, a, d, numA, numD, C, B, p, h]
  have hgapPZero : 0 < gapP 0 := by
    norm_num [gapP]
  have hgap : EqModPow 8 (fun ε ↦ Real.sqrt (rad ε)) gapP := by
    exact EqModPow.sqrt_of_sq (hrad.trans hgapSquare) hradCont hgapPcont
      hradZero hgapPZero
  let low : ℝ → ℝ := fun ε ↦ (A ε + d ε - Real.sqrt (rad ε)) / 2
  let high : ℝ → ℝ := fun ε ↦ (A ε + d ε + Real.sqrt (rad ε)) / 2
  let lowP : ℝ → ℝ := fun ε ↦ 2 * ε ^ 4 + (298 / 5) * ε ^ 7
  let highP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 + 6 * ε ^ 6 + 2 * ε ^ 7
  have htwoRefl : EqModPow 8 (fun _ : ℝ ↦ (2 : ℝ)) (fun _ : ℝ ↦ (2 : ℝ)) :=
    EqModPow.refl 8 _
  have htwoCont : ContinuousAt (fun _ : ℝ ↦ (2 : ℝ)) 0 := continuousAt_const
  have htwoZero : (fun _ : ℝ ↦ (2 : ℝ)) 0 ≠ 0 := by norm_num
  have hlowNumerator := (hA.add hd).sub hgap
  have hhighNumerator := (hA.add hd).add hgap
  let lowRawP : ℝ → ℝ := fun ε ↦ (AP ε + dP ε - gapP ε) / 2
  let highRawP : ℝ → ℝ := fun ε ↦ (AP ε + dP ε + gapP ε) / 2
  have hlowRaw : EqModPow 8 low lowRawP := by
    have hpolyRefl : EqModPow 8
        (fun ε ↦ AP ε + dP ε - gapP ε)
        (fun ε ↦ AP ε + dP ε - gapP ε) := EqModPow.refl 8 _
    have hrawCont : ContinuousAt lowRawP 0 := by
      dsimp only [lowRawP, AP, aP, dP, gapP]
      fun_prop
    have hdenPoly : EqModPow 8
        (fun ε ↦ AP ε + dP ε - gapP ε)
        (fun ε ↦ 2 * lowRawP ε) := by
      apply eqModPow_of_eq
      intro ε
      dsimp only [lowRawP]
      ring
    exact eqModPow_div_approx hlowNumerator htwoRefl hdenPoly htwoCont
      hrawCont htwoCont htwoZero
  have hhighRaw : EqModPow 8 high highRawP := by
    have hrawCont : ContinuousAt highRawP 0 := by
      dsimp only [highRawP, AP, aP, dP, gapP]
      fun_prop
    have hdenPoly : EqModPow 8
        (fun ε ↦ AP ε + dP ε + gapP ε)
        (fun ε ↦ 2 * highRawP ε) := by
      apply eqModPow_of_eq
      intro ε
      dsimp only [highRawP]
      ring
    exact eqModPow_div_approx hhighNumerator htwoRefl hdenPoly htwoCont
      hrawCont htwoCont htwoZero
  have hlowPoly : EqModPow 8 lowRawP lowP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -(46 * ε ^ 3 - 792 * ε ^ 2 + 7) / 5)
    · fun_prop
    · intro ε
      dsimp only [lowRawP, lowP, AP, aP, dP, gapP]
      ring
  have hhighPoly : EqModPow 8 highRawP highP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -(46 * ε ^ 3 - 792 * ε ^ 2 + 7) / 5)
    · fun_prop
    · intro ε
      dsimp only [highRawP, highP, AP, aP, dP, gapP]
      ring
  have hlow : EqModPow 8 low lowP := hlowRaw.trans hlowPoly
  have hhigh : EqModPow 8 high highP := hhighRaw.trans hhighPoly
  let denRad : ℝ → ℝ := fun ε ↦ (d ε - low ε) ^ 2 + (E ε) ^ 2
  let denRadP : ℝ → ℝ := fun ε ↦ (dP ε - lowP ε) ^ 2 + (EP ε) ^ 2
  have hlowPcont : ContinuousAt lowP 0 := by
    dsimp only [lowP]
    fun_prop
  have hdenRad : EqModPow 8 denRad denRadP := by
    have hdiff := hd.sub hlow
    have hdiffPcont : ContinuousAt (fun ε ↦ dP ε - lowP ε) 0 :=
      hdPcont.sub hlowPcont
    have hlowCont : ContinuousAt low 0 :=
      ((hACont.add hdCont).sub hradCont.sqrt).div_const 2
    have hdiffCont : ContinuousAt (fun ε ↦ d ε - low ε) 0 :=
      hdCont.sub hlowCont
    have hdiffSq := hdiff.mul hdiff hdiffPcont hdiffCont
    have hESq := hE.mul hE hEdPcont hECont
    apply EqModPow.congr (hdiffSq.add hESq)
    · intro ε
      dsimp only [denRad]
      ring
    · intro ε
      dsimp only [denRadP]
      ring
  let denP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 + 6 * ε ^ 6 - (273 / 5) * ε ^ 7
  have hdenSquare : EqModPow 8 denRadP (fun ε ↦ (denP ε) ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (228484 * ε ^ 10 + 474176 * ε ^ 9 + 246016 * ε ^ 8 +
          28680 * ε ^ 7 + 36140 * ε ^ 6 + 43280 * ε ^ 5 +
          900 * ε ^ 4 - 3500 * ε ^ 3 - 10120 * ε ^ 2 - 325) / 100)
    · fun_prop
    · intro ε
      dsimp only [denRadP, denP, dP, lowP, EP, bP]
      ring
  have hdenRadCont : ContinuousAt denRad 0 := by
    have hlowCont : ContinuousAt low 0 := by
      exact ((hACont.add hdCont).sub hradCont.sqrt).div_const 2
    exact ((hdCont.sub hlowCont).pow 2).add (hECont.pow 2)
  have hdenPcont : ContinuousAt denP 0 := by
    dsimp only [denP]
    fun_prop
  have hdenRadZero : 0 < denRad 0 := by
    norm_num [denRad, d, low, A, E, rad, a, b, numA, numB, numD, C, B, p, h]
  have hdenPZero : 0 < denP 0 := by norm_num [denP]
  have hden : EqModPow 8 (fun ε ↦ Real.sqrt (denRad ε)) denP := by
    exact EqModPow.sqrt_of_sq (hdenRad.trans hdenSquare) hdenRadCont hdenPcont
      hdenRadZero hdenPZero
  let q : ℝ → ℝ := fun ε ↦
    1 - 2 * (p ε + 1) * ε ^ 3 * (1 + ε) / (3 * B ε)
  let v : ℝ → ℝ := fun ε ↦
    p ε - 2 * (p ε + 1) * (1 + ε ^ 3) / (3 * B ε)
  let threeB : ℝ → ℝ := fun ε ↦ 3 * B ε
  let numQ : ℝ → ℝ := fun ε ↦ 2 * (p ε + 1) * ε ^ 3 * (1 + ε)
  let numV : ℝ → ℝ := fun ε ↦ 2 * (p ε + 1) * (1 + ε ^ 3)
  let termQP : ℝ → ℝ := fun ε ↦
    2 * ε ^ 3 * (48 * ε ^ 4 + 56 * ε ^ 3 + 5 * ε + 5) / 5
  let termVP : ℝ → ℝ := fun ε ↦
    -2 * (48 * ε ^ 7 + 56 * ε ^ 6 + 8 * ε ^ 4 - 61 * ε ^ 3 - 5) / 5
  have htermQPcont : ContinuousAt termQP 0 := by fun_prop
  have htermVPcont : ContinuousAt termVP 0 := by fun_prop
  have hthreeBcont : ContinuousAt threeB 0 := by
    dsimp only [threeB]
    exact hBcont.const_mul 3
  have hthreeBzero : threeB 0 ≠ 0 := by norm_num [threeB, B]
  have htermQPoly : EqModPow 8 numQ (fun ε ↦ threeB ε * termQP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -48 * (ε + 1) * (6 * ε ^ 2 + 13 * ε + 1) / 5)
    · fun_prop
    · intro ε
      dsimp only [numQ, termQP, threeB, B, p]
      ring
  have htermVPoly : EqModPow 8 numV (fun ε ↦ threeB ε * termVP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ 48 * (ε + 1) * (6 * ε ^ 2 + 13 * ε + 1) / 5)
    · fun_prop
    · intro ε
      dsimp only [numV, termVP, threeB, B, p]
      ring
  have htermQ : EqModPow 8 (fun ε ↦ numQ ε / threeB ε) termQP := by
    have hnumQRefl : EqModPow 8 numQ numQ := EqModPow.refl 8 numQ
    have hthreeBRefl : EqModPow 8 threeB threeB := EqModPow.refl 8 threeB
    exact eqModPow_div_approx hnumQRefl hthreeBRefl htermQPoly hthreeBcont
      htermQPcont hthreeBcont hthreeBzero
  have htermV : EqModPow 8 (fun ε ↦ numV ε / threeB ε) termVP := by
    have hnumVRefl : EqModPow 8 numV numV := EqModPow.refl 8 numV
    have hthreeBRefl : EqModPow 8 threeB threeB := EqModPow.refl 8 threeB
    exact eqModPow_div_approx hnumVRefl hthreeBRefl htermVPoly hthreeBcont
      htermVPcont hthreeBcont hthreeBzero
  let qP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6 - (96 / 5) * ε ^ 7
  let vP : ℝ → ℝ := fun ε ↦
    (76 / 5) * ε ^ 3 + (7 / 5) * ε ^ 4 + (112 / 5) * ε ^ 6 +
      (96 / 5) * ε ^ 7
  have hq : EqModPow 8 q qP := by
    have honeRefl : EqModPow 8 one one := EqModPow.refl 8 one
    apply EqModPow.congr (honeRefl.sub htermQ)
    · intro ε
      dsimp only [q, numQ, threeB]
    · intro ε
      dsimp only [one, qP, termQP]
      ring
  have hv : EqModPow 8 v vP := by
    have hpRefl : EqModPow 8 p p := EqModPow.refl 8 p
    apply EqModPow.congr (hpRefl.sub htermV)
    · intro ε
      dsimp only [v, numV, threeB]
    · intro ε
      dsimp only [p, vP, termVP]
      ring
  have hqPcont : ContinuousAt qP 0 := by fun_prop
  have hvPcont : ContinuousAt vP 0 := by fun_prop
  have hqCont : ContinuousAt q 0 := by
    dsimp only [q, p, B]
    fun_prop
  have hvCont : ContinuousAt v 0 := by
    dsimp only [v, p, B]
    fun_prop
  let numeratorL : ℝ → ℝ := fun ε ↦ a ε * d ε - (b ε) ^ 2
  let numeratorLP : ℝ → ℝ := fun ε ↦ aP ε * dP ε - (bP ε) ^ 2
  let LP : ℝ → ℝ := fun ε ↦
    2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4 + 418 * ε ^ 6 +
      (128 / 5) * ε ^ 7
  have hnumL : EqModPow 8 numeratorL numeratorLP := by
    have hproduct := ha.mul hd haPcont hdCont
    have hsquare := hb.mul hb hbPcont hbCont
    apply EqModPow.congr (hproduct.sub hsquare)
    · intro ε
      dsimp only [numeratorL]
      ring
    · intro ε
      dsimp only [numeratorLP]
      ring
  have hLPcont : ContinuousAt LP 0 := by fun_prop
  have hhighPcont : ContinuousAt highP 0 := by fun_prop
  have hhighCont : ContinuousAt high 0 := by
    dsimp only [high, A, rad]
    fun_prop
  have hhighZero : high 0 ≠ 0 := by
    norm_num [high, A, rad, a, b, d, E, numA, numB, numD, C, B, p, h]
  have hLPoly : EqModPow 8 numeratorLP (fun ε ↦ highP ε * LP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(62081 * ε ^ 6 + 82684 * ε ^ 5 + 76684 * ε ^ 4 +
          7280 * ε ^ 3 + 15430 * ε ^ 2 + 5760 * ε + 155) / 25)
    · fun_prop
    · intro ε
      dsimp only [numeratorLP, highP, LP, aP, bP, dP]
      ring
  have hL : EqModPow 8 (fun ε ↦ numeratorL ε / high ε) LP := by
    exact eqModPow_div_approx hnumL hhigh hLPoly hhighPcont hLPcont
      hhighCont hhighZero
  let numeratorQ : ℝ → ℝ := fun ε ↦
    (d ε - low ε) * q ε - ε ^ 4 * b ε * v ε
  let numeratorQP : ℝ → ℝ := fun ε ↦
    (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε
  let QP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 - (112 / 5) * ε ^ 6 -
      (157 / 5) * ε ^ 7
  have hnumQFinal : EqModPow 8 numeratorQ numeratorQP := by
    have hleft := (hd.sub hlow).mul hq (hdPcont.sub hlowPcont) hqCont
    have hpowFourRefl : EqModPow 8 (fun ε : ℝ ↦ ε ^ 4)
        (fun ε : ℝ ↦ ε ^ 4) := EqModPow.refl 8 _
    have hrightFirst := hpowFourRefl.mul hb hpowFourCont hbCont
    have hrightApproxCont := hpowFourCont.mul hbPcont
    have hright := hrightFirst.mul hv hrightApproxCont hvCont
    simpa only [numeratorQ, numeratorQP] using hleft.sub hright
  have hQPcont : ContinuousAt QP 0 := by fun_prop
  have hdenCont : ContinuousAt (fun ε ↦ Real.sqrt (denRad ε)) 0 :=
    hdenRadCont.sqrt
  have hdenZero : Real.sqrt (denRad 0) ≠ 0 := by
    positivity
  have hQPoly : EqModPow 8 numeratorQP (fun ε ↦ denP ε * QP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (91776 * ε ^ 10 + 202304 * ε ^ 9 + 111104 * ε ^ 8 +
          12452 * ε ^ 7 + 21628 * ε ^ 6 + 84952 * ε ^ 5 +
          420 * ε ^ 4 - 2220 * ε ^ 3 + 2220 * ε ^ 2 - 165) / 100)
    · fun_prop
    · intro ε
      dsimp only [numeratorQP, denP, QP, dP, lowP, qP, bP, vP]
      ring
  have hQ : EqModPow 8
      (fun ε ↦ numeratorQ ε / Real.sqrt (denRad ε)) QP := by
    exact eqModPow_div_approx hnumQFinal hden hQPoly hdenPcont hQPcont
      hdenCont hdenZero
  let numeratorU : ℝ → ℝ := fun ε ↦
    b ε * q ε + (d ε - low ε) * v ε
  let numeratorUP : ℝ → ℝ := fun ε ↦
    bP ε * qP ε + (dP ε - lowP ε) * vP ε
  let UP : ℝ → ℝ := fun ε ↦
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4 - (278 / 5) * ε ^ 6 -
      (9 / 5) * ε ^ 7
  have hnumU : EqModPow 8 numeratorU numeratorUP := by
    have hleft := hb.mul hq hbPcont hqCont
    have hright := (hd.sub hlow).mul hv (hdPcont.sub hlowPcont) hvCont
    simpa only [numeratorU, numeratorUP] using hleft.add hright
  have hUPcont : ContinuousAt UP 0 := by fun_prop
  have hUPoly : EqModPow 8 numeratorUP (fun ε ↦ denP ε * UP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(17124 * ε ^ 6 + 204256 * ε ^ 5 - 157904 * ε ^ 4 +
          4120 * ε ^ 3 + 6720 * ε ^ 2 - 5680 * ε + 95) / 100)
    · fun_prop
    · intro ε
      dsimp only [numeratorUP, denP, UP, bP, qP, dP, lowP, vP]
      ring
  have hU : EqModPow 8
      (fun ε ↦ numeratorU ε / Real.sqrt (denRad ε)) UP := by
    exact eqModPow_div_approx hnumU hden hUPoly hdenPcont hUPcont
      hdenCont hdenZero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply EqModPow.congr hL
    · intro ε
      dsimp only [numeratorL, high, A, E, rad, a, b, d, numA, numB, numD,
        C, B, p, h]
      simp only [DFP.FirstLeg.spectralFactors, RealSymmetric2.high,
        RealSymmetric2.gap]
    · intro ε
      rfl
  · apply EqModPow.congr hhigh
    · intro ε
      dsimp only [high, A, E, rad, a, b, d, numA, numB, numD, C, B, p, h]
      simp only [DFP.FirstLeg.spectralFactors, RealSymmetric2.high,
        RealSymmetric2.gap]
    · intro ε
      rfl
  · apply EqModPow.congr hQ
    · intro ε
      dsimp only [numeratorQ, denRad, low, high, A, E, rad, q, v, a, b, d,
        numA, numB, numD, C, B, p, h]
      simp only [DFP.FirstLeg.gradientFactors, RealSymmetric2.lowDenom,
        RealSymmetric2.low, RealSymmetric2.gap]
    · intro ε
      rfl
  · apply EqModPow.congr hU
    · intro ε
      dsimp only [numeratorU, denRad, low, high, A, E, rad, q, v, a, b, d,
        numA, numB, numD, C, B, p, h]
      simp only [DFP.FirstLeg.gradientFactors, RealSymmetric2.lowDenom,
        RealSymmetric2.low, RealSymmetric2.gap]
    · intro ε
      rfl
  · have hEPoly : EqModPow 8 EP
        (fun ε : ℝ ↦ ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6) := by
      apply EqModPow.of_factor
        (q := fun ε : ℝ ↦ -(248 / 5) - (239 / 5) * ε)
      · fun_prop
      · intro ε
        dsimp only [EP, bP]
        ring
    apply EqModPow.congr (hE.trans hEPoly)
    · intro ε
      dsimp only [E, b, numB, C, B, p, h]
      rfl
    · intro ε
      rfl
  · apply EqModPow.congr (hd.sub hlow)
    · intro ε
      change d ε - RealSymmetric2.low (A ε) (E ε) (d ε) = d ε - low ε
      dsimp only [low, rad]
      simp only [RealSymmetric2.low, RealSymmetric2.gap]
    · intro ε
      dsimp only [dP, lowP]
      ring

set_option maxHeartbeats 2000000 in
-- The explicit second-leg rational and square-root normalization has a large elaboration term.
/-- The removable second-leg low-gradient factor has the stated order-seven germ on
the polynomial slow graph. -/
private theorem slowGraphSecondLegAllGerms :
    EqModPow 8
      (fun ε : ℝ ↦
        (DFP.SecondLeg.gradientFactors ε
          (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
          (1 + 8 * ε ^ 3)).1)
      (fun ε : ℝ ↦
        1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7) ∧
    EqModPow 8
      (fun ε : ℝ ↦
        (DFP.SecondLeg.outputMetric ε
          (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
          (1 + 8 * ε ^ 3)) 0 1)
      (fun ε : ℝ ↦
        2 * ε ^ 2 + (286 / 5) * ε ^ 5 - (73 / 5) * ε ^ 6) ∧
    EqModPow 8
      (fun ε : ℝ ↦
        let M := DFP.SecondLeg.outputMetric ε
          (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
          (1 + 8 * ε ^ 3)
        M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1))
      (fun ε : ℝ ↦
        1 + 8 * ε ^ 3 - 6 * ε ^ 4 + (1104 / 5) * ε ^ 6 -
          (1414 / 5) * ε ^ 7) := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let path : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let L : ℝ → ℝ := fun ε ↦ (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).1
  let H : ℝ → ℝ := fun ε ↦ (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).2
  let Q : ℝ → ℝ := fun ε ↦ (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).1
  let U : ℝ → ℝ := fun ε ↦ (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).2
  let LP : ℝ → ℝ := fun ε ↦
    2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4 + 418 * ε ^ 6 +
      (128 / 5) * ε ^ 7
  let HP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 + 6 * ε ^ 6 + 2 * ε ^ 7
  let QP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 - (112 / 5) * ε ^ 6 -
      (157 / 5) * ε ^ 7
  let UP : ℝ → ℝ := fun ε ↦
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4 - (278 / 5) * ε ^ 6 -
      (9 / 5) * ε ^ 7
  rcases slowGraphFirstLegAllGerms with ⟨hLRaw, hHRaw, hQRaw, hURaw, _, _⟩
  have hL : EqModPow 8 L LP := by simpa only [L, LP, p, h] using hLRaw
  have hH : EqModPow 8 H HP := by simpa only [H, HP, p, h] using hHRaw
  have hQ : EqModPow 8 Q QP := by simpa only [Q, QP, p, h] using hQRaw
  have hU : EqModPow 8 U UP := by simpa only [U, UP, p, h] using hURaw
  have hpathCont : ContinuousAt path 0 := by
    dsimp only [path, p, h]
    fun_prop
  have hfactorCont : ContinuousAt
      (fun ε : ℝ ↦ DFP.FirstLeg.factors ε (p ε) (h ε)) 0 := by
    have hpathZero : path 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      norm_num [path, p, h]
    have hall := DFP.FirstLeg.factorsAnalytic.continuousAt
    rw [← hpathZero] at hall
    have hcomp := hall.comp (f := path) hpathCont
    simpa only [Function.comp_def, path] using hcomp
  have hLCont : ContinuousAt L 0 := by
    simpa only [L, DFP.FirstLeg.factors] using hfactorCont.fst.fst
  have hHCont : ContinuousAt H 0 := by
    simpa only [H, DFP.FirstLeg.factors] using hfactorCont.fst.snd
  have hQCont : ContinuousAt Q 0 := by
    simpa only [Q, DFP.FirstLeg.factors] using hfactorCont.snd.fst.fst
  have hUCont : ContinuousAt U 0 := by
    simpa only [U, DFP.FirstLeg.factors] using hfactorCont.snd.fst.snd
  have hLPCont : ContinuousAt LP 0 := by fun_prop
  have hHPCont : ContinuousAt HP 0 := by fun_prop
  have hQPCont : ContinuousAt QP 0 := by fun_prop
  have hUPCont : ContinuousAt UP 0 := by fun_prop
  let w₁ : ℝ → ℝ := fun ε ↦ ε * L ε * Q ε - 2 * H ε * U ε
  let w₂ : ℝ → ℝ := fun ε ↦ H ε * U ε - 2 * ε ^ 3 * L ε * Q ε
  let w₁P : ℝ → ℝ := fun ε ↦
    -2 + 2 * ε - (92 / 5) * ε ^ 3 + (289 / 5) * ε ^ 4 -
      (24 / 5) * ε ^ 5 + 144 * ε ^ 6 + (1246 / 5) * ε ^ 7
  let w₂P : ℝ → ℝ := fun ε ↦
    1 + (26 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4 - (916 / 5) * ε ^ 6 +
      12 * ε ^ 7
  have hLQ := hL.mul hQ hLPCont hQCont
  have hHU := hH.mul hU hHPCont hUCont
  have hLQCont : ContinuousAt (fun ε ↦ L ε * Q ε) 0 := hLCont.mul hQCont
  have hHUCont : ContinuousAt (fun ε ↦ H ε * U ε) 0 := hHCont.mul hUCont
  have hLPQPCont : ContinuousAt (fun ε ↦ LP ε * QP ε) 0 := hLPCont.mul hQPCont
  have hHPUPCont : ContinuousAt (fun ε ↦ HP ε * UP ε) 0 := hHPCont.mul hUPCont
  have hId : EqModPow 8 (fun ε : ℝ ↦ ε) (fun ε : ℝ ↦ ε) := EqModPow.refl 8 _
  have hIdCont : ContinuousAt (fun ε : ℝ ↦ ε) 0 := continuousAt_id
  have hIdLQ := hId.mul hLQ hIdCont hLQCont
  have hTwo : EqModPow 8 (fun _ : ℝ ↦ (2 : ℝ)) (fun _ : ℝ ↦ (2 : ℝ)) :=
    EqModPow.refl 8 _
  have hTwoCont : ContinuousAt (fun _ : ℝ ↦ (2 : ℝ)) 0 := continuousAt_const
  have hTwoHU := hTwo.mul hHU hTwoCont hHUCont
  have hw₁Raw : EqModPow 8 w₁
      (fun ε ↦ ε * (LP ε * QP ε) - 2 * (HP ε * UP ε)) := by
    simpa only [w₁, mul_assoc] using hIdLQ.sub hTwoHU
  have hw₁Poly : EqModPow 8
      (fun ε ↦ ε * (LP ε * QP ε) - 2 * (HP ε * UP ε)) w₁P := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(40192 * ε ^ 7 + 684572 * ε ^ 6 + 455960 * ε ^ 5 -
          29846 * ε ^ 4 + 148386 * ε ^ 3 + 110492 * ε ^ 2 +
          17865 * ε + 9330) / 50)
    · fun_prop
    · intro ε
      dsimp only [LP, QP, HP, UP, w₁P]
      ring
  have hw₁ : EqModPow 8 w₁ w₁P := hw₁Raw.trans hw₁Poly
  have hCube : EqModPow 8 (fun ε : ℝ ↦ ε ^ 3) (fun ε : ℝ ↦ ε ^ 3) :=
    EqModPow.refl 8 _
  have hCubeCont : ContinuousAt (fun ε : ℝ ↦ ε ^ 3) 0 := by fun_prop
  have hCubeLQ := hCube.mul hLQ hCubeCont hLQCont
  have hCubeLQCont : ContinuousAt (fun ε ↦ ε ^ 3 * (L ε * Q ε)) 0 := by
    have hfun :
        (fun ε : ℝ ↦ ε ^ 3) * (fun ε ↦ L ε * Q ε) =
          (fun ε ↦ ε ^ 3 * (L ε * Q ε)) := by
      funext ε
      rfl
    rw [← hfun]
    exact hCubeCont.mul hLQCont
  have hTwoCubeLQ := hTwo.mul hCubeLQ hTwoCont hCubeLQCont
  have hw₂Raw : EqModPow 8 w₂
      (fun ε ↦ HP ε * UP ε - 2 * (ε ^ 3 * (LP ε * QP ε))) := by
    simpa only [w₂, mul_assoc] using hHU.sub hTwoCubeLQ
  have hw₂Poly : EqModPow 8
      (fun ε ↦ HP ε * UP ε - 2 * (ε ^ 3 * (LP ε * QP ε))) w₂P := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ ε *
        (40192 * ε ^ 8 + 684932 * ε ^ 7 + 468160 * ε ^ 6 +
          3424 * ε ^ 5 + 145556 * ε ^ 4 + 100212 * ε ^ 3 -
          30 * ε ^ 2 + 9815 * ε - 8240) / 25)
    · fun_prop
    · intro ε
      dsimp only [LP, QP, HP, UP, w₂P]
      ring
  have hw₂ : EqModPow 8 w₂ w₂P := hw₂Raw.trans hw₂Poly
  have hw₁Cont : ContinuousAt w₁ 0 := by
    dsimp only [w₁]
    have hfun :
        ((fun ε : ℝ ↦ ε) * L) * Q - ((fun _ : ℝ ↦ (2 : ℝ)) * H) * U =
          (fun ε ↦ ε * L ε * Q ε - 2 * H ε * U ε) := by
      funext ε
      rfl
    rw [← hfun]
    exact (((hIdCont.mul hLCont).mul hQCont).sub
      ((hTwoCont.mul hHCont).mul hUCont))
  have hw₂Cont : ContinuousAt w₂ 0 := by
    dsimp only [w₂]
    have hfun :
        (fun ε ↦ H ε * U ε) -
            (((fun _ : ℝ ↦ (2 : ℝ)) * (fun ε ↦ ε ^ 3)) * L) * Q =
          (fun ε ↦ H ε * U ε - 2 * ε ^ 3 * L ε * Q ε) := by
      funext ε
      rfl
    rw [← hfun]
    exact hHUCont.sub (((hTwoCont.mul hCubeCont).mul hLCont).mul hQCont)
  have hw₁PCont : ContinuousAt w₁P 0 := by fun_prop
  have hw₂PCont : ContinuousAt w₂P 0 := by fun_prop
  let beta : ℝ → ℝ := fun ε ↦
    ε ^ 3 * L ε * Q ε * w₁ ε + H ε * U ε * w₂ ε
  let gamma : ℝ → ℝ := fun ε ↦
    ε ^ 6 * L ε * (w₁ ε) ^ 2 + H ε * (w₂ ε) ^ 2
  let delta : ℝ → ℝ := fun ε ↦ L ε * (Q ε) ^ 2 + H ε * (U ε) ^ 2
  let betaP : ℝ → ℝ := fun ε ↦
    1 + (52 / 5) * ε ^ 3 + (9 / 5) * ε ^ 4 - (8884 / 25) * ε ^ 6 +
      (5874 / 25) * ε ^ 7
  let gammaP : ℝ → ℝ := fun ε ↦
    1 + (42 / 5) * ε ^ 3 - (11 / 5) * ε ^ 4 - (8654 / 25) * ε ^ 6 +
      (74 / 25) * ε ^ 7
  let deltaP : ℝ → ℝ := fun ε ↦
    3 + 72 * ε ^ 3 - 12 * ε ^ 4 + (1836 / 25) * ε ^ 6 -
      (10016 / 25) * ε ^ 7
  have hCubeLQw₁ := hCubeLQ.mul hw₁
    (hCubeCont.mul hLPQPCont) hw₁Cont
  have hHUw₂ := hHU.mul hw₂ hHPUPCont hw₂Cont
  have hbetaRaw : EqModPow 8 beta
      (fun ε ↦ ε ^ 3 * (LP ε * QP ε) * w₁P ε +
        (HP ε * UP ε) * w₂P ε) := by
    simpa only [beta, mul_assoc] using hCubeLQw₁.add hHUw₂
  have hbetaPoly : EqModPow 8
      (fun ε ↦ ε ^ 3 * (LP ε * QP ε) * w₁P ε +
        (HP ε * UP ε) * w₂P ε) betaP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(100158464 * ε ^ 16 + 1764727024 * ε ^ 15 + 2151027584 * ε ^ 14 +
          673283128 * ε ^ 13 + 741812240 * ε ^ 12 + 619730944 * ε ^ 11 +
          35391044 * ε ^ 10 + 115842696 * ε ^ 9 + 13690072 * ε ^ 8 -
          30780288 * ε ^ 7 + 9501450 * ε ^ 6 - 15680040 * ε ^ 5 -
          10740700 * ε ^ 4 + 467280 * ε ^ 3 - 2552300 * ε ^ 2 +
          1562240 * ε + 8995) / 500)
    · fun_prop
    · intro ε
      dsimp only [LP, QP, w₁P, HP, UP, w₂P, betaP]
      ring
  have hbeta : EqModPow 8 beta betaP := hbetaRaw.trans hbetaPoly
  have hSix : EqModPow 8 (fun ε : ℝ ↦ ε ^ 6) (fun ε : ℝ ↦ ε ^ 6) :=
    EqModPow.refl 8 _
  have hSixCont : ContinuousAt (fun ε : ℝ ↦ ε ^ 6) 0 := by fun_prop
  have hw₁Sq := hw₁.mul hw₁ hw₁PCont hw₁Cont
  have hw₂Sq := hw₂.mul hw₂ hw₂PCont hw₂Cont
  have hw₁SqCont : ContinuousAt (fun ε ↦ w₁ ε * w₁ ε) 0 :=
    hw₁Cont.mul hw₁Cont
  have hw₂SqCont : ContinuousAt (fun ε ↦ w₂ ε * w₂ ε) 0 :=
    hw₂Cont.mul hw₂Cont
  have hLw₁Sq := hL.mul hw₁Sq hLPCont hw₁SqCont
  have hLw₁SqCont : ContinuousAt (fun ε ↦ L ε * (w₁ ε * w₁ ε)) 0 :=
    hLCont.mul hw₁SqCont
  have hSixLw₁Sq := hSix.mul hLw₁Sq hSixCont
    hLw₁SqCont
  have hHw₂Sq := hH.mul hw₂Sq hHPCont hw₂SqCont
  have hgammaRaw : EqModPow 8 gamma
      (fun ε ↦ ε ^ 6 * (LP ε * (w₁P ε * w₁P ε)) +
        HP ε * (w₂P ε * w₂P ε)) := by
    apply EqModPow.congr (hSixLw₁Sq.add hHw₂Sq)
    · intro ε
      dsimp only [gamma]
      ring
    · intro ε
      ring
  have hgammaPoly : EqModPow 8
      (fun ε ↦ ε ^ 6 * (LP ε * (w₁P ε * w₁P ε)) +
        HP ε * (w₂P ε * w₂P ε)) gammaP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (794888192 * ε ^ 19 + 13897684640 * ε ^ 18 + 15234645504 * ε ^ 17 +
          4191080720 * ε ^ 16 + 7685611776 * ε ^ 15 + 3632902144 * ε ^ 14 -
          616191760 * ε ^ 13 + 1787026472 * ε ^ 12 - 220760896 * ε ^ 11 -
          105428796 * ε ^ 10 + 210432680 * ε ^ 9 - 127138496 * ε ^ 8 -
          37320182 * ε ^ 7 + 12793910 * ε ^ 6 - 16272240 * ε ^ 5 +
          20441360 * ε ^ 4 + 352190 * ε ^ 3 - 287640 * ε ^ 2 -
          389280 * ε + 4605) / 500)
    · fun_prop
    · intro ε
      dsimp only [LP, w₁P, HP, w₂P, gammaP]
      ring
  have hgamma : EqModPow 8 gamma gammaP := hgammaRaw.trans hgammaPoly
  have hQSq := hQ.mul hQ hQPCont hQCont
  have hUSq := hU.mul hU hUPCont hUCont
  have hQSqCont : ContinuousAt (fun ε ↦ Q ε * Q ε) 0 := hQCont.mul hQCont
  have hUSqCont : ContinuousAt (fun ε ↦ U ε * U ε) 0 := hUCont.mul hUCont
  have hLQSq := hL.mul hQSq hLPCont hQSqCont
  have hHUSq := hH.mul hUSq hHPCont hUSqCont
  have hdeltaRaw : EqModPow 8 delta
      (fun ε ↦ LP ε * (QP ε * QP ε) + HP ε * (UP ε * UP ε)) := by
    apply EqModPow.congr (hLQSq.add hHUSq)
    · intro ε
      dsimp only [delta]
      ring
    · intro ε
      ring
  have hdeltaPoly : EqModPow 8
      (fun ε ↦ LP ε * (QP ε * QP ε) + HP ε * (UP ε * UP ε)) deltaP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (12623528 * ε ^ 13 + 224281536 * ε ^ 12 + 304118848 * ε ^ 11 +
          116254076 * ε ^ 10 + 65467200 * ε ^ 9 + 91576112 * ε ^ 8 +
          26948078 * ε ^ 7 + 6291780 * ε ^ 6 - 3113680 * ε ^ 5 -
          2520895 * ε ^ 4 + 272540 * ε ^ 3 - 2351080 * ε ^ 2 -
          2532000 * ε + 6355) / 500)
    · fun_prop
    · intro ε
      dsimp only [LP, QP, HP, UP, deltaP]
      ring
  have hdelta : EqModPow 8 delta deltaP := hdeltaRaw.trans hdeltaPoly
  have hbetaCont : ContinuousAt beta 0 := by
    dsimp only [beta]
    have hfun :
        (((fun ε : ℝ ↦ ε ^ 3) * L) * Q) * w₁ + (H * U) * w₂ =
          (fun ε ↦ ε ^ 3 * L ε * Q ε * w₁ ε + H ε * U ε * w₂ ε) := by
      funext ε
      rfl
    rw [← hfun]
    exact (((hCubeCont.mul hLCont).mul hQCont).mul hw₁Cont).add
      ((hHCont.mul hUCont).mul hw₂Cont)
  have hgammaCont : ContinuousAt gamma 0 := by
    exact ((hSixCont.mul hLCont).mul (hw₁Cont.pow 2)).add
      (hHCont.mul (hw₂Cont.pow 2))
  have hdeltaCont : ContinuousAt delta 0 := by
    exact (hLCont.mul (hQCont.pow 2)).add (hHCont.mul (hUCont.pow 2))
  have hbetaPCont : ContinuousAt betaP 0 := by fun_prop
  have hgammaPCont : ContinuousAt gammaP 0 := by fun_prop
  have hdeltaPCont : ContinuousAt deltaP 0 := by fun_prop
  have hbetaZero : beta 0 ≠ 0 := by
    norm_num [beta, w₁, w₂, L, H, Q, U, p, h,
      DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom]
  have hgammaZero : gamma 0 ≠ 0 := by
    norm_num [gamma, w₁, w₂, L, H, Q, U, p, h,
      DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom]
  let termA₁P : ℝ → ℝ := fun ε ↦ -16 * ε ^ 6 * (2 * ε - 1)
  let termA₂P : ℝ → ℝ := fun ε ↦
    -4 * (14193 * ε ^ 7 - 22803 * ε ^ 6 + 165 * ε ^ 4 -
      1130 * ε ^ 3 - 25) / 25
  let numA₁ : ℝ → ℝ := fun ε ↦ ε ^ 6 * (L ε) ^ 2 * (w₁ ε) ^ 2
  let numA₁P : ℝ → ℝ := fun ε ↦ ε ^ 6 * (LP ε) ^ 2 * (w₁P ε) ^ 2
  let numA₂ : ℝ → ℝ := fun ε ↦ (L ε) ^ 2 * (Q ε) ^ 2
  let numA₂P : ℝ → ℝ := fun ε ↦ (LP ε) ^ 2 * (QP ε) ^ 2
  have hLSq := hL.mul hL hLPCont hLCont
  have hnumA₁ : EqModPow 8 numA₁ numA₁P := by
    have hLSqw₁Sq := hLSq.mul hw₁Sq (hLPCont.mul hLPCont) hw₁SqCont
    have hLSqw₁SqCont : ContinuousAt
        (fun ε ↦ (L ε * L ε) * (w₁ ε * w₁ ε)) 0 :=
      (hLCont.mul hLCont).mul hw₁SqCont
    have hraw := hSix.mul hLSqw₁Sq hSixCont
      hLSqw₁SqCont
    apply EqModPow.congr hraw
    · intro ε
      dsimp only [numA₁]
      ring
    · intro ε
      dsimp only [numA₁P]
      ring
  have hnumA₂ : EqModPow 8 numA₂ numA₂P := by
    have hraw := hLSq.mul hQSq (hLPCont.mul hLPCont) hQSqCont
    apply EqModPow.congr hraw
    · intro ε
      dsimp only [numA₂]
      ring
    · intro ε
      dsimp only [numA₂P]
      ring
  have htermA₁PCont : ContinuousAt termA₁P 0 := by fun_prop
  have htermA₂PCont : ContinuousAt termA₂P 0 := by fun_prop
  have htermA₁Poly : EqModPow 8 numA₁P (fun ε ↦ gammaP ε * termA₁P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (25436422144 * ε ^ 26 + 860054988800 * ε ^ 25 +
          7749048880528 * ε ^ 24 + 8094415580928 * ε ^ 23 +
          2498472844496 * ε ^ 22 + 5171171188624 * ε ^ 21 +
          3014497486148 * ε ^ 20 + 51420423168 * ε ^ 19 +
          1536307206516 * ε ^ 18 + 175997033276 * ε ^ 17 -
          135949030332 * ε ^ 16 + 258175663768 * ε ^ 15 -
          77430114295 * ε ^ 14 - 15413838812 * ε ^ 13 +
          26300340236 * ε ^ 12 - 17209171020 * ε ^ 11 +
          1094435296 * ε ^ 10 + 1641946760 * ε ^ 9 -
          1591485820 * ε ^ 8 + 312441400 * ε ^ 7 + 60931400 * ε ^ 6 -
          84506000 * ε ^ 5 + 26848800 * ε ^ 4 + 1174000 * ε ^ 3 -
          1762000 * ε ^ 2 + 696000 * ε + 10000) / 625)
    · fun_prop
    · intro ε
      dsimp only [numA₁P, gammaP, termA₁P, LP, w₁P]
      ring
  have htermA₂Poly : EqModPow 8 numA₂P (fun ε ↦ betaP ε * termA₂P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (1615396864 * ε ^ 20 + 55057573888 * ε ^ 19 + 506764418064 * ε ^ 18 +
          641597999616 * ε ^ 17 + 235933032400 * ε ^ 16 + 215586082032 * ε ^ 15 +
          287858604644 * ε ^ 14 + 103468040928 * ε ^ 13 + 34630009012 * ε ^ 12 +
          23601725524 * ε ^ 11 - 15433596 * ε ^ 10 + 2794459800 * ε ^ 9 -
          5332516575 * ε ^ 8 - 5358037180 * ε ^ 7 + 1464083452 * ε ^ 6 -
          5308679744 * ε ^ 5 + 2705430512 * ε ^ 4 + 29362920 * ε ^ 3 -
          174722960 * ε ^ 2 + 114663840 * ε + 171400) / 2500)
    · fun_prop
    · intro ε
      dsimp only [numA₂P, betaP, termA₂P, LP, QP]
      ring
  have htermA₁ : EqModPow 8 (fun ε ↦ numA₁ ε / gamma ε) termA₁P := by
    exact eqModPow_div_approx hnumA₁ hgamma htermA₁Poly hgammaPCont
      htermA₁PCont hgammaCont hgammaZero
  have htermA₂ : EqModPow 8 (fun ε ↦ numA₂ ε / beta ε) termA₂P := by
    exact eqModPow_div_approx hnumA₂ hbeta htermA₂Poly hbetaPCont
      htermA₂PCont hbetaCont hbetaZero
  let a : ℝ → ℝ := fun ε ↦ L ε - numA₁ ε / gamma ε + numA₂ ε / beta ε
  let aP : ℝ → ℝ := fun ε ↦
    6 + (1202 / 5) * ε ^ 3 - (131 / 5) * ε ^ 4 + (101262 / 25) * ε ^ 6 -
      (55332 / 25) * ε ^ 7
  have ha : EqModPow 8 a aP := by
    apply EqModPow.congr ((hL.sub htermA₁).add htermA₂)
    · intro ε
      rfl
    · intro ε
      dsimp only [LP, termA₁P, termA₂P, aP]
      ring
  have hnumA₁Cont : ContinuousAt numA₁ 0 := by
    dsimp only [numA₁]
    fun_prop
  have hnumA₂Cont : ContinuousAt numA₂ 0 := by
    dsimp only [numA₂]
    fun_prop
  have haCont : ContinuousAt a 0 :=
    (hLCont.sub (hnumA₁Cont.div hgammaCont hgammaZero)).add
      (hnumA₂Cont.div hbetaCont hbetaZero)
  have haPCont : ContinuousAt aP 0 := by fun_prop
  let termB₁P : ℝ → ℝ := fun ε ↦
    2 * ε ^ 3 * (523 * ε ^ 4 - 338 * ε ^ 3 + 10 * ε - 10) / 5
  let termB₂P : ℝ → ℝ := fun ε ↦
    -(18564 * ε ^ 7 - 19474 * ε ^ 6 + 265 * ε ^ 4 -
      1330 * ε ^ 3 - 50) / 25
  let numB₁ : ℝ → ℝ := fun ε ↦
    ε ^ 3 * L ε * H ε * w₁ ε * w₂ ε
  let numB₁P : ℝ → ℝ := fun ε ↦
    ε ^ 3 * LP ε * HP ε * w₁P ε * w₂P ε
  let numB₂ : ℝ → ℝ := fun ε ↦ L ε * Q ε * H ε * U ε
  let numB₂P : ℝ → ℝ := fun ε ↦ LP ε * QP ε * HP ε * UP ε
  have hLH := hL.mul hH hLPCont hHCont
  have hLHCont : ContinuousAt (fun ε ↦ L ε * H ε) 0 := hLCont.mul hHCont
  have hCubeLH := hCube.mul hLH hCubeCont hLHCont
  have hCubeLHCont : ContinuousAt (fun ε ↦ ε ^ 3 * (L ε * H ε)) 0 :=
    hCubeCont.mul hLHCont
  have hCubeLHw₁ := hCubeLH.mul hw₁
    (hCubeCont.mul (hLPCont.mul hHPCont)) hw₁Cont
  have hCubeLHw₁Cont : ContinuousAt
      (fun ε ↦ ε ^ 3 * (L ε * H ε) * w₁ ε) 0 :=
    hCubeLHCont.mul hw₁Cont
  have hnumB₁Raw := hCubeLHw₁.mul hw₂
    ((hCubeCont.mul (hLPCont.mul hHPCont)).mul hw₁PCont) hw₂Cont
  have hnumB₁ : EqModPow 8 numB₁ numB₁P := by
    apply EqModPow.congr hnumB₁Raw
    · intro ε
      dsimp only [numB₁]
      ring
    · intro ε
      dsimp only [numB₁P]
      ring
  have hnumB₂Raw := hLQ.mul hHU hLPQPCont hHUCont
  have hnumB₂ : EqModPow 8 numB₂ numB₂P := by
    apply EqModPow.congr hnumB₂Raw
    · intro ε
      dsimp only [numB₂]
      ring
    · intro ε
      dsimp only [numB₂P]
      ring
  have htermB₁PCont : ContinuousAt termB₁P 0 := by fun_prop
  have htermB₂PCont : ContinuousAt termB₂P 0 := by fun_prop
  have htermB₁Poly : EqModPow 8 numB₁P (fun ε ↦ gammaP ε * termB₁P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (38277120 * ε ^ 23 + 177579328 * ε ^ 22 - 9330584576 * ε ^ 21 -
          34065186848 * ε ^ 20 - 16332008104 * ε ^ 19 -
          2645965592 * ε ^ 18 - 248627460 * ε ^ 17 +
          5778046864 * ε ^ 16 - 401286660 * ε ^ 15 -
          2162720854 * ε ^ 14 - 2279877666 * ε ^ 13 +
          93209076 * ε ^ 12 - 1310603116 * ε ^ 11 -
          115137140 * ε ^ 10 + 17883222 * ε ^ 9 - 147378224 * ε ^ 8 +
          78477841 * ε ^ 7 - 389094 * ε ^ 6 + 20871272 * ε ^ 5 -
          5872030 * ε ^ 4 + 650 * ε ^ 3 + 1043160 * ε ^ 2 -
          410600 * ε - 1200) / 250)
    · fun_prop
    · intro ε
      dsimp only [numB₁P, gammaP, termB₁P, LP, HP, w₁P, w₂P]
      ring
  have htermB₂Poly : EqModPow 8 numB₂P (fun ε ↦ betaP ε * termB₂P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (7234560 * ε ^ 20 + 368458960 * ε ^ 19 + 4932756560 * ε ^ 18 +
          14285495400 * ε ^ 17 + 7893449560 * ε ^ 16 +
          13250400 * ε ^ 15 - 3422402320 * ε ^ 14 -
          2355392900 * ε ^ 13 - 46008620 * ε ^ 12 +
          1056872190 * ε ^ 11 + 508090290 * ε ^ 10 + 4294120 * ε ^ 9 +
          148776040 * ε ^ 8 + 242563870 * ε ^ 7 + 439140834 * ε ^ 6 -
          1178828608 * ε ^ 5 + 596097119 * ε ^ 4 + 9854110 * ε ^ 3 -
          35991480 * ε ^ 2 + 18308320 * ε + 59650) / 2500)
    · fun_prop
    · intro ε
      dsimp only [numB₂P, betaP, termB₂P, LP, QP, HP, UP]
      ring
  have htermB₁ : EqModPow 8 (fun ε ↦ numB₁ ε / gamma ε) termB₁P := by
    exact eqModPow_div_approx hnumB₁ hgamma htermB₁Poly hgammaPCont
      htermB₁PCont hgammaCont hgammaZero
  have htermB₂ : EqModPow 8 (fun ε ↦ numB₂ ε / beta ε) termB₂P := by
    exact eqModPow_div_approx hnumB₂ hbeta htermB₂Poly hbetaPCont
      htermB₂PCont hbetaCont hbetaZero
  let b : ℝ → ℝ := fun ε ↦ -(numB₁ ε / gamma ε) + numB₂ ε / beta ε
  let bP : ℝ → ℝ := fun ε ↦
    2 + (286 / 5) * ε ^ 3 - (73 / 5) * ε ^ 4 + (22854 / 25) * ε ^ 6 -
      (23794 / 25) * ε ^ 7
  have hb : EqModPow 8 b bP := by
    apply EqModPow.congr (htermB₁.neg.add htermB₂)
    · intro ε
      rfl
    · intro ε
      dsimp only [termB₁P, termB₂P, bP]
      ring
  have hnumB₁Cont : ContinuousAt numB₁ 0 := by
    dsimp only [numB₁]
    fun_prop
  have hnumB₂Cont : ContinuousAt numB₂ 0 := by
    dsimp only [numB₂]
    fun_prop
  have hbCont : ContinuousAt b 0 :=
    (hnumB₁Cont.div hgammaCont hgammaZero).neg.add
      (hnumB₂Cont.div hbetaCont hbetaZero)
  have hbPCont : ContinuousAt bP 0 := by fun_prop
  let termD₁P : ℝ → ℝ := fun ε ↦ 18 * ε ^ 7 - 2 * ε ^ 6 - 2 * ε ^ 3 + 1
  let termD₂P : ℝ → ℝ := fun ε ↦
    -(1116 * ε ^ 7 - 1064 * ε ^ 6 + 20 * ε ^ 4 -
      40 * ε ^ 3 - 5) / 5
  let numD₁ : ℝ → ℝ := fun ε ↦ (H ε) ^ 2 * (w₂ ε) ^ 2
  let numD₁P : ℝ → ℝ := fun ε ↦ (HP ε) ^ 2 * (w₂P ε) ^ 2
  let numD₂ : ℝ → ℝ := fun ε ↦ (H ε) ^ 2 * (U ε) ^ 2
  let numD₂P : ℝ → ℝ := fun ε ↦ (HP ε) ^ 2 * (UP ε) ^ 2
  have hHSq := hH.mul hH hHPCont hHCont
  have hHSqCont : ContinuousAt (fun ε ↦ H ε * H ε) 0 := hHCont.mul hHCont
  have hnumD₁Raw := hHSq.mul hw₂Sq (hHPCont.mul hHPCont) hw₂SqCont
  have hnumD₁ : EqModPow 8 numD₁ numD₁P := by
    apply EqModPow.congr hnumD₁Raw
    · intro ε
      dsimp only [numD₁]
      ring
    · intro ε
      dsimp only [numD₁P]
      ring
  have hnumD₂Raw := hHSq.mul hUSq (hHPCont.mul hHPCont) hUSqCont
  have hnumD₂ : EqModPow 8 numD₂ numD₂P := by
    apply EqModPow.congr hnumD₂Raw
    · intro ε
      dsimp only [numD₂]
      ring
    · intro ε
      dsimp only [numD₂P]
      ring
  have htermD₁PCont : ContinuousAt termD₁P 0 := by fun_prop
  have htermD₂PCont : ContinuousAt termD₂P 0 := by fun_prop
  have htermD₁Poly : EqModPow 8 numD₁P (fun ε ↦ gammaP ε * termD₁P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (57600 * ε ^ 20 - 1413120 * ε ^ 19 + 3390976 * ε ^ 18 +
          64710336 * ε ^ 17 + 120856640 * ε ^ 16 + 3581504 * ε ^ 15 -
          18969436 * ε ^ 14 - 87321736 * ε ^ 13 - 1988476 * ε ^ 12 +
          5878176 * ε ^ 11 + 57038152 * ε ^ 10 + 97224 * ε ^ 9 +
          2099536 * ε ^ 8 - 15620956 * ε ^ 7 + 28752 * ε ^ 6 -
          143424 * ε ^ 5 + 3484768 * ε ^ 4 - 44 * ε ^ 3 +
          32632 * ε ^ 2 - 108096 * ε + 121) / 100)
    · fun_prop
    · intro ε
      dsimp only [numD₁P, gammaP, termD₁P, HP, w₂P]
      ring
  have htermD₂Poly : EqModPow 8 numD₂P (fun ε ↦ betaP ε * termD₂P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (6480 * ε ^ 20 + 439200 * ε ^ 19 + 8642960 * ε ^ 18 +
          40707120 * ε ^ 17 + 55843040 * ε ^ 16 - 2275120 * ε ^ 15 -
          28234220 * ε ^ 14 - 59565560 * ε ^ 13 - 237900 * ε ^ 12 +
          11444320 * ε ^ 11 + 39931160 * ε ^ 10 + 306040 * ε ^ 9 -
          1724080 * ε ^ 8 - 15911500 * ε ^ 7 + 26179236 * ε ^ 6 -
          64970480 * ε ^ 5 + 41709984 * ε ^ 4 + 665960 * ε ^ 3 -
          560760 * ε ^ 2 - 169120 * ε + 4205) / 500)
    · fun_prop
    · intro ε
      dsimp only [numD₂P, betaP, termD₂P, HP, UP]
      ring
  have htermD₁ : EqModPow 8 (fun ε ↦ numD₁ ε / gamma ε) termD₁P := by
    exact eqModPow_div_approx hnumD₁ hgamma htermD₁Poly hgammaPCont
      htermD₁PCont hgammaCont hgammaZero
  have htermD₂ : EqModPow 8 (fun ε ↦ numD₂ ε / beta ε) termD₂P := by
    exact eqModPow_div_approx hnumD₂ hbeta htermD₂Poly hbetaPCont
      htermD₂PCont hbetaCont hbetaZero
  let d : ℝ → ℝ := fun ε ↦ H ε - numD₁ ε / gamma ε + numD₂ ε / beta ε
  let dP : ℝ → ℝ := fun ε ↦
    1 + 8 * ε ^ 3 - 4 * ε ^ 4 + (1104 / 5) * ε ^ 6 -
      (1196 / 5) * ε ^ 7
  have hd : EqModPow 8 d dP := by
    apply EqModPow.congr ((hH.sub htermD₁).add htermD₂)
    · intro ε
      rfl
    · intro ε
      dsimp only [HP, termD₁P, termD₂P, dP]
      ring
  have hnumD₁Cont : ContinuousAt numD₁ 0 := by
    dsimp only [numD₁]
    fun_prop
  have hnumD₂Cont : ContinuousAt numD₂ 0 := by
    dsimp only [numD₂]
    fun_prop
  have hdCont : ContinuousAt d 0 :=
    (hHCont.sub (hnumD₁Cont.div hgammaCont hgammaZero)).add
      (hnumD₂Cont.div hbetaCont hbetaZero)
  have hdPCont : ContinuousAt dP 0 := by fun_prop
  let threeBeta : ℝ → ℝ := fun ε ↦ 3 * beta ε
  let threeBetaP : ℝ → ℝ := fun ε ↦ 3 * betaP ε
  let numq : ℝ → ℝ := fun ε ↦ ε ^ 3 * delta ε * w₁ ε
  let numqP : ℝ → ℝ := fun ε ↦ ε ^ 3 * deltaP ε * w₁P ε
  let numv : ℝ → ℝ := fun ε ↦ delta ε * w₂ ε
  let numvP : ℝ → ℝ := fun ε ↦ deltaP ε * w₂P ε
  let termqP : ℝ → ℝ := fun ε ↦
    ε ^ 3 * (483 * ε ^ 4 - 228 * ε ^ 3 + 10 * ε - 10) / 5
  let termvP : ℝ → ℝ := fun ε ↦
    -(54868 * ε ^ 7 - 18888 * ε ^ 6 + 1035 * ε ^ 4 -
      2820 * ε ^ 3 - 150) / 150
  have hThree : EqModPow 8 (fun _ : ℝ ↦ (3 : ℝ))
      (fun _ : ℝ ↦ (3 : ℝ)) := EqModPow.refl 8 _
  have hThreeCont : ContinuousAt (fun _ : ℝ ↦ (3 : ℝ)) 0 := continuousAt_const
  have hthreeBetaRaw := hThree.mul hbeta hThreeCont hbetaCont
  have hthreeBeta : EqModPow 8 threeBeta threeBetaP := by
    simpa only [threeBeta, threeBetaP] using hthreeBetaRaw
  have hthreeBetaCont : ContinuousAt threeBeta 0 := hThreeCont.mul hbetaCont
  have hthreeBetaPCont : ContinuousAt threeBetaP 0 := hThreeCont.mul hbetaPCont
  have hthreeBetaZero : threeBeta 0 ≠ 0 := by
    have hThreeNe : (3 : ℝ) ≠ 0 := by norm_num
    dsimp only [threeBeta]
    exact mul_ne_zero hThreeNe hbetaZero
  have hCubeDelta := hCube.mul hdelta hCubeCont hdeltaCont
  have hCubeDeltaCont : ContinuousAt (fun ε ↦ ε ^ 3 * delta ε) 0 :=
    hCubeCont.mul hdeltaCont
  have hnumqRaw := hCubeDelta.mul hw₁
    (hCubeCont.mul hdeltaPCont) hw₁Cont
  have hnumq : EqModPow 8 numq numqP := by
    simpa only [numq, numqP] using hnumqRaw
  have hnumvRaw := hdelta.mul hw₂ hdeltaPCont hw₂Cont
  have hnumv : EqModPow 8 numv numvP := by
    simpa only [numv, numvP] using hnumvRaw
  have htermqPCont : ContinuousAt termqP 0 := by fun_prop
  have htermvPCont : ContinuousAt termvP 0 := by fun_prop
  have htermqPoly : EqModPow 8 numqP (fun ε ↦ threeBetaP ε * termqP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(12479936 * ε ^ 9 + 4923864 * ε ^ 8 - 1562304 * ε ^ 7 +
          11823914 * ε ^ 6 - 20369608 * ε ^ 5 + 4942368 * ε ^ 4 +
          471485 * ε ^ 3 - 856550 * ε ^ 2 + 218640 * ε + 6150) / 125)
    · fun_prop
    · intro ε
      dsimp only [numqP, threeBetaP, betaP, termqP, deltaP, w₁P]
      ring
  have htermvPoly : EqModPow 8 numvP (fun ε ↦ threeBetaP ε * termvP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (316285032 * ε ^ 6 - 505547264 * ε ^ 5 + 150983232 * ε ^ 4 +
          8919530 * ε ^ 3 - 11221040 * ε ^ 2 + 4131360 * ε + 63075) / 1250)
    · fun_prop
    · intro ε
      dsimp only [numvP, threeBetaP, betaP, termvP, deltaP, w₂P]
      ring
  have htermq : EqModPow 8 (fun ε ↦ numq ε / threeBeta ε) termqP := by
    exact eqModPow_div_approx hnumq hthreeBeta htermqPoly hthreeBetaPCont
      htermqPCont hthreeBetaCont hthreeBetaZero
  have htermv : EqModPow 8 (fun ε ↦ numv ε / threeBeta ε) termvP := by
    exact eqModPow_div_approx hnumv hthreeBeta htermvPoly hthreeBetaPCont
      htermvPCont hthreeBetaCont hthreeBetaZero
  let q : ℝ → ℝ := fun ε ↦ Q ε - numq ε / threeBeta ε
  let v : ℝ → ℝ := fun ε ↦ U ε - numv ε / threeBeta ε
  let qP : ℝ → ℝ := fun ε ↦
    1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - 128 * ε ^ 7
  let vP : ℝ → ℝ := fun ε ↦
    -(38 / 5) * ε ^ 3 + (29 / 5) * ε ^ 4 - (4538 / 25) * ε ^ 6 +
      (27299 / 75) * ε ^ 7
  have hq : EqModPow 8 q qP := by
    apply EqModPow.congr (hQ.sub htermq)
    · intro ε
      rfl
    · intro ε
      dsimp only [QP, termqP, qP]
      ring
  have hv : EqModPow 8 v vP := by
    apply EqModPow.congr (hU.sub htermv)
    · intro ε
      rfl
    · intro ε
      dsimp only [UP, termvP, vP]
      ring
  have hnumqCont : ContinuousAt numq 0 := by
    dsimp only [numq]
    fun_prop
  have hnumvCont : ContinuousAt numv 0 := by
    dsimp only [numv]
    fun_prop
  have hqCont : ContinuousAt q 0 :=
    hQCont.sub (hnumqCont.div hthreeBetaCont hthreeBetaZero)
  have hvCont : ContinuousAt v 0 :=
    hUCont.sub (hnumvCont.div hthreeBetaCont hthreeBetaZero)
  have hqPCont : ContinuousAt qP 0 := by fun_prop
  have hvPCont : ContinuousAt vP 0 := by fun_prop
  let A : ℝ → ℝ := fun ε ↦ ε ^ 4 * a ε
  let E : ℝ → ℝ := fun ε ↦ ε ^ 2 * b ε
  let AP : ℝ → ℝ := fun ε ↦ ε ^ 4 * aP ε
  let EP : ℝ → ℝ := fun ε ↦ ε ^ 2 * bP ε
  have hpowFour : EqModPow 8 (fun ε : ℝ ↦ ε ^ 4)
      (fun ε : ℝ ↦ ε ^ 4) := EqModPow.refl 8 _
  have hpowTwo : EqModPow 8 (fun ε : ℝ ↦ ε ^ 2)
      (fun ε : ℝ ↦ ε ^ 2) := EqModPow.refl 8 _
  have hpowFourCont : ContinuousAt (fun ε : ℝ ↦ ε ^ 4) 0 := by fun_prop
  have hpowTwoCont : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by fun_prop
  have hA : EqModPow 8 A AP := by
    simpa only [A, AP] using hpowFour.mul ha hpowFourCont haCont
  have hE : EqModPow 8 E EP := by
    simpa only [E, EP] using hpowTwo.mul hb hpowTwoCont hbCont
  have hACont : ContinuousAt A 0 := hpowFourCont.mul haCont
  have hECont : ContinuousAt E 0 := hpowTwoCont.mul hbCont
  have hAPCont : ContinuousAt AP 0 := hpowFourCont.mul haPCont
  have hEPCont : ContinuousAt EP 0 := hpowTwoCont.mul hbPCont
  let rad : ℝ → ℝ := fun ε ↦ (d ε - A ε) ^ 2 + 4 * (E ε) ^ 2
  let radP : ℝ → ℝ := fun ε ↦ (dP ε - AP ε) ^ 2 + 4 * (EP ε) ^ 2
  have hdiffDA := hd.sub hA
  have hdiffDACont : ContinuousAt (fun ε ↦ d ε - A ε) 0 := hdCont.sub hACont
  have hdiffDAPCont : ContinuousAt (fun ε ↦ dP ε - AP ε) 0 := hdPCont.sub hAPCont
  have hdiffDASq := hdiffDA.mul hdiffDA hdiffDAPCont hdiffDACont
  have hESq := hE.mul hE hEPCont hECont
  have hFour : EqModPow 8 (fun _ : ℝ ↦ (4 : ℝ))
      (fun _ : ℝ ↦ (4 : ℝ)) := EqModPow.refl 8 _
  have hFourCont : ContinuousAt (fun _ : ℝ ↦ (4 : ℝ)) 0 := continuousAt_const
  have hrad : EqModPow 8 rad radP := by
    have hscaledESq := hFour.mul hESq hFourCont (hECont.mul hECont)
    apply EqModPow.congr (hdiffDASq.add hscaledESq)
    · intro ε
      dsimp only [rad]
      ring
    · intro ε
      dsimp only [radP]
      ring
  let gapP : ℝ → ℝ := fun ε ↦
    1 + 8 * ε ^ 3 - 2 * ε ^ 4 + (1104 / 5) * ε ^ 6 - 86 * ε ^ 7
  have hgapSquare : EqModPow 8 radP (fun ε ↦ (gapP ε) ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (3061630224 * ε ^ 14 - 11206057968 * ε ^ 13 +
          10253992644 * ε ^ 12 + 72484920 * ε ^ 11 +
          805103164 * ε ^ 10 - 1311176568 * ε ^ 9 +
          971717809 * ε ^ 8 + 26105580 * ε ^ 7 - 119804440 * ε ^ 6 +
          112311360 * ε ^ 5 + 205400 * ε ^ 4 - 4884600 * ε ^ 3 +
          6114100 * ε ^ 2 - 53250) / 625)
    · fun_prop
    · intro ε
      dsimp only [radP, dP, AP, aP, EP, bP, gapP]
      ring
  have hradCont : ContinuousAt rad 0 :=
    (hdiffDACont.pow 2).add ((hECont.pow 2).const_mul 4)
  have hgapPCont : ContinuousAt gapP 0 := by fun_prop
  have hEightPositive : 0 < (8 : ℕ) := by norm_num
  have hdAtZero : d 0 = dP 0 := EqModPow.eq_at_zero_of_pos hEightPositive hd
  have hAAtZero : A 0 = AP 0 := EqModPow.eq_at_zero_of_pos hEightPositive hA
  have hEAtZero : E 0 = EP 0 := EqModPow.eq_at_zero_of_pos hEightPositive hE
  have hradZero : 0 < rad 0 := by
    dsimp only [rad]
    rw [hdAtZero, hAAtZero, hEAtZero]
    norm_num [dP, AP, aP, EP, bP]
  have hgapPZero : 0 < gapP 0 := by norm_num [gapP]
  have hgap : EqModPow 8 (fun ε ↦ Real.sqrt (rad ε)) gapP := by
    exact EqModPow.sqrt_of_sq (hrad.trans hgapSquare) hradCont hgapPCont
      hradZero hgapPZero
  let low : ℝ → ℝ := fun ε ↦ (A ε + d ε - Real.sqrt (rad ε)) / 2
  let lowRawP : ℝ → ℝ := fun ε ↦ (AP ε + dP ε - gapP ε) / 2
  let lowP : ℝ → ℝ := fun ε ↦ 2 * ε ^ 4 + (218 / 5) * ε ^ 7
  have hTwoRefl : EqModPow 8 (fun _ : ℝ ↦ (2 : ℝ))
      (fun _ : ℝ ↦ (2 : ℝ)) := EqModPow.refl 8 _
  have hTwoCont : ContinuousAt (fun _ : ℝ ↦ (2 : ℝ)) 0 := continuousAt_const
  have hTwoZero : (fun _ : ℝ ↦ (2 : ℝ)) 0 ≠ 0 := by norm_num
  have hlowNumerator := (hA.add hd).sub hgap
  have hlowRawPCont : ContinuousAt lowRawP 0 := by fun_prop
  have hlowDenPoly : EqModPow 8
      (fun ε ↦ AP ε + dP ε - gapP ε)
      (fun ε ↦ 2 * lowRawP ε) := by
    apply eqModPow_of_eq
    intro ε
    dsimp only [lowRawP]
    ring
  have hlowRaw : EqModPow 8 low lowRawP := by
    exact eqModPow_div_approx hlowNumerator hTwoRefl hlowDenPoly hTwoCont
      hlowRawPCont hTwoCont hTwoZero
  have hlowPoly : EqModPow 8 lowRawP lowP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -(55332 * ε ^ 3 - 101262 * ε ^ 2 + 655) / 50)
    · fun_prop
    · intro ε
      dsimp only [lowRawP, lowP, AP, aP, dP, gapP]
      ring
  have hlow : EqModPow 8 low lowP := hlowRaw.trans hlowPoly
  have hlowCont : ContinuousAt low 0 :=
    ((hACont.add hdCont).sub hradCont.sqrt).div_const 2
  have hlowPCont : ContinuousAt lowP 0 := by fun_prop
  let denRad : ℝ → ℝ := fun ε ↦ (d ε - low ε) ^ 2 + (E ε) ^ 2
  let denRadP : ℝ → ℝ := fun ε ↦ (dP ε - lowP ε) ^ 2 + (EP ε) ^ 2
  have hdiffDL := hd.sub hlow
  have hdiffDLCont : ContinuousAt (fun ε ↦ d ε - low ε) 0 := hdCont.sub hlowCont
  have hdiffDLPCont : ContinuousAt (fun ε ↦ dP ε - lowP ε) 0 :=
    hdPCont.sub hlowPCont
  have hdiffDLSq := hdiffDL.mul hdiffDL hdiffDLPCont hdiffDLCont
  have hdenRad : EqModPow 8 denRad denRadP := by
    apply EqModPow.congr (hdiffDLSq.add hESq)
    · intro ε
      dsimp only [denRad]
      ring
    · intro ε
      dsimp only [denRadP]
      ring
  let denP : ℝ → ℝ := fun ε ↦
    1 + 8 * ε ^ 3 - 4 * ε ^ 4 + (1104 / 5) * ε ^ 6 -
      (922 / 5) * ε ^ 7
  have hdenSquare : EqModPow 8 denRadP (fun ε ↦ (denP ε) ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (566154436 * ε ^ 10 - 1087576152 * ε ^ 9 + 522305316 * ε ^ 8 +
          17369620 * ε ^ 7 - 56001460 * ε ^ 6 + 38204040 * ε ^ 5 +
          133225 * ε ^ 4 - 2224300 * ε ^ 3 + 2794300 * ε ^ 2 -
          24000) / 625)
    · fun_prop
    · intro ε
      dsimp only [denRadP, dP, lowP, EP, bP, denP]
      ring
  have hdenRadCont : ContinuousAt denRad 0 :=
    (hdiffDLCont.pow 2).add (hECont.pow 2)
  have hdenPCont : ContinuousAt denP 0 := by fun_prop
  have hlowAtZero : low 0 = lowP 0 := EqModPow.eq_at_zero_of_pos hEightPositive hlow
  have hdenRadZero : 0 < denRad 0 := by
    dsimp only [denRad]
    rw [hdAtZero, hlowAtZero, hEAtZero]
    norm_num [dP, lowP, EP, bP]
  have hdenPZero : 0 < denP 0 := by norm_num [denP]
  have hden : EqModPow 8 (fun ε ↦ Real.sqrt (denRad ε)) denP := by
    exact EqModPow.sqrt_of_sq (hdenRad.trans hdenSquare) hdenRadCont hdenPCont
      hdenRadZero hdenPZero
  let numerator : ℝ → ℝ := fun ε ↦
    (d ε - low ε) * q ε - ε ^ 4 * b ε * v ε
  let numeratorP : ℝ → ℝ := fun ε ↦
    (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε
  let amplitudeP : ℝ → ℝ := fun ε ↦
    1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7
  have hleftNumerator := hdiffDL.mul hq hdiffDLPCont hqCont
  have hpowFourB := hpowFour.mul hb hpowFourCont hbCont
  have hpowFourBPCont : ContinuousAt (fun ε ↦ ε ^ 4 * bP ε) 0 :=
    hpowFourCont.mul hbPCont
  have hrightNumerator := hpowFourB.mul hv hpowFourBPCont hvCont
  have hnumerator : EqModPow 8 numerator numeratorP := by
    simpa only [numerator, numeratorP] using hleftNumerator.sub hrightNumerator
  have hamplitudePCont : ContinuousAt amplitudeP 0 := by fun_prop
  have hfinalPoly : EqModPow 8 numeratorP (fun ε ↦ denP ε * amplitudeP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (649552406 * ε ^ 10 - 947822862 * ε ^ 9 + 311134356 * ε ^ 8 +
          20314525 * ε ^ 7 - 67129150 * ε ^ 6 + 56035200 * ε ^ 5 +
          158775 * ε ^ 4 - 2080300 * ε ^ 3 + 3244800 * ε ^ 2 -
          19875) / 1875)
    · fun_prop
    · intro ε
      dsimp only [numeratorP, dP, lowP, qP, bP, vP, denP, amplitudeP]
      ring
  have hdenCont : ContinuousAt (fun ε ↦ Real.sqrt (denRad ε)) 0 :=
    hdenRadCont.sqrt
  have hdenZero : Real.sqrt (denRad 0) ≠ 0 := by positivity
  have hamplitude : EqModPow 8
      (fun ε ↦ numerator ε / Real.sqrt (denRad ε)) amplitudeP := by
    exact eqModPow_div_approx hnumerator hden hfinalPoly hdenPCont
      hamplitudePCont hdenCont hdenZero
  refine ⟨?_, ?_, ?_⟩
  · apply EqModPow.congr hamplitude
    · intro ε
      dsimp only [numerator, denRad, low, A, E, rad, a, b, d, q, v,
        numA₁, numA₂, numB₁, numB₂, numD₁, numD₂, numq, numv,
        threeBeta, L, H, Q, U]
      simp only [DFP.SecondLeg.gradientFactors, RealSymmetric2.lowDenom,
        RealSymmetric2.low, RealSymmetric2.gap]
      ring
    · intro ε
      rfl
  · have hEPoly : EqModPow 8 EP
        (fun ε : ℝ ↦
          2 * ε ^ 2 + (286 / 5) * ε ^ 5 - (73 / 5) * ε ^ 6) := by
      apply EqModPow.of_factor
        (q := fun ε : ℝ ↦ (22854 / 25) - (23794 / 25) * ε)
      · fun_prop
      · intro ε
        dsimp only [EP, bP]
        ring
    apply EqModPow.congr (hE.trans hEPoly)
    · intro ε
      dsimp only [E, b, numB₁, numB₂, gamma, beta, w₁, w₂,
        L, H, Q, U, p, h]
      rfl
    · intro ε
      rfl
  · apply EqModPow.congr hdiffDL
    · intro ε
      change d ε - RealSymmetric2.low (A ε) (E ε) (d ε) = d ε - low ε
      dsimp only [low, rad]
      simp only [RealSymmetric2.low, RealSymmetric2.gap]
    · intro ε
      dsimp only [dP, lowP]
      ring


/-- The four first-leg removable factors have their order-eight germs along the
polynomial slow graph. -/
theorem slowGraphFirstLegFactorGerms :
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.spectralFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).1)
        (fun ε : ℝ ↦
          2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4 +
            418 * ε ^ 6 + (128 / 5) * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.spectralFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).2)
        (fun ε : ℝ ↦ 1 - 2 * ε ^ 3 + 6 * ε ^ 6 + 2 * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.gradientFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).1)
        (fun ε : ℝ ↦
          1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 - (112 / 5) * ε ^ 6 -
            (157 / 5) * ε ^ 7) ∧
    EqModPow 8
        (fun ε : ℝ ↦
          (DFP.FirstLeg.gradientFactors ε
            (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
            (1 + 8 * ε ^ 3)).2)
        (fun ε : ℝ ↦
          1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4 - (278 / 5) * ε ^ 6 -
            (9 / 5) * ε ^ 7) := by
  rcases slowGraphFirstLegAllGerms with ⟨hL, hH, hQ, hU, _, _⟩
  exact ⟨hL, hH, hQ, hU⟩

/-- The removable low second-leg gradient factor has its order-eight germ along
the polynomial slow graph. -/
theorem slowGraphSecondLegAmplitudeGerm :
    EqModPow 8
      (fun ε : ℝ ↦
        (DFP.SecondLeg.gradientFactors ε
          (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
          (1 + 8 * ε ^ 3)).1)
      (fun ε : ℝ ↦
        1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7) := by
  exact slowGraphSecondLegAllGerms.1

/-- Along the polynomial slow graph, the first- and second-leg raw frame
off-diagonal entries and high-minus-low entries have these order-eight germs. -/
theorem slowGraphRawFrameGerms :
    EqModPow 8
      (fun ε : ℝ ↦
        let x := slowGraphJetPath ε
        let M := DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2
        M 0 1)
      (fun ε : ℝ ↦ ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6) ∧
    EqModPow 8
      (fun ε : ℝ ↦
        let x := slowGraphJetPath ε
        let M := DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2
        M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1))
      (fun ε : ℝ ↦
        1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7) ∧
    EqModPow 8
      (fun ε : ℝ ↦
        let x := slowGraphJetPath ε
        let M := DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2
        M 0 1)
      (fun ε : ℝ ↦
        2 * ε ^ 2 + (286 / 5) * ε ^ 5 - (73 / 5) * ε ^ 6) ∧
    EqModPow 8
      (fun ε : ℝ ↦
        let x := slowGraphJetPath ε
        let M := DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2
        M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1))
      (fun ε : ℝ ↦
        1 + 8 * ε ^ 3 - 6 * ε ^ 4 + (1104 / 5) * ε ^ 6 -
          (1414 / 5) * ε ^ 7) := by
  rcases slowGraphFirstLegAllGerms with ⟨_, _, _, _, hE₁, hx₁⟩
  rcases slowGraphSecondLegAllGerms with ⟨_, hE₂, hx₂⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply EqModPow.congr hE₁
    · intro ε
      rw [slowGraphJetPath_apply]
    · intro ε
      rfl
  · apply EqModPow.congr hx₁
    · intro ε
      rw [slowGraphJetPath_apply]
    · intro ε
      rfl
  · apply EqModPow.congr hE₂
    · intro ε
      rw [slowGraphJetPath_apply]
    · intro ε
      rfl
  · apply EqModPow.congr hx₂
    · intro ε
      rw [slowGraphJetPath_apply]
    · intro ε
      rfl

/-- Along the polynomial slow graph, the normalized amplitude equals its stated
degree-seven polynomial up to `O(ε ^ 8)`, independently of the legacy theorem. -/
theorem slowGraphAmplitudeRemainderDirect :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hpathCont : ContinuousAt slowGraphJetPath 0 := by
    have hpoly : ContinuousAt
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    apply hpoly.congr_of_eventuallyEq
    filter_upwards [] with ε
    exact slowGraphJetPath_apply ε
  have hpathZero : slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [slowGraphJetPath_apply]
    norm_num
  have hpathTendsto : Tendsto slowGraphJetPath (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    rw [← hpathZero]
    exact hpathCont
  have hfactorization := hpathTendsto.eventually DFP.SecondLeg.gradientFactorization
  have hobservable : ∀ᶠ ε in 𝓝 0,
      (observableMap (slowGraphJetPath ε)).amplitudeRatio =
        (DFP.SecondLeg.gradientFactors ε
          (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
          (1 + 8 * ε ^ 3)).1 := by
    filter_upwards [hfactorization] with ε hε
    simp only [slowGraphJetPath_apply] at hε ⊢
    rw [observableMap_amplitudeRatio]
    have hv := hε 1
    simp only [one_smul] at hv
    unfold DFP.SecondLeg.coordinates
    exact congrArg (fun v : Fin 2 → ℝ ↦ v 0) hv
  refine (EqModPow.to_isBigO slowGraphSecondLegAmplitudeGerm).congr' ?_
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [hobservable] with ε hε
  rw [hε]

end DFP.TwoLeg
