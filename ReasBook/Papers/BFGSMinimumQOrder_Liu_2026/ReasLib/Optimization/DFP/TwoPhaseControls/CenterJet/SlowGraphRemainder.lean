module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterCancellationBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.QuotientGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterCancellationBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.QuotientGerm

public section

noncomputable section

open Filter
open Asymptotics
open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.CenterJet

private def slowP (ε : ℝ) : ℝ :=
  2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4

private def slowH (ε : ℝ) : ℝ := 1 + 8 * ε ^ 3

private def slowL (ε : ℝ) : ℝ :=
  (DFP.FirstLeg.spectralFactors ε (slowP ε) (slowH ε)).1

private def slowHigh (ε : ℝ) : ℝ :=
  (DFP.FirstLeg.spectralFactors ε (slowP ε) (slowH ε)).2

private def slowQ (ε : ℝ) : ℝ :=
  (DFP.FirstLeg.gradientFactors ε (slowP ε) (slowH ε)).1

private def slowU (ε : ℝ) : ℝ :=
  (DFP.FirstLeg.gradientFactors ε (slowP ε) (slowH ε)).2

private def slowLQ (ε : ℝ) : ℝ := slowL ε * slowQ ε

private def slowHU (ε : ℝ) : ℝ := slowHigh ε * slowU ε

private def slowBeta (ε : ℝ) : ℝ :=
  ε ^ 4 * (slowLQ ε) ^ 2 - 4 * ε ^ 3 * slowLQ ε * slowHU ε +
    (slowHU ε) ^ 2

private def slowDelta (ε : ℝ) : ℝ :=
  slowQ ε * slowLQ ε + slowU ε * slowHU ε

private def slowTransportLow (ε : ℝ) : ℝ :=
  -slowQ ε - 2 * slowDelta ε * ε ^ 3 * slowHU ε / (3 * slowBeta ε)

private def slowTransportHighFactor (ε : ℝ) : ℝ :=
  -slowU ε - 2 * slowDelta ε * ε ^ 3 * slowLQ ε / (3 * slowBeta ε)

private def slowB (ε : ℝ) : ℝ := 1 + 2 * ε ^ 3 + ε ^ 4

private def slowC (ε : ℝ) : ℝ :=
  (1 + ε ^ 3) ^ 2 + slowP ε * ε ^ 6 * (1 + ε) ^ 2

private def slowOffDiagFactor (ε : ℝ) : ℝ :=
  1 / slowB ε -
    slowH ε * slowP ε * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / slowC ε

private def slowCenterCoefficient (ε : ℝ) : ℝ :=
  2 * (slowP ε + 1) / (3 * slowB ε)

private def slowFrameOffDiag (ε : ℝ) : ℝ :=
  (DFP.FirstLeg.outputMetric ε (slowP ε) (slowH ε)) 0 1

private def slowFrameHighMinusLow (ε : ℝ) : ℝ :=
  let M := DFP.FirstLeg.outputMetric ε (slowP ε) (slowH ε)
  M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1)

private def slowFrameDenom (ε : ℝ) : ℝ :=
  Real.sqrt ((slowFrameHighMinusLow ε) ^ 2 + (slowFrameOffDiag ε) ^ 2)

private def slowCanceledFullLow (ε : ℝ) : ℝ :=
  1 - slowCenterCoefficient ε * ε ^ 4 +
    (slowFrameHighMinusLow ε * slowTransportLow ε +
      slowFrameOffDiag ε * ε ^ 2 * slowTransportHighFactor ε) /
        slowFrameDenom ε

private def slowCanceledFullHigh (ε : ℝ) : ℝ :=
  ε ^ 2 * (slowP ε - slowCenterCoefficient ε) +
    (-slowFrameOffDiag ε * slowTransportLow ε +
      slowFrameHighMinusLow ε * ε ^ 2 * slowTransportHighFactor ε) /
        slowFrameDenom ε

/-- The canceled second-leg displacement minus its output gradient has two
removable scalar transport factors. -/
private theorem secondTransport_eq (ε : ℝ) :
    (fun i ↦ DFP.TwoLeg.CenterCancellation.secondDisplacement
        ε (slowP ε) (slowH ε) i -
      DFP.SecondLeg.outputGradient ε (slowP ε) (slowH ε) i) =
      ![slowTransportLow ε, ε ^ 2 * slowTransportHighFactor ε] := by
  unfold slowTransportLow slowTransportHighFactor slowBeta slowDelta
    slowLQ slowHU slowL slowHigh slowQ slowU
  ext i
  fin_cases i <;>
    simp [DFP.TwoLeg.CenterCancellation.secondDisplacement,
      DFP.TwoLeg.CenterCancellation.secondEnergyFactor,
      DFP.SecondLeg.outputGradient] <;>
    ring

/-- The first frame applied to the removable transport factors has the displayed
low coordinate. -/
private theorem firstFrame_transport_low (ε : ℝ) :
    (DFP.FirstLeg.frame ε (slowP ε) (slowH ε) *ᵥ
      ![slowTransportLow ε, ε ^ 2 * slowTransportHighFactor ε]) 0 =
        (slowFrameHighMinusLow ε * slowTransportLow ε +
          slowFrameOffDiag ε * ε ^ 2 * slowTransportHighFactor ε) /
            slowFrameDenom ε := by
  unfold slowFrameDenom slowFrameHighMinusLow slowFrameOffDiag
  simp [DFP.FirstLeg.frame, RealSymmetric2.lowVector,
    RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
    EuclideanPlane.frame, EuclideanPlane.perp_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The first frame applied to the removable transport factors has the displayed
high coordinate. -/
private theorem firstFrame_transport_high (ε : ℝ) :
    (DFP.FirstLeg.frame ε (slowP ε) (slowH ε) *ᵥ
      ![slowTransportLow ε, ε ^ 2 * slowTransportHighFactor ε]) 1 =
        (-slowFrameOffDiag ε * slowTransportLow ε +
          slowFrameHighMinusLow ε * ε ^ 2 * slowTransportHighFactor ε) /
            slowFrameDenom ε := by
  unfold slowFrameDenom slowFrameHighMinusLow slowFrameOffDiag
  simp [DFP.FirstLeg.frame, RealSymmetric2.lowVector,
    RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
    EuclideanPlane.frame, EuclideanPlane.perp_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The canceled full-center displacement splits into its first displacement,
initial gradient, and transported second residual. -/
private theorem canceledFullCenter_split (ε : ℝ) (i : Fin 2) :
    DFP.TwoLeg.CenterCancellation.canceledFullCenterDisplacement
        (ε, slowP ε, slowH ε) i =
      DFP.TwoLeg.CenterCancellation.firstDisplacement ε (slowP ε) i +
        ![(1 : ℝ), slowP ε * ε ^ 2] i +
        (DFP.FirstLeg.frame ε (slowP ε) (slowH ε) *ᵥ
          (fun j ↦ DFP.TwoLeg.CenterCancellation.secondDisplacement
              ε (slowP ε) (slowH ε) j -
            DFP.SecondLeg.outputGradient ε (slowP ε) (slowH ε) j)) i := by
  unfold DFP.TwoLeg.CenterCancellation.canceledFullCenterDisplacement
  simp [Matrix.mulVec]
  ring

/-- The canceled low full-center coordinate has the displayed exact scalar formula. -/
private theorem canceledFullCenter_low_eq (ε : ℝ) :
    DFP.TwoLeg.CenterCancellation.canceledFullCenterDisplacement
        (ε, slowP ε, slowH ε) 0 = slowCanceledFullLow ε := by
  rw [canceledFullCenter_split, secondTransport_eq, firstFrame_transport_low]
  simp [slowCanceledFullLow, slowCenterCoefficient,
    DFP.TwoLeg.CenterCancellation.firstDisplacement, slowB]
  ring

/-- The canceled high full-center coordinate has the displayed exact scalar formula. -/
private theorem canceledFullCenter_high_eq (ε : ℝ) :
    DFP.TwoLeg.CenterCancellation.canceledFullCenterDisplacement
        (ε, slowP ε, slowH ε) 1 = slowCanceledFullHigh ε := by
  rw [canceledFullCenter_split, secondTransport_eq, firstFrame_transport_high]
  simp [slowCanceledFullHigh, slowCenterCoefficient,
    DFP.TwoLeg.CenterCancellation.firstDisplacement, slowB]
  ring

/-- The removable first-frame off-diagonal factor is known deeply enough for
the order-nine high-center cancellation. -/
private theorem slowOffDiagFactor_germ :
    EqModPow 7 slowOffDiagFactor
      (fun ε : ℝ ↦ 1 - 4 * ε ^ 3 - 3 * ε ^ 4 - (248 / 5) * ε ^ 6) := by
  let one : ℝ → ℝ := fun _ ↦ 1
  let CP : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + 3 * ε ^ 6
  let invBP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 - ε ^ 4 + 4 * ε ^ 6
  let numB : ℝ → ℝ := fun ε ↦
    slowH ε * slowP ε * ε ^ 3 * (1 + ε) * (1 + ε ^ 3)
  let termBP : ℝ → ℝ := fun ε ↦
    2 * ε ^ 3 + 2 * ε ^ 4 + (268 / 5) * ε ^ 6
  let bP : ℝ → ℝ := fun ε ↦
    1 - 4 * ε ^ 3 - 3 * ε ^ 4 - (248 / 5) * ε ^ 6
  have hBCont : ContinuousAt slowB 0 := by
    unfold slowB
    fun_prop
  have hCCont : ContinuousAt slowC 0 := by
    unfold slowC slowP
    fun_prop
  have hCPCont : ContinuousAt CP 0 := by fun_prop
  have hinvBPCont : ContinuousAt invBP 0 := by fun_prop
  have htermBPCont : ContinuousAt termBP 0 := by fun_prop
  have hBZero : slowB 0 ≠ 0 := by norm_num [slowB]
  have hCZero : slowC 0 ≠ 0 := by norm_num [slowC, slowP]
  have hC : EqModPow 7 slowC CP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(9 * ε ^ 5 - 180 * ε ^ 4 - 387 * ε ^ 3 - 198 * ε ^ 2 -
          10 * ε - 20) / 5)
    · fun_prop
    · intro ε
      dsimp only [slowC, slowP, CP]
      ring
  have hInvBPoly : EqModPow 7 one (fun ε ↦ slowB ε * invBP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -4 * ε ^ 3 - 8 * ε ^ 2 + ε + 4)
    · fun_prop
    · intro ε
      dsimp only [one, slowB, invBP]
      ring
  have hInvB : EqModPow 7 (fun ε ↦ 1 / slowB ε) invBP := by
    exact EqModPow.div_approx (EqModPow.refl 7 one) (EqModPow.refl 7 slowB)
      hInvBPoly hBCont hinvBPCont hBCont hBZero
  have htermBPoly : EqModPow 7 numB (fun ε ↦ CP ε * termBP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(72 * ε ^ 7 - 1512 * ε ^ 6 - 780 * ε ^ 5 + 81 * ε ^ 4 -
          1751 * ε ^ 3 - 1296 * ε ^ 2 + 9 * ε - 259) / 5)
    · fun_prop
    · intro ε
      dsimp only [numB, CP, termBP, slowH, slowP]
      ring
  have htermB : EqModPow 7 (fun ε ↦ numB ε / slowC ε) termBP := by
    exact EqModPow.div_approx (EqModPow.refl 7 numB) hC htermBPoly
      hCPCont htermBPCont hCCont hCZero
  apply EqModPow.congr (hInvB.sub htermB)
  · intro ε
    rfl
  · intro ε
    dsimp only [invBP, termBP, bP]
    ring

/-- The common first-displacement coefficient has its order-seven slow-graph germ. -/
private theorem slowCenterCoefficient_germ :
    EqModPow 7 slowCenterCoefficient
      (fun ε : ℝ ↦
        2 + (112 / 5) * ε ^ 3 - (16 / 5) * ε ^ 4 - (224 / 5) * ε ^ 6) := by
  let numerator : ℝ → ℝ := fun ε ↦ 2 * (slowP ε + 1)
  let denominator : ℝ → ℝ := fun ε ↦ 3 * slowB ε
  let cP : ℝ → ℝ := fun ε ↦
    2 + (112 / 5) * ε ^ 3 - (16 / 5) * ε ^ 4 - (224 / 5) * ε ^ 6
  have hpoly : EqModPow 7 numerator (fun ε ↦ denominator ε * cP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ 48 * (14 * ε ^ 3 + 28 * ε ^ 2 + ε - 5) / 5)
    · fun_prop
    · intro ε
      dsimp only [numerator, denominator, cP, slowP, slowB]
      ring
  have hdenCont : ContinuousAt denominator 0 := by
    dsimp only [denominator, slowB]
    fun_prop
  have hdenZero : denominator 0 ≠ 0 := by norm_num [denominator, slowB]
  apply EqModPow.congr
    (EqModPow.div_approx (EqModPow.refl 7 numerator)
      (EqModPow.refl 7 denominator) hpoly hdenCont (by fun_prop)
      hdenCont hdenZero)
  · intro ε
    rfl
  · intro ε
    rfl

/-- The two scalar transport factors have the order-eight germs needed by both
center coordinates. -/
private theorem slowTransport_germs :
    EqModPow 8 slowTransportLow
      (fun ε : ℝ ↦
        -1 + (5 / 2) * ε ^ 4 - (116 / 5) * ε ^ 6 + (226 / 5) * ε ^ 7) ∧
    EqModPow 8 slowTransportHighFactor
      (fun ε : ℝ ↦
        -1 - (76 / 5) * ε ^ 3 + (11 / 10) * ε ^ 4 - 110 * ε ^ 6 +
          (173 / 5) * ε ^ 7) := by
  let LP : ℝ → ℝ := fun ε ↦
    2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4 + 418 * ε ^ 6 +
      (128 / 5) * ε ^ 7
  let HP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 + 6 * ε ^ 6 + 2 * ε ^ 7
  let QP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 - (112 / 5) * ε ^ 6 -
      (157 / 5) * ε ^ 7
  let UP : ℝ → ℝ := fun ε ↦
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4 - (278 / 5) * ε ^ 6 -
      (9 / 5) * ε ^ 7
  let lqP : ℝ → ℝ := fun ε ↦ LP ε * QP ε
  let huP : ℝ → ℝ := fun ε ↦ HP ε * UP ε
  let betaRawP : ℝ → ℝ := fun ε ↦
    ε ^ 4 * (lqP ε) ^ 2 - 4 * ε ^ 3 * lqP ε * huP ε + (huP ε) ^ 2
  let betaP : ℝ → ℝ := fun ε ↦
    1 + (52 / 5) * ε ^ 3 + (9 / 5) * ε ^ 4 - (8884 / 25) * ε ^ 6 +
      (5874 / 25) * ε ^ 7
  let deltaRawP : ℝ → ℝ := fun ε ↦
    QP ε * lqP ε + UP ε * huP ε
  let deltaP : ℝ → ℝ := fun ε ↦
    3 + 72 * ε ^ 3 - 12 * ε ^ 4 + (1836 / 25) * ε ^ 6 -
      (10016 / 25) * ε ^ 7
  let num0P : ℝ → ℝ := fun ε ↦ 2 * deltaP ε * ε ^ 3 * huP ε
  let num1P : ℝ → ℝ := fun ε ↦ 2 * deltaP ε * ε ^ 3 * lqP ε
  let denP : ℝ → ℝ := fun ε ↦ 3 * betaP ε
  let term0P : ℝ → ℝ := fun ε ↦
    2 * ε ^ 3 + (228 / 5) * ε ^ 6 - (69 / 5) * ε ^ 7
  let term1P : ℝ → ℝ := fun ε ↦
    4 * ε ^ 3 + (828 / 5) * ε ^ 6 - (164 / 5) * ε ^ 7
  let t0P : ℝ → ℝ := fun ε ↦
    -1 + (5 / 2) * ε ^ 4 - (116 / 5) * ε ^ 6 + (226 / 5) * ε ^ 7
  let t1P : ℝ → ℝ := fun ε ↦
    -1 - (76 / 5) * ε ^ 3 + (11 / 10) * ε ^ 4 - 110 * ε ^ 6 +
      (173 / 5) * ε ^ 7
  rcases DFP.TwoLeg.slowGraphFirstLegFactorGerms with
    ⟨hLRaw, hHRaw, hQRaw, hURaw⟩
  have hL : EqModPow 8 slowL LP := by
    exact EqModPow.congr hLRaw (fun _ => rfl) (fun _ => rfl)
  have hH : EqModPow 8 slowHigh HP := by
    exact EqModPow.congr hHRaw (fun _ => rfl) (fun _ => rfl)
  have hQ : EqModPow 8 slowQ QP := by
    exact EqModPow.congr hQRaw (fun _ => rfl) (fun _ => rfl)
  have hU : EqModPow 8 slowU UP := by
    exact EqModPow.congr hURaw (fun _ => rfl) (fun _ => rfl)
  let path : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, slowP ε, slowH ε)
  have hpathCont : ContinuousAt path 0 := by
    dsimp only [path, slowP, slowH]
    fun_prop
  have hfactorCont : ContinuousAt
      (fun ε : ℝ ↦ DFP.FirstLeg.factors ε (slowP ε) (slowH ε)) 0 := by
    have hpathZero : path 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      norm_num [path, slowP, slowH]
    have hall := DFP.FirstLeg.factorsAnalytic.continuousAt
    rw [← hpathZero] at hall
    have hcomp := hall.comp (f := path) hpathCont
    simpa only [Function.comp_def, path] using hcomp
  have hLCont : ContinuousAt slowL 0 := by
    change ContinuousAt (fun ε ↦ (DFP.FirstLeg.spectralFactors ε (slowP ε) (slowH ε)).1) 0
    simpa only [DFP.FirstLeg.factors] using hfactorCont.fst.fst
  have hHCont : ContinuousAt slowHigh 0 := by
    change ContinuousAt (fun ε ↦ (DFP.FirstLeg.spectralFactors ε (slowP ε) (slowH ε)).2) 0
    simpa only [DFP.FirstLeg.factors] using hfactorCont.fst.snd
  have hQCont : ContinuousAt slowQ 0 := by
    change ContinuousAt (fun ε ↦ (DFP.FirstLeg.gradientFactors ε (slowP ε) (slowH ε)).1) 0
    simpa only [DFP.FirstLeg.factors] using hfactorCont.snd.fst.fst
  have hUCont : ContinuousAt slowU 0 := by
    change ContinuousAt (fun ε ↦ (DFP.FirstLeg.gradientFactors ε (slowP ε) (slowH ε)).2) 0
    simpa only [DFP.FirstLeg.factors] using hfactorCont.snd.fst.snd
  have hLPCont : ContinuousAt LP 0 := by fun_prop
  have hHPCont : ContinuousAt HP 0 := by fun_prop
  have hQPCont : ContinuousAt QP 0 := by fun_prop
  have hUPCont : ContinuousAt UP 0 := by fun_prop
  have hLQ : EqModPow 8 slowLQ lqP := by
    exact EqModPow.congr (hL.mul hQ hLPCont hQCont) (fun _ => rfl) (fun _ => rfl)
  have hHU : EqModPow 8 slowHU huP := by
    exact EqModPow.congr (hH.mul hU hHPCont hUCont) (fun _ => rfl) (fun _ => rfl)
  have hLQCont : ContinuousAt slowLQ 0 := by
    change ContinuousAt (fun ε ↦ slowL ε * slowQ ε) 0
    exact hLCont.mul hQCont
  have hHUCont : ContinuousAt slowHU 0 := by
    change ContinuousAt (fun ε ↦ slowHigh ε * slowU ε) 0
    exact hHCont.mul hUCont
  have hlqPCont : ContinuousAt lqP 0 := by fun_prop
  have hhuPCont : ContinuousAt huP 0 := by fun_prop
  have hLQSq := hLQ.mul hLQ hlqPCont hLQCont
  have hHUSq := hHU.mul hHU hhuPCont hHUCont
  have hLQHU := hLQ.mul hHU hlqPCont hHUCont
  have hpow4 : EqModPow 8 (fun ε : ℝ ↦ ε ^ 4) (fun ε ↦ ε ^ 4) :=
    EqModPow.refl 8 _
  have hpow3 : EqModPow 8 (fun ε : ℝ ↦ ε ^ 3) (fun ε ↦ ε ^ 3) :=
    EqModPow.refl 8 _
  have htermA := hpow4.mul hLQSq (by fun_prop) (hLQCont.mul hLQCont)
  have htermB0 := hpow3.mul hLQHU (by fun_prop) (hLQCont.mul hHUCont)
  have htermB := EqModPow.const_mul_left 4 htermB0
  have hbetaRaw : EqModPow 8 slowBeta betaRawP := by
    apply EqModPow.congr ((htermA.sub htermB).add hHUSq)
    · intro ε
      dsimp only [slowBeta, betaRawP]
      ring
    · intro ε
      dsimp only [betaRawP]
      ring
  have hbetaPoly : EqModPow 8 betaRawP betaP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (1615396864 * ε ^ 24 + 55028635648 * ε ^ 23 +
          505290582224 * ε ^ 22 + 621866973376 * ε ^ 21 +
          178791083200 * ε ^ 20 + 184014479792 * ε ^ 19 +
          287848817844 * ε ^ 18 + 117361185808 * ε ^ 17 +
          44330795812 * ε ^ 16 + 23774384404 * ε ^ 15 -
          4384093456 * ε ^ 14 + 464270840 * ε ^ 13 -
          5350882555 * ε ^ 12 - 5895919740 * ε ^ 11 -
          640431140 * ε ^ 10 - 1158426960 * ε ^ 9 -
          298190720 * ε ^ 8 + 307802880 * ε ^ 7 -
          89048100 * ε ^ 6 + 91842800 * ε ^ 5 +
          54357400 * ε ^ 4 - 3272400 * ε ^ 3 +
          13743000 * ε ^ 2 - 8635200 * ε - 44975) / 2500)
    · fun_prop
    · intro ε
      dsimp only [betaRawP, betaP, lqP, huP, LP, QP, HP, UP]
      ring
  have hbeta : EqModPow 8 slowBeta betaP := hbetaRaw.trans hbetaPoly
  have hQLQ := hQ.mul hLQ hQPCont hLQCont
  have hUHU := hU.mul hHU hUPCont hHUCont
  have hdeltaRaw : EqModPow 8 slowDelta deltaRawP := by
    exact EqModPow.congr (hQLQ.add hUHU) (fun _ => rfl) (fun _ => rfl)
  have hdeltaPoly : EqModPow 8 deltaRawP deltaP := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (12623528 * ε ^ 13 + 224281536 * ε ^ 12 +
          304118848 * ε ^ 11 + 116254076 * ε ^ 10 +
          65467200 * ε ^ 9 + 91576112 * ε ^ 8 +
          26948078 * ε ^ 7 + 6291780 * ε ^ 6 -
          3113680 * ε ^ 5 - 2520895 * ε ^ 4 +
          272540 * ε ^ 3 - 2351080 * ε ^ 2 - 2532000 * ε + 6355) / 500)
    · fun_prop
    · intro ε
      dsimp only [deltaRawP, deltaP, lqP, huP, LP, QP, HP, UP]
      ring
  have hdelta : EqModPow 8 slowDelta deltaP := hdeltaRaw.trans hdeltaPoly
  have hbetaCont : ContinuousAt slowBeta 0 := by
    exact (((continuousAt_id.pow 4).mul (hLQCont.pow 2)).sub
      ((((continuousAt_const.mul (continuousAt_id.pow 3)).mul hLQCont).mul
        hHUCont))).add (hHUCont.pow 2)
  have hdeltaCont : ContinuousAt slowDelta 0 := hQCont.mul hLQCont |>.add (hUCont.mul hHUCont)
  have hbetaPCont : ContinuousAt betaP 0 := by fun_prop
  have hdeltaPCont : ContinuousAt deltaP 0 := by fun_prop
  have hbetaZero : slowBeta 0 ≠ 0 := by
    have hzero := EqModPow.eq_at_zero_of_pos (by norm_num) hbeta
    rw [hzero]
    norm_num [betaP]
  let num0 : ℝ → ℝ := fun ε ↦ 2 * slowDelta ε * ε ^ 3 * slowHU ε
  let num1 : ℝ → ℝ := fun ε ↦ 2 * slowDelta ε * ε ^ 3 * slowLQ ε
  let den : ℝ → ℝ := fun ε ↦ 3 * slowBeta ε
  have htwoDelta := EqModPow.const_mul_left 2 hdelta
  have hnum0 : EqModPow 8 num0 num0P := by
    have hraw := (htwoDelta.mul hpow3 (by fun_prop) (by fun_prop)).mul hHU
      (by fun_prop) hHUCont
    apply EqModPow.congr hraw <;> intro ε <;>
      simp only [num0, num0P, huP]
  have hnum1 : EqModPow 8 num1 num1P := by
    have hraw := (htwoDelta.mul hpow3 (by fun_prop) (by fun_prop)).mul hLQ
      (by fun_prop) hLQCont
    apply EqModPow.congr hraw <;> intro ε <;>
      simp only [num1, num1P, lqP]
  have hden : EqModPow 8 den denP := by
    simpa only [den, denP] using EqModPow.const_mul_left 3 hbeta
  have hterm0Poly : EqModPow 8 num0P (fun ε ↦ denP ε * term0P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ ε *
        (360576 * ε ^ 15 + 12153424 * ε ^ 14 + 31173456 * ε ^ 13 -
          5893744 * ε ^ 12 - 1682296 * ε ^ 11 - 18707560 * ε ^ 10 -
          2722776 * ε ^ 9 - 340884 * ε ^ 8 + 6978084 * ε ^ 7 +
          1639080 * ε ^ 6 + 1317244 * ε ^ 5 - 6524722 * ε ^ 4 +
          5083368 * ε ^ 3 + 12615 * ε ^ 2 - 298940 * ε + 218640) / 125)
    · fun_prop
    · intro ε
      dsimp only [num0P, denP, term0P, deltaP, betaP, huP, HP, UP]
      ring
  have hterm1Poly : EqModPow 8 num1P (fun ε ↦ denP ε * term1P ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ ε *
        (402563072 * ε ^ 15 + 6786486400 * ε ^ 14 +
          3431555408 * ε ^ 13 - 812287936 * ε ^ 12 +
          1615119992 * ε ^ 11 - 278013384 * ε ^ 10 -
          1040684872 * ε ^ 9 + 128645580 * ε ^ 8 -
          430628180 * ε ^ 7 - 207180900 * ε ^ 6 +
          19344330 * ε ^ 5 - 154844290 * ε ^ 4 +
          130161960 * ε ^ 3 + 180825 * ε ^ 2 - 4648850 * ε + 5576100) / 625)
    · fun_prop
    · intro ε
      dsimp only [num1P, denP, term1P, deltaP, betaP, lqP, LP, QP]
      ring
  have hdenCont : ContinuousAt den 0 := continuousAt_const.mul hbetaCont
  have hdenZero : den 0 ≠ 0 := by norm_num [den, hbetaZero]
  have hterm0 : EqModPow 8 (fun ε ↦ num0 ε / den ε) term0P := by
    exact EqModPow.div_approx hnum0 hden hterm0Poly (by fun_prop) (by fun_prop)
      hdenCont hdenZero
  have hterm1 : EqModPow 8 (fun ε ↦ num1 ε / den ε) term1P := by
    exact EqModPow.div_approx hnum1 hden hterm1Poly (by fun_prop) (by fun_prop)
      hdenCont hdenZero
  constructor
  · apply EqModPow.congr (hQ.neg.sub hterm0)
    · intro ε
      dsimp only [slowTransportLow, num0, den]
    · intro ε
      dsimp only [QP, term0P, t0P]
      ring
  · apply EqModPow.congr (hU.neg.sub hterm1)
    · intro ε
      dsimp only [slowTransportHighFactor, num1, den]
    · intro ε
      dsimp only [UP, term1P, t1P]
      ring

/-- A positive-order polynomial germ is continuous at the origin whenever its
polynomial representative is. -/
private theorem continuousAt_of_eqModPow {n : ℕ} {f g : ℝ → ℝ}
    (hn : 0 < n) (hfg : EqModPow n f g) (hg : ContinuousAt g 0) :
    ContinuousAt f 0 := by
  have hpow : Tendsto (fun ε : ℝ ↦ ε ^ n) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ n) 0 := by fun_prop
    convert hc.tendsto using 1
    norm_num [zero_pow (Nat.ne_of_gt hn)]
  have hdiff := (EqModPow.to_isBigO hfg).trans_tendsto hpow
  have hsum := hdiff.add hg
  have hzero := EqModPow.eq_at_zero_of_pos hn hfg
  change Tendsto f (𝓝 0) (𝓝 (f 0))
  rw [hzero]
  simpa only [sub_add_cancel, zero_add] using hsum

/-- The first raw-frame off-diagonal entry has an exact removable quadratic
factor. -/
private theorem slowFrameOffDiag_eq (ε : ℝ) :
    slowFrameOffDiag ε = ε ^ 2 * slowOffDiagFactor ε := by
  rfl

/-- The raw first frame and its normalization denominator have the precise germs
needed for the order-nine high-coordinate cancellation. -/
private theorem slowFrame_germs :
    EqModPow 9 slowFrameOffDiag
      (fun ε : ℝ ↦
        ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6 - (248 / 5) * ε ^ 8) ∧
    EqModPow 8 slowFrameHighMinusLow
      (fun ε : ℝ ↦
        1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7) ∧
    EqModPow 8 slowFrameDenom
      (fun ε : ℝ ↦
        1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 + 6 * ε ^ 6 - (273 / 5) * ε ^ 7) := by
  let bP : ℝ → ℝ := fun ε ↦
    1 - 4 * ε ^ 3 - 3 * ε ^ 4 - (248 / 5) * ε ^ 6
  let EP : ℝ → ℝ := fun ε ↦
    ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6 - (248 / 5) * ε ^ 8
  let xP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7
  let denP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 + 6 * ε ^ 6 - (273 / 5) * ε ^ 7
  have hE : EqModPow 9 slowFrameOffDiag EP := by
    have hscaled := EqModPow.mul_pow_left (k := 2) slowOffDiagFactor_germ
    apply EqModPow.congr hscaled
    · intro ε
      exact slowFrameOffDiag_eq ε
    · intro ε
      dsimp only [bP, EP]
      ring
  have hxRaw := DFP.TwoLeg.slowGraphRawFrameGerms.2.1
  have hx : EqModPow 8 slowFrameHighMinusLow xP := by
    apply EqModPow.congr hxRaw
    · intro ε
      rw [DFP.TwoLeg.slowGraphJetPath_apply]
      rfl
    · intro ε
      rfl
  have hEPCont : ContinuousAt EP 0 := by fun_prop
  have hxPCont : ContinuousAt xP 0 := by fun_prop
  have hECont : ContinuousAt slowFrameOffDiag 0 :=
    continuousAt_of_eqModPow (by norm_num) hE hEPCont
  have hxCont : ContinuousAt slowFrameHighMinusLow 0 :=
    continuousAt_of_eqModPow (by norm_num) hx hxPCont
  have hE8 := hE.mono (by norm_num : 8 ≤ 9)
  have hESq := hE8.mul hE8 hEPCont hECont
  have hxSq := hx.mul hx hxPCont hxCont
  let radP : ℝ → ℝ := fun ε ↦ xP ε ^ 2 + EP ε ^ 2
  have hradRaw : EqModPow 8
      (fun ε ↦ slowFrameHighMinusLow ε ^ 2 + slowFrameOffDiag ε ^ 2) radP := by
    apply EqModPow.congr (hxSq.add hESq)
    · intro ε
      ring
    · intro ε
      dsimp only [radP]
      ring
  have hradPoly : EqModPow 8 radP (fun ε ↦ denP ε ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (246016 * ε ^ 8 - 2100 * ε ^ 6 + 43280 * ε ^ 5 + 900 * ε ^ 4 +
          6060 * ε ^ 3 - 10120 * ε ^ 2 - 325) / 100)
    · fun_prop
    · intro ε
      dsimp only [radP, denP, xP, EP]
      ring
  have hradCont : ContinuousAt
      (fun ε ↦ slowFrameHighMinusLow ε ^ 2 + slowFrameOffDiag ε ^ 2) 0 :=
    (hxCont.pow 2).add (hECont.pow 2)
  have hradZero : 0 <
      slowFrameHighMinusLow 0 ^ 2 + slowFrameOffDiag 0 ^ 2 := by
    have hx0 := EqModPow.eq_at_zero_of_pos (by norm_num) hx
    have hE0 := EqModPow.eq_at_zero_of_pos (by norm_num) hE
    rw [hx0, hE0]
    norm_num [xP, EP]
  have hdenPZero : 0 < denP 0 := by norm_num [denP]
  have hden : EqModPow 8 slowFrameDenom denP := by
    have hsqrt := EqModPow.sqrt_of_sq (hradRaw.trans hradPoly) hradCont
      (by fun_prop) hradZero hdenPZero
    apply EqModPow.congr hsqrt
    · intro ε
      rfl
    · intro ε
      rfl
  exact ⟨hE, hx, hden⟩

private def slowCanceledFullHighInner (ε : ℝ) : ℝ :=
  slowP ε - slowCenterCoefficient ε +
    (-slowOffDiagFactor ε * slowTransportLow ε +
      slowFrameHighMinusLow ε * slowTransportHighFactor ε) /
        slowFrameDenom ε

/-- The canceled high coordinate retains an exact outer factor `ε²`. -/
private theorem slowCanceledFullHigh_eq_pow_mul (ε : ℝ) :
    slowCanceledFullHigh ε = ε ^ 2 * slowCanceledFullHighInner ε := by
  unfold slowCanceledFullHigh
  rw [slowFrameOffDiag_eq]
  unfold slowCanceledFullHighInner
  ring

/-- The canceled representative has the two slow-graph center germs, including
the full order-nine high-coordinate cancellation. -/
private theorem slowCanceledFullCenter_germs :
    EqModPow 8 slowCanceledFullLow
      (fun ε : ℝ ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7) ∧
    EqModPow 9 slowCanceledFullHigh
      (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) := by
  let bP : ℝ → ℝ := fun ε ↦
    1 - 4 * ε ^ 3 - 3 * ε ^ 4 - (248 / 5) * ε ^ 6
  let EP : ℝ → ℝ := fun ε ↦
    ε ^ 2 - 4 * ε ^ 5 - 3 * ε ^ 6 - (248 / 5) * ε ^ 8
  let xP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 3 * ε ^ 4 + 6 * ε ^ 6 - (258 / 5) * ε ^ 7
  let denP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 + 6 * ε ^ 6 - (273 / 5) * ε ^ 7
  let t0P : ℝ → ℝ := fun ε ↦
    -1 + (5 / 2) * ε ^ 4 - (116 / 5) * ε ^ 6 + (226 / 5) * ε ^ 7
  let t1P : ℝ → ℝ := fun ε ↦
    -1 - (76 / 5) * ε ^ 3 + (11 / 10) * ε ^ 4 - 110 * ε ^ 6 +
      (173 / 5) * ε ^ 7
  let cP : ℝ → ℝ := fun ε ↦
    2 + (112 / 5) * ε ^ 3 - (16 / 5) * ε ^ 4 - (224 / 5) * ε ^ 6
  let lowFrameP : ℝ → ℝ := fun ε ↦
    -1 + 2 * ε ^ 4 - (116 / 5) * ε ^ 6 + 30 * ε ^ 7
  let highFrameP : ℝ → ℝ := fun ε ↦
    -(86 / 5) * ε ^ 3 - (7 / 5) * ε ^ 4 - (732 / 5) * ε ^ 6
  rcases slowTransport_germs with ⟨ht0, ht1⟩
  rcases slowFrame_germs with ⟨hE9, hx, hden⟩
  have hb := slowOffDiagFactor_germ
  have hc := slowCenterCoefficient_germ
  have hEPCont : ContinuousAt EP 0 := by fun_prop
  have hxPCont : ContinuousAt xP 0 := by fun_prop
  have hdenPCont : ContinuousAt denP 0 := by fun_prop
  have ht0PCont : ContinuousAt t0P 0 := by fun_prop
  have ht1PCont : ContinuousAt t1P 0 := by fun_prop
  have hbPCont : ContinuousAt bP 0 := by fun_prop
  have hcPCont : ContinuousAt cP 0 := by fun_prop
  have hECont : ContinuousAt slowFrameOffDiag 0 :=
    continuousAt_of_eqModPow (by norm_num) hE9 hEPCont
  have hxCont : ContinuousAt slowFrameHighMinusLow 0 :=
    continuousAt_of_eqModPow (by norm_num) hx hxPCont
  have hdenCont : ContinuousAt slowFrameDenom 0 :=
    continuousAt_of_eqModPow (by norm_num) hden hdenPCont
  have ht0Cont : ContinuousAt slowTransportLow 0 :=
    continuousAt_of_eqModPow (by norm_num) ht0 ht0PCont
  have ht1Cont : ContinuousAt slowTransportHighFactor 0 :=
    continuousAt_of_eqModPow (by norm_num) ht1 ht1PCont
  have hbCont : ContinuousAt slowOffDiagFactor 0 :=
    continuousAt_of_eqModPow (by norm_num) hb hbPCont
  have hdenZero : slowFrameDenom 0 ≠ 0 := by
    have hzero := EqModPow.eq_at_zero_of_pos (by norm_num) hden
    rw [hzero]
    norm_num [denP]
  have hpow2 : EqModPow 8 (fun ε : ℝ ↦ ε ^ 2) (fun ε ↦ ε ^ 2) :=
    EqModPow.refl 8 _
  have hE8 := hE9.mono (by norm_num : 8 ≤ 9)
  have hEpow2 := hE8.mul hpow2 hEPCont (by fun_prop)
  have hxT0 := hx.mul ht0 hxPCont ht0Cont
  have hEpow2T1 := hEpow2.mul ht1 (by fun_prop) ht1Cont
  let lowNumP : ℝ → ℝ := fun ε ↦ xP ε * t0P ε + EP ε * ε ^ 2 * t1P ε
  have hlowNum : EqModPow 8
      (fun ε ↦ slowFrameHighMinusLow ε * slowTransportLow ε +
        slowFrameOffDiag ε * ε ^ 2 * slowTransportHighFactor ε) lowNumP := by
    apply EqModPow.congr (hxT0.add hEpow2T1)
    · intro ε
      ring
    · intro ε
      dsimp only [lowNumP]
  have hlowPoly : EqModPow 8 lowNumP (fun ε ↦ denP ε * lowFrameP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(85808 * ε ^ 9 - 272800 * ε ^ 8 + 5190 * ε ^ 7 +
          27864 * ε ^ 6 - 60776 * ε ^ 5 + 165 * ε ^ 4 + 230 * ε ^ 3 +
          770 * ε ^ 2 - 80) / 50)
    · fun_prop
    · intro ε
      dsimp only [lowNumP, denP, lowFrameP, xP, EP, t0P, t1P]
      ring
  have hlowFrame : EqModPow 8
      (fun ε ↦
        (slowFrameHighMinusLow ε * slowTransportLow ε +
          slowFrameOffDiag ε * ε ^ 2 * slowTransportHighFactor ε) /
            slowFrameDenom ε) lowFrameP :=
    EqModPow.div_approx hlowNum hden hlowPoly hdenPCont (by fun_prop)
      hdenCont hdenZero
  have hce4High := EqModPow.mul_pow_left (k := 4) hc
  have hce4 := hce4High.mono (by norm_num : 8 ≤ 7 + 4)
  have hone : EqModPow 8 (fun _ : ℝ ↦ (1 : ℝ)) (fun _ ↦ 1) := EqModPow.refl 8 _
  let lowRawP : ℝ → ℝ := fun ε ↦ 1 - ε ^ 4 * cP ε + lowFrameP ε
  have hlowRaw : EqModPow 8 slowCanceledFullLow lowRawP := by
    have hsum := (hone.sub hce4).add hlowFrame
    apply EqModPow.congr hsum
    · intro ε
      dsimp only [slowCanceledFullLow]
      ring
    · intro ε
      dsimp only [lowRawP]
  let lowP : ℝ → ℝ := fun ε ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7
  have hlowPolyFinal : EqModPow 8 lowRawP lowP := by
    apply EqModPow.of_factor (q := fun ε : ℝ ↦ 16 * (14 * ε ^ 2 + 1) / 5)
    · fun_prop
    · intro ε
      dsimp only [lowRawP, lowP, cP, lowFrameP]
      ring
  have hlow : EqModPow 8 slowCanceledFullLow lowP := hlowRaw.trans hlowPolyFinal
  have hb7 := hb
  have hx7 := hx.mono (by norm_num : 7 ≤ 8)
  have hden7 := hden.mono (by norm_num : 7 ≤ 8)
  have ht07 := ht0.mono (by norm_num : 7 ≤ 8)
  have ht17 := ht1.mono (by norm_num : 7 ≤ 8)
  have hnegBT0 := hb7.neg.mul ht07 (by fun_prop) ht0Cont
  have hxT1 := hx7.mul ht17 hxPCont ht1Cont
  let highNumP : ℝ → ℝ := fun ε ↦ -bP ε * t0P ε + xP ε * t1P ε
  have hhighNum : EqModPow 7
      (fun ε ↦ -slowOffDiagFactor ε * slowTransportLow ε +
        slowFrameHighMinusLow ε * slowTransportHighFactor ε) highNumP := by
    apply EqModPow.congr (hnegBT0.add hxT1)
    · intro ε
      ring
    · intro ε
      dsimp only [highNumP]
  have hhighPoly : EqModPow 7 highNumP (fun ε ↦ denP ε * highFrameP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(89268 * ε ^ 7 - 6604 * ε ^ 6 + 46616 * ε ^ 5 + 5070 * ε ^ 4 +
          490 * ε ^ 3 + 7680 * ε ^ 2 - 35 * ε - 2430) / 50)
    · fun_prop
    · intro ε
      dsimp only [highNumP, denP, highFrameP, bP, xP, t0P, t1P]
      ring
  have hhighFrame : EqModPow 7
      (fun ε ↦
        (-slowOffDiagFactor ε * slowTransportLow ε +
          slowFrameHighMinusLow ε * slowTransportHighFactor ε) /
            slowFrameDenom ε) highFrameP :=
    EqModPow.div_approx hhighNum hden7 hhighPoly hdenPCont (by fun_prop)
      hdenCont hdenZero
  have hp : EqModPow 7 slowP slowP := EqModPow.refl 7 _
  let highInnerP : ℝ → ℝ := fun ε ↦ -(508 / 5) * ε ^ 6
  have hinner : EqModPow 7 slowCanceledFullHighInner highInnerP := by
    apply EqModPow.congr ((hp.sub hc).add hhighFrame)
    · intro ε
      rfl
    · intro ε
      dsimp only [slowP, cP, highFrameP, highInnerP]
      ring
  have hscaled := EqModPow.mul_pow_left (k := 2) hinner
  have hhigh : EqModPow 9 slowCanceledFullHigh
      (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) := by
    apply EqModPow.congr hscaled
    · intro ε
      exact slowCanceledFullHigh_eq_pow_mul ε
    · intro ε
      dsimp only [highInnerP]
      ring
  exact ⟨hlow, hhigh⟩

/-- Along the polynomial slow graph, the observable full-center displacement
agrees near zero with the canceled representative in either coordinate. -/
private theorem slowGraphFullCenter_eventuallyEq_canceled (i : Fin 2) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).fullCenterDisplacement i) =ᶠ[𝓝 0]
      (fun ε ↦ DFP.TwoLeg.CenterCancellation.canceledFullCenterDisplacement
        (ε, slowP ε, slowH ε) i) := by
  have hpathCont : ContinuousAt DFP.TwoLeg.slowGraphJetPath 0 := by
    have hpoly : ContinuousAt
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    apply hpoly.congr_of_eventuallyEq
    filter_upwards [] with ε
    exact DFP.TwoLeg.slowGraphJetPath_apply ε
  have hpathZero : DFP.TwoLeg.slowGraphJetPath 0 =
      ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  have hpathTendsto : Tendsto DFP.TwoLeg.slowGraphJetPath (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    rw [← hpathZero]
    exact hpathCont
  have hbridge := hpathTendsto.eventually
    (DFP.TwoLeg.CenterCancellation.fullCenterDisplacement_eventuallyEq_canceled i)
  filter_upwards [hbridge] with ε hε
  simpa only [DFP.TwoLeg.slowGraphJetPath_apply, slowP, slowH] using hε

/-- Along the polynomial slow graph, the low coordinate of the normalized
full-center displacement equals `-(116/5) ε⁶ + (38/5) ε⁷` up to `O(ε⁸)`. -/
theorem slowGraphFullCenterLowRemainder :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).fullCenterDisplacement 0 -
        (-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hbridge := slowGraphFullCenter_eventuallyEq_canceled 0
  refine (EqModPow.to_isBigO slowCanceledFullCenter_germs.1).congr' ?_
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [hbridge] with ε hε
  rw [hε, canceledFullCenter_low_eq]

/-- Along the polynomial slow graph, the high coordinate of the normalized
full-center displacement equals `-(508/5) ε⁸` up to `O(ε⁹)`. -/
theorem slowGraphFullCenterHighRemainder :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).fullCenterDisplacement 1 -
        (-(508 / 5) * ε ^ 8)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 9) := by
  have hbridge := slowGraphFullCenter_eventuallyEq_canceled 1
  refine (EqModPow.to_isBigO slowCanceledFullCenter_germs.2).congr' ?_
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [hbridge] with ε hε
  rw [hε, canceledFullCenter_high_eq]

end DFP.TwoLeg.CenterJet
