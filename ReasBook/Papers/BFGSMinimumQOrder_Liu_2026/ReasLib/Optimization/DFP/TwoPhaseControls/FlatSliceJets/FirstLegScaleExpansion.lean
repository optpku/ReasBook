module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
public section

noncomputable section
open Filter
open scoped Topology
namespace DFP.TwoLeg
private theorem eqModPow_congr_of_eq {n : ℕ} {f g f' g' : ℝ → ℝ}
    (h : EqModPow n f g) (hf : ∀ ε, f' ε = f ε) (hg : ∀ ε, g' ε = g ε) :
    EqModPow n f' g' := by
  exact EqModPow.congr h hf hg
private theorem eqModPow_of_eq (n : ℕ) {f g : ℝ → ℝ}
    (h : ∀ ε, f ε = g ε) : EqModPow n f g :=
  eqModPow_congr_of_eq (EqModPow.refl n f) (fun _ => rfl) (fun ε => (h ε).symm)
private theorem eqModPow_div_approx {n : ℕ}
    {num den numP denP q : ℝ → ℝ}
    (hnum : EqModPow n num numP) (hden : EqModPow n den denP)
    (hpoly : EqModPow n numP (fun ε => denP ε * q ε))
    (hdenP : ContinuousAt denP 0) (hq : ContinuousAt q 0)
    (hdenCont : ContinuousAt den 0) (hden0 : den 0 ≠ 0) :
    EqModPow n (fun ε => num ε / den ε) q := by
  have hdenMul : EqModPow n (fun ε => den ε * q ε)
      (fun ε => denP ε * q ε) :=
    hden.mul (EqModPow.refl n q) hdenP hq
  exact EqModPow.div_of_eq_mul
    (hnum.trans (hpoly.trans hdenMul.symm)) hdenCont hden0
-- Local declaration justification (notation): This file-local notation abbreviates repeated
-- first-leg `EqModPow 5` expressions and does not alter inference.
local infix:50 " =₅ " => EqModPow 5
/-- Order-five germs of the four removable first-leg factors on the pure scale axis. -/
theorem firstLeg_scale_factor_expansions :
    (fun ε : ℝ => (DFP.FirstLeg.spectralFactors ε 2 1).1) =₅
        (fun ε => 2 + 4 * ε ^ 3 + 2 * ε ^ 4) ∧
    (fun ε : ℝ => (DFP.FirstLeg.spectralFactors ε 2 1).2) =₅
        (fun ε => 1 - 2 * ε ^ 3) ∧
    (fun ε : ℝ => (DFP.FirstLeg.gradientFactors ε 2 1).1) =₅
        (fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4) ∧
    (fun ε : ℝ => (DFP.FirstLeg.gradientFactors ε 2 1).2) =₅
        (fun ε => 1 - 2 * ε ^ 3 - (1 / 2) * ε ^ 4) := by
  let one : ℝ → ℝ := fun _ => 1
  let two : ℝ → ℝ := fun _ => 2
  let three : ℝ → ℝ := fun _ => 3
  let zero : ℝ → ℝ := fun _ => 0
  let B : ℝ → ℝ := fun ε => 1 + 2 * ε ^ 3 + ε ^ 4
  let C : ℝ → ℝ := fun ε => (1 + ε ^ 3) ^ 2 + 2 * ε ^ 6 * (1 + ε) ^ 2
  let iB : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - ε ^ 4
  have hBcont : ContinuousAt B 0 := by fun_prop
  have hCcont : ContinuousAt C 0 := by fun_prop
  have hB0 : B 0 ≠ 0 := by norm_num [B]
  have hC0 : C 0 ≠ 0 := by norm_num [C]
  have hiBmul : (fun ε => B ε * iB ε) =₅ one := by
    apply EqModPow.of_factor (q := fun ε => -ε * (ε + 2) ^ 2)
    · fun_prop
    · intro ε
      simp [B, iB, one]
      ring
  have hiB : (fun ε => 1 / B ε) =₅ iB := by
    simpa only [one_div] using
      (EqModPow.inv_of_mul_eq_one hiBmul hBcont hB0)
  let sixTerm : ℝ → ℝ := fun ε => 4 * ε ^ 6 * (1 + ε) ^ 2
  have hsixDiv : (fun ε => sixTerm ε / C ε) =₅ zero := by
    apply EqModPow.div_of_eq_mul _ hCcont hC0
    apply EqModPow.of_factor (q := fun ε => 4 * ε * (ε + 1) ^ 2)
    · fun_prop
    · intro ε
      simp [sixTerm, C, zero]
      ring
  let squareTerm : ℝ → ℝ := fun ε => (1 + ε ^ 3) ^ 2
  have hsquareDiv : (fun ε => squareTerm ε / C ε) =₅ one := by
    apply EqModPow.div_of_eq_mul _ hCcont hC0
    apply EqModPow.of_factor (q := fun ε => -2 * ε * (ε + 1) ^ 2)
    · fun_prop
    · intro ε
      simp [squareTerm, C, one]
      ring
  let bRatioNum : ℝ → ℝ := fun ε => 2 * ε ^ 3 * (1 + ε) * (1 + ε ^ 3)
  let bRatioP : ℝ → ℝ := fun ε => 2 * ε ^ 3 + 2 * ε ^ 4
  have hbRatio : (fun ε => bRatioNum ε / C ε) =₅ bRatioP := by
    apply EqModPow.div_of_eq_mul _ hCcont hC0
    apply EqModPow.of_factor
      (q := fun ε => -2 * ε * (ε + 1) ^ 2 *
        (2 * ε ^ 4 + 2 * ε ^ 3 + ε ^ 2 - ε + 1))
    · fun_prop
    · intro ε
      simp [bRatioNum, C, bRatioP]
      ring
  let qRatioNum : ℝ → ℝ := fun ε => 6 * ε ^ 3 * (1 + ε)
  let threeB : ℝ → ℝ := fun ε => 3 * B ε
  let qRatioP : ℝ → ℝ := fun ε => 2 * ε ^ 3 + 2 * ε ^ 4
  have hthreeBcont : ContinuousAt threeB 0 := by fun_prop
  have hthreeB0 : threeB 0 ≠ 0 := by norm_num [threeB, B]
  have hqRatio : (fun ε => qRatioNum ε / threeB ε) =₅ qRatioP := by
    apply EqModPow.div_of_eq_mul _ hthreeBcont hthreeB0
    apply EqModPow.of_factor (q := fun ε => -6 * ε * (ε + 1) * (ε + 2))
    · fun_prop
    · intro ε
      simp [qRatioNum, threeB, B, qRatioP]
      ring
  let vRatioNum : ℝ → ℝ := fun ε => 6 * (1 + ε ^ 3)
  let vRatioP : ℝ → ℝ := fun ε => 2 - 2 * ε ^ 3 - 2 * ε ^ 4
  have hvRatio : (fun ε => vRatioNum ε / threeB ε) =₅ vRatioP := by
    apply EqModPow.div_of_eq_mul _ hthreeBcont hthreeB0
    apply EqModPow.of_factor (q := fun ε => 6 * ε * (ε + 1) * (ε + 2))
    · fun_prop
    · intro ε
      simp [vRatioNum, threeB, B, vRatioP]
      ring
  let a : ℝ → ℝ := fun ε => 2 - sixTerm ε / C ε + 1 / B ε
  let b : ℝ → ℝ := fun ε => 1 / B ε - bRatioNum ε / C ε
  let d : ℝ → ℝ := fun ε => 1 - squareTerm ε / C ε + 1 / B ε
  let q : ℝ → ℝ := fun ε => 1 - qRatioNum ε / threeB ε
  let v : ℝ → ℝ := fun ε => 2 - vRatioNum ε / threeB ε
  let aP : ℝ → ℝ := fun ε => 3 - 2 * ε ^ 3 - ε ^ 4
  let bP : ℝ → ℝ := fun ε => 1 - 4 * ε ^ 3 - 3 * ε ^ 4
  let dP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - ε ^ 4
  let qP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - 2 * ε ^ 4
  let vP : ℝ → ℝ := fun ε => 2 * ε ^ 3 + 2 * ε ^ 4
  have ha : a =₅ aP := by
    apply eqModPow_congr_of_eq
      (((EqModPow.refl 5 two).sub hsixDiv).add hiB)
    · intro ε
      rfl
    · intro ε
      simp [two, zero, iB, aP]
      ring
  have hb : b =₅ bP := by
    apply eqModPow_congr_of_eq (hiB.sub hbRatio)
    · intro ε
      rfl
    · intro ε
      simp [iB, bRatioP, bP]
      ring
  have hd : d =₅ dP := by
    apply eqModPow_congr_of_eq
      (((EqModPow.refl 5 one).sub hsquareDiv).add hiB)
    · intro ε
      rfl
    · intro ε
      simp [one, iB, dP]
  have hq : q =₅ qP := by
    apply eqModPow_congr_of_eq ((EqModPow.refl 5 one).sub hqRatio)
    · intro ε
      rfl
    · intro ε
      simp [one, qRatioP, qP]
      ring
  have hv : v =₅ vP := by
    apply eqModPow_congr_of_eq ((EqModPow.refl 5 two).sub hvRatio)
    · intro ε
      rfl
    · intro ε
      simp [two, vRatioP, vP]
      ring
  have hacont : ContinuousAt a 0 := by
    dsimp [a, sixTerm, C, B]
    fun_prop
  have hbcont : ContinuousAt b 0 := by
    dsimp [b, bRatioNum, C, B]
    fun_prop
  have hdcont : ContinuousAt d 0 := by
    dsimp [d, squareTerm, C, B]
    fun_prop
  have hqcont : ContinuousAt q 0 := by
    dsimp [q, qRatioNum, threeB, B]
    fun_prop
  have hvcont : ContinuousAt v 0 := by
    dsimp [v, vRatioNum, threeB, B]
    fun_prop
  let x4 : ℝ → ℝ := fun ε => ε ^ 4
  let x2 : ℝ → ℝ := fun ε => ε ^ 2
  let A : ℝ → ℝ := fun ε => x4 ε * a ε
  let E : ℝ → ℝ := fun ε => x2 ε * b ε
  let AP : ℝ → ℝ := fun ε => 3 * ε ^ 4
  let EP : ℝ → ℝ := fun ε => ε ^ 2
  have hAraw : A =₅ (fun ε => x4 ε * aP ε) := by
    exact (EqModPow.refl 5 x4).mul ha (by fun_prop) hacont
  have hAtrunc : (fun ε => x4 ε * aP ε) =₅ AP := by
    apply EqModPow.of_factor (q := fun ε => -ε ^ 2 * (ε + 2))
    · fun_prop
    · intro ε
      simp [x4, aP, AP]
      ring
  have hA : A =₅ AP := hAraw.trans hAtrunc
  have hEraw : E =₅ (fun ε => x2 ε * bP ε) := by
    exact (EqModPow.refl 5 x2).mul hb (by fun_prop) hbcont
  have hEtrunc : (fun ε => x2 ε * bP ε) =₅ EP := by
    apply EqModPow.of_factor (q := fun ε => -3 * ε - 4)
    · fun_prop
    · intro ε
      simp [x2, bP, EP]
      ring
  have hE : E =₅ EP := hEraw.trans hEtrunc
  have hAcont : ContinuousAt A 0 := by fun_prop
  have hEcont : ContinuousAt E 0 := by fun_prop
  let rad : ℝ → ℝ := fun ε => (d ε - A ε) ^ 2 + 4 * E ε ^ 2
  let gapP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - 2 * ε ^ 4
  have hdA := hd.sub hA
  have hdAsq := hdA.mul hdA (by fun_prop) (hdcont.sub hAcont)
  have hEsq := hE.mul hE (by fun_prop) hEcont
  have hfourEsq := (EqModPow.refl 5 (fun _ : ℝ => 4)).mul hEsq
    (by fun_prop) (hEcont.mul hEcont)
  have hradRaw : rad =₅
      (fun ε => (dP ε - AP ε) ^ 2 + 4 * EP ε ^ 2) := by
    apply eqModPow_congr_of_eq (hdAsq.add hfourEsq)
    · intro ε
      simp [rad]
      ring
    · intro ε
      ring
  have hradPoly :
      (fun ε => (dP ε - AP ε) ^ 2 + 4 * EP ε ^ 2) =₅
        (fun ε => gapP ε ^ 2) := by
    apply EqModPow.of_factor (q := fun ε => 4 * ε ^ 2 * (3 * ε + 2))
    · fun_prop
    · intro ε
      simp [dP, AP, EP, gapP]
      ring
  have hrad : rad =₅ (fun ε => gapP ε ^ 2) := hradRaw.trans hradPoly
  have hradcont : ContinuousAt rad 0 := by fun_prop
  have hgapPcont : ContinuousAt gapP 0 := by fun_prop
  have hgap : (fun ε => Real.sqrt (rad ε)) =₅ gapP := by
    apply EqModPow.sqrt_of_sq hrad hradcont hgapPcont
    · norm_num [rad, d, A, E, x4, x2, a, sixTerm, C, B, b,
        bRatioNum]
    · norm_num [gapP]
  let gap : ℝ → ℝ := fun ε => Real.sqrt (rad ε)
  let high : ℝ → ℝ := fun ε => (A ε + d ε + gap ε) / 2
  let low : ℝ → ℝ := fun ε => (A ε + d ε - gap ε) / 2
  let highP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3
  let lowP : ℝ → ℝ := fun ε => 2 * ε ^ 4
  have hgap' : gap =₅ gapP := hgap
  have hhighNum : (fun ε => A ε + d ε + gap ε) =₅
      (fun ε => AP ε + dP ε + gapP ε) := hA.add hd |>.add hgap'
  have hhighPoly : (fun ε => AP ε + dP ε + gapP ε) =₅
      (fun ε => 2 * highP ε) :=
    eqModPow_of_eq 5 (fun ε => by simp [AP, dP, gapP, highP]; ring)
  have htwoRefl : two =₅ two := EqModPow.refl 5 two
  have hhigh : high =₅ highP := by
    have hdiv := eqModPow_div_approx hhighNum htwoRefl hhighPoly
      (by fun_prop) (by fun_prop) (by fun_prop) (by norm_num [two])
    exact eqModPow_congr_of_eq hdiv (fun ε => by simp [high, two])
      (fun _ => rfl)
  have hlowNum : (fun ε => A ε + d ε - gap ε) =₅
      (fun ε => AP ε + dP ε - gapP ε) := (hA.add hd).sub hgap'
  have hlowPoly : (fun ε => AP ε + dP ε - gapP ε) =₅
      (fun ε => 2 * lowP ε) :=
    eqModPow_of_eq 5 (fun ε => by simp [AP, dP, gapP, lowP]; ring)
  have hlow : low =₅ lowP := by
    have hdiv := eqModPow_div_approx hlowNum htwoRefl hlowPoly
      (by fun_prop) (by fun_prop) (by fun_prop) (by norm_num [two])
    exact eqModPow_congr_of_eq hdiv (fun ε => by simp [low, two])
      (fun _ => rfl)
  have hgapcont : ContinuousAt gap 0 := hradcont.sqrt
  have hhighcont : ContinuousAt high 0 := by fun_prop
  have hlowcont : ContinuousAt low 0 := by fun_prop
  let denomRad : ℝ → ℝ := fun ε => (d ε - low ε) ^ 2 + E ε ^ 2
  let denomP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  have hdlow := hd.sub hlow
  have hdlowSq := hdlow.mul hdlow (by fun_prop) (hdcont.sub hlowcont)
  have hdenomRadRaw : denomRad =₅
      (fun ε => (dP ε - lowP ε) ^ 2 + EP ε ^ 2) := by
    apply eqModPow_congr_of_eq (hdlowSq.add hEsq)
    · intro ε
      simp [denomRad]
      ring
    · intro ε
      ring
  have hdenomRadPoly :
      (fun ε => (dP ε - lowP ε) ^ 2 + EP ε ^ 2) =₅
        (fun ε => denomP ε ^ 2) := by
    apply EqModPow.of_factor (q := fun ε => ε ^ 2 * (11 * ε + 8) / 4)
    · fun_prop
    · intro ε
      simp [dP, lowP, EP, denomP]
      ring
  have hdenomRad : denomRad =₅ (fun ε => denomP ε ^ 2) :=
    hdenomRadRaw.trans hdenomRadPoly
  have hdenomRadcont : ContinuousAt denomRad 0 := by fun_prop
  have hdenomPcont : ContinuousAt denomP 0 := by fun_prop
  let denom : ℝ → ℝ := fun ε => Real.sqrt (denomRad ε)
  have hdenom : denom =₅ denomP := by
    apply EqModPow.sqrt_of_sq hdenomRad hdenomRadcont hdenomPcont
    · norm_num [denomRad, d, low, A, E, gap, rad, x4, x2, a,
        sixTerm, C, B, b, bRatioNum]
    · norm_num [denomP]
  have hdenomcont : ContinuousAt denom 0 := hdenomRadcont.sqrt
  let LP : ℝ → ℝ := fun ε => 2 + 4 * ε ^ 3 + 2 * ε ^ 4
  have had := ha.mul hd (by fun_prop) hdcont
  have hbb := hb.mul hb (by fun_prop) hbcont
  have hLnum : (fun ε => a ε * d ε - b ε ^ 2) =₅
      (fun ε => aP ε * dP ε - bP ε ^ 2) := by
    apply eqModPow_congr_of_eq (had.sub hbb)
    · intro ε
      ring
    · intro ε
      ring
  have hLpoly : (fun ε => aP ε * dP ε - bP ε ^ 2) =₅
      (fun ε => highP ε * LP ε) := by
    apply EqModPow.of_factor (q := fun ε => -4 * ε * (2 * ε ^ 2 + 4 * ε + 1))
    · fun_prop
    · intro ε
      simp [aP, bP, dP, highP, LP]
      ring
  have hL : (fun ε => (a ε * d ε - b ε ^ 2) / high ε) =₅ LP :=
    eqModPow_div_approx hLnum hhigh hLpoly (by fun_prop) (by fun_prop)
      hhighcont (by norm_num [high, A, d, gap, rad, E, a, b, x4,
        x2, sixTerm, C, B, bRatioNum])
  let QP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  have hdq := (hd.sub hlow).mul hq (by fun_prop) hqcont
  have hbv := hb.mul hv (by fun_prop) hvcont
  have hx4bv := (EqModPow.refl 5 x4).mul hbv (by fun_prop)
    (hbcont.mul hvcont)
  have hQnum :
      (fun ε => (d ε - low ε) * q ε - x4 ε * b ε * v ε) =₅
        (fun ε => (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε) := by
    apply eqModPow_congr_of_eq (hdq.sub hx4bv)
    · intro ε
      simp [x4]
      ring
    · intro ε
      simp [x4]
      ring
  have hQpoly :
      (fun ε => (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε) =₅
        (fun ε => denomP ε * QP ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε ^ 2 *
        (24 * ε ^ 5 + 56 * ε ^ 4 + 32 * ε ^ 3 - 9 * ε - 8) / 4)
    · fun_prop
    · intro ε
      simp [dP, lowP, qP, bP, vP, denomP, QP]
      ring
  have hQ :
      (fun ε => ((d ε - low ε) * q ε - x4 ε * b ε * v ε) / denom ε) =₅ QP :=
    eqModPow_div_approx hQnum hdenom hQpoly (by fun_prop) (by fun_prop)
      hdenomcont (by norm_num [denom, denomRad, d, low, A, E, gap,
        rad, x4, x2, a, sixTerm, C, B, b, bRatioNum])
  let UP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (1 / 2) * ε ^ 4
  have hbq := hb.mul hq (by fun_prop) hqcont
  have hdlowv := (hd.sub hlow).mul hv (by fun_prop) hvcont
  have hUnum : (fun ε => b ε * q ε + (d ε - low ε) * v ε) =₅
      (fun ε => bP ε * qP ε + (dP ε - lowP ε) * vP ε) :=
    hbq.add hdlowv
  have hUpoly :
      (fun ε => bP ε * qP ε + (dP ε - lowP ε) * vP ε) =₅
        (fun ε => denomP ε * UP ε) := by
    apply EqModPow.of_factor (q := fun ε => -ε ^ 2 * (5 * ε + 8) / 4)
    · fun_prop
    · intro ε
      simp [bP, qP, dP, lowP, vP, denomP, UP]
      ring
  have hU :
      (fun ε => (b ε * q ε + (d ε - low ε) * v ε) / denom ε) =₅ UP :=
    eqModPow_div_approx hUnum hdenom hUpoly (by fun_prop) (by fun_prop)
      hdenomcont (by norm_num [denom, denomRad, d, low, A, E, gap,
        rad, x4, x2, a, sixTerm, C, B, b, bRatioNum])
  have hhighFormula : ∀ ε,
      RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) = high ε := by
    intro ε
    rfl
  have hlowFormula : ∀ ε,
      RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε) = low ε := by
    intro ε
    rfl
  have hdenomFormula : ∀ ε,
      RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) = denom ε := by
    intro ε
    rfl
  have hspectralLRaw : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε 2 1).1 =
        (a ε * d ε - b ε ^ 2) /
          RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    simp only [DFP.FirstLeg.spectralFactors]
    norm_num [a, b, d, x4, x2, sixTerm, squareTerm, bRatioNum, B, C]
  have hspectralHRaw : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε 2 1).2 =
        RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    simp only [DFP.FirstLeg.spectralFactors]
    norm_num [a, b, d, x4, x2, sixTerm, squareTerm, bRatioNum, B, C]
  have hgradientQRaw : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε 2 1).1 =
        ((d ε - RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε)) * q ε -
          x4 ε * b ε * v ε) /
            RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    simp only [DFP.FirstLeg.gradientFactors]
    norm_num [a, b, d, q, v, x4, x2, sixTerm, squareTerm, bRatioNum,
      qRatioNum, vRatioNum, threeB, B, C]
  have hgradientURaw : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε 2 1).2 =
        (b ε * q ε +
          (d ε - RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε)) * v ε) /
            RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    simp only [DFP.FirstLeg.gradientFactors]
    norm_num [a, b, d, q, v, x4, x2, sixTerm, squareTerm, bRatioNum,
      qRatioNum, vRatioNum, threeB, B, C]
  have hspectralL : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε 2 1).1 =
        (a ε * d ε - b ε ^ 2) / high ε := by
    intro ε
    rw [hspectralLRaw ε, hhighFormula ε]
  have hspectralH : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε 2 1).2 = high ε := by
    intro ε
    rw [hspectralHRaw ε, hhighFormula ε]
  have hgradientQ : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε 2 1).1 =
        ((d ε - low ε) * q ε - x4 ε * b ε * v ε) / denom ε := by
    intro ε
    rw [hgradientQRaw ε, hlowFormula ε, hdenomFormula ε]
  have hgradientU : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε 2 1).2 =
        (b ε * q ε + (d ε - low ε) * v ε) / denom ε := by
    intro ε
    rw [hgradientURaw ε, hlowFormula ε, hdenomFormula ε]
  exact ⟨eqModPow_congr_of_eq hL hspectralL (fun _ => rfl),
    eqModPow_congr_of_eq hhigh hspectralH (fun _ => rfl),
    eqModPow_congr_of_eq hQ hgradientQ (fun _ => rfl),
    eqModPow_congr_of_eq hU hgradientU (fun _ => rfl)⟩
end DFP.TwoLeg
