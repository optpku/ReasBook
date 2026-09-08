module

public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondReduction
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.QuotientGerm

public section

noncomputable section

open Filter
open Asymptotics
open scoped Topology

namespace DFP.TwoLeg.EndpointAngleJet

local infix:50 " =₅ " => DFP.TwoLeg.EqModPow 5

set_option maxHeartbeats 2000000 in
-- The explicit rational and square-root germ normalization creates large ring terms.
private theorem slowFirstLeg_factor_expansions :
    (fun ε : ℝ =>
      let x := DFP.TwoLeg.slowGraphJetPath ε
      (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1) =₅
        (fun ε => 2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4) ∧
    (fun ε : ℝ =>
      let x := DFP.TwoLeg.slowGraphJetPath ε
      (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2) =₅
        (fun ε => 1 - 2 * ε ^ 3) ∧
    (fun ε : ℝ =>
      let x := DFP.TwoLeg.slowGraphJetPath ε
      (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1) =₅
        (fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4) ∧
    (fun ε : ℝ =>
      let x := DFP.TwoLeg.slowGraphJetPath ε
      (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2) =₅
        (fun ε => 1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4) := by
  let one : ℝ → ℝ := fun _ => 1
  let two : ℝ → ℝ := fun _ => 2
  let p : ℝ → ℝ := fun ε =>
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3
  let B : ℝ → ℝ := fun ε => 1 + 2 * ε ^ 3 + ε ^ 4
  let C : ℝ → ℝ := fun ε =>
    (1 + ε ^ 3) ^ 2 + p ε * ε ^ 6 * (1 + ε) ^ 2
  let iB : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - ε ^ 4
  have hBcont : ContinuousAt B 0 := by fun_prop
  have hCcont : ContinuousAt C 0 := by
    dsimp [C, p]
    fun_prop
  have hB0 : B 0 ≠ 0 := by norm_num [B]
  have hC0 : C 0 ≠ 0 := by norm_num [C, p]
  have hiBmul : DFP.TwoLeg.EqModPow 5 (fun ε => B ε * iB ε) one := by
    apply DFP.TwoLeg.EqModPow.of_factor (q := fun ε => -ε * (ε + 2) ^ 2)
    · fun_prop
    · intro ε
      simp [B, iB, one]
      ring
  have hiB : DFP.TwoLeg.EqModPow 5 (fun ε => 1 / B ε) iB := by
    simpa only [one_div] using
      (DFP.TwoLeg.EqModPow.inv_of_mul_eq_one hiBmul hBcont hB0)
  let hpP : ℝ → ℝ := fun ε =>
    2 + (278 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  have hp : DFP.TwoLeg.EqModPow 5 (fun ε => h ε * p ε) hpP := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -(72 / 5) * ε * (ε - 22))
    · fun_prop
    · intro ε
      simp [h, p, hpP]
      ring
  let sixTerm : ℝ → ℝ := fun ε =>
    h ε * p ε ^ 2 * ε ^ 6 * (1 + ε) ^ 2
  have hsixDiv : DFP.TwoLeg.EqModPow 5
      (fun ε => sixTerm ε / C ε) (fun _ => 0) := by
    apply DFP.TwoLeg.EqModPow.div_of_eq_mul _ hCcont hC0
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => h ε * p ε ^ 2 * ε * (1 + ε) ^ 2)
    · dsimp [h, p]
      fun_prop
    · intro ε
      simp [sixTerm]
      ring
  let squareTerm : ℝ → ℝ := fun ε => h ε * (1 + ε ^ 3) ^ 2
  have hsquareDiv : DFP.TwoLeg.EqModPow 5
      (fun ε => squareTerm ε / C ε) h := by
    apply DFP.TwoLeg.EqModPow.div_of_eq_mul _ hCcont hC0
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -(h ε * p ε * ε * (1 + ε) ^ 2))
    · dsimp [h, p]
      fun_prop
    · intro ε
      simp [squareTerm, C]
      ring
  let bRatioNum : ℝ → ℝ := fun ε =>
    h ε * p ε * ε ^ 3 * (1 + ε) * (1 + ε ^ 3)
  let bRatioP : ℝ → ℝ := fun ε => 2 * ε ^ 3 + 2 * ε ^ 4
  let rb : ℝ → ℝ := fun ε =>
    ε * (ε + 1) ^ 2 *
      (18 * ε ^ 8 - 378 * ε ^ 7 - 468 * ε ^ 6 + 1656 * ε ^ 5 -
        1676 * ε ^ 4 + 1555 * ε ^ 3 + 277 * ε ^ 2 - 277 * ε + 268) / 5
  have hbRatio : DFP.TwoLeg.EqModPow 5
      (fun ε => bRatioNum ε / C ε) bRatioP := by
    apply DFP.TwoLeg.EqModPow.div_of_eq_mul _ hCcont hC0
    apply DFP.TwoLeg.EqModPow.of_factor (q := rb)
    · dsimp [rb]
      fun_prop
    · intro ε
      simp [bRatioNum, C, bRatioP, rb, h, p]
      ring
  let qRatioNum : ℝ → ℝ := fun ε =>
    2 * (p ε + 1) * ε ^ 3 * (1 + ε)
  let threeB : ℝ → ℝ := fun ε => 3 * B ε
  let qRatioP : ℝ → ℝ := fun ε => 2 * ε ^ 3 + 2 * ε ^ 4
  have hthreeBcont : ContinuousAt threeB 0 := by fun_prop
  have hthreeB0 : threeB 0 ≠ 0 := by norm_num [threeB, B]
  have hqRatio : DFP.TwoLeg.EqModPow 5
      (fun ε => qRatioNum ε / threeB ε) qRatioP := by
    apply DFP.TwoLeg.EqModPow.div_of_eq_mul _ hthreeBcont hthreeB0
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -(48 / 5) * ε * (ε - 7) * (ε + 1))
    · fun_prop
    · intro ε
      simp [qRatioNum, threeB, B, qRatioP, p]
      ring
  let vRatioNum : ℝ → ℝ := fun ε =>
    2 * (p ε + 1) * (1 + ε ^ 3)
  let vRatioP : ℝ → ℝ := fun ε =>
    2 + (122 / 5) * ε ^ 3 - (16 / 5) * ε ^ 4
  have hvRatio : DFP.TwoLeg.EqModPow 5
      (fun ε => vRatioNum ε / threeB ε) vRatioP := by
    apply DFP.TwoLeg.EqModPow.div_of_eq_mul _ hthreeBcont hthreeB0
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => (48 / 5) * ε * (ε - 7) * (ε + 1))
    · fun_prop
    · intro ε
      simp [vRatioNum, threeB, B, vRatioP, p]
      ring
  let a : ℝ → ℝ := fun ε =>
    h ε * p ε - sixTerm ε / C ε + 1 / B ε
  let b : ℝ → ℝ := fun ε => 1 / B ε - bRatioNum ε / C ε
  let d : ℝ → ℝ := fun ε => h ε - squareTerm ε / C ε + 1 / B ε
  let q : ℝ → ℝ := fun ε => 1 - qRatioNum ε / threeB ε
  let v : ℝ → ℝ := fun ε => p ε - vRatioNum ε / threeB ε
  let aP : ℝ → ℝ := fun ε =>
    3 + (268 / 5) * ε ^ 3 - (14 / 5) * ε ^ 4
  let bP : ℝ → ℝ := fun ε => 1 - 4 * ε ^ 3 - 3 * ε ^ 4
  let dP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - ε ^ 4
  let qP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - 2 * ε ^ 4
  let vP : ℝ → ℝ := fun ε => (76 / 5) * ε ^ 3 + (7 / 5) * ε ^ 4
  have ha : a =₅ aP := by
    apply DFP.TwoLeg.EqModPow.congr ((hp.sub hsixDiv).add hiB)
    · intro ε
      rfl
    · intro ε
      simp [hpP, iB, aP]
      ring
  have hb : b =₅ bP := by
    apply DFP.TwoLeg.EqModPow.congr (hiB.sub hbRatio)
    · intro ε
      rfl
    · intro ε
      simp [iB, bRatioP, bP]
      ring
  have hd : d =₅ dP := by
    apply DFP.TwoLeg.EqModPow.congr
      (((DFP.TwoLeg.EqModPow.refl 5 h).sub hsquareDiv).add hiB)
    · intro ε
      rfl
    · intro ε
      simp [iB, dP]
  have hq : q =₅ qP := by
    apply DFP.TwoLeg.EqModPow.congr
      ((DFP.TwoLeg.EqModPow.refl 5 one).sub hqRatio)
    · intro ε
      rfl
    · intro ε
      simp [one, qRatioP, qP]
      ring
  have hv : v =₅ vP := by
    apply DFP.TwoLeg.EqModPow.congr
      ((DFP.TwoLeg.EqModPow.refl 5 p).sub hvRatio)
    · intro ε
      rfl
    · intro ε
      simp [p, vRatioP, vP]
      ring
  have hacont : ContinuousAt a 0 := by
    dsimp [a, sixTerm, C, B, h, p]
    fun_prop (disch := norm_num)
  have hbcont : ContinuousAt b 0 := by
    dsimp [b, bRatioNum, C, B, h, p]
    fun_prop (disch := norm_num)
  have hdcont : ContinuousAt d 0 := by
    dsimp [d, squareTerm, C, B, h, p]
    fun_prop (disch := norm_num)
  have hqcont : ContinuousAt q 0 := by
    dsimp [q, qRatioNum, threeB, B, p]
    fun_prop (disch := norm_num)
  have hvcont : ContinuousAt v 0 := by
    dsimp [v, vRatioNum, threeB, B, p]
    fun_prop (disch := norm_num)
  let x4 : ℝ → ℝ := fun ε => ε ^ 4
  let x2 : ℝ → ℝ := fun ε => ε ^ 2
  let A : ℝ → ℝ := fun ε => x4 ε * a ε
  let E : ℝ → ℝ := fun ε => x2 ε * b ε
  let AP : ℝ → ℝ := fun ε => 3 * ε ^ 4
  let EP : ℝ → ℝ := fun ε => ε ^ 2
  have hAraw : A =₅ (fun ε => x4 ε * aP ε) :=
    (DFP.TwoLeg.EqModPow.refl 5 x4).mul ha (by fun_prop) hacont
  have hAtrunc : (fun ε => x4 ε * aP ε) =₅ AP := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -(2 / 5) * ε ^ 2 * (7 * ε - 134))
    · fun_prop
    · intro ε
      simp [x4, aP, AP]
      ring
  have hA : A =₅ AP := hAraw.trans hAtrunc
  have hEraw : E =₅ (fun ε => x2 ε * bP ε) :=
    (DFP.TwoLeg.EqModPow.refl 5 x2).mul hb (by fun_prop) hbcont
  have hEtrunc : (fun ε => x2 ε * bP ε) =₅ EP := by
    apply DFP.TwoLeg.EqModPow.of_factor (q := fun ε => -3 * ε - 4)
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
  have hfourEsq :=
    (DFP.TwoLeg.EqModPow.refl 5 (fun _ : ℝ => 4)).mul hEsq
      (by fun_prop) (hEcont.mul hEcont)
  have hradRaw : rad =₅
      (fun ε => (dP ε - AP ε) ^ 2 + 4 * EP ε ^ 2) := by
    apply DFP.TwoLeg.EqModPow.congr (hdAsq.add hfourEsq)
    · intro ε
      simp [rad]
      ring
    · intro ε
      ring
  have hradPoly :
      (fun ε => (dP ε - AP ε) ^ 2 + 4 * EP ε ^ 2) =₅
        (fun ε => gapP ε ^ 2) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => 4 * ε ^ 2 * (3 * ε + 2))
    · fun_prop
    · intro ε
      simp [dP, AP, EP, gapP]
      ring
  have hrad : rad =₅ (fun ε => gapP ε ^ 2) := hradRaw.trans hradPoly
  have hradcont : ContinuousAt rad 0 := by fun_prop
  have hgapPcont : ContinuousAt gapP 0 := by fun_prop
  have hgap : DFP.TwoLeg.EqModPow 5 (fun ε => Real.sqrt (rad ε)) gapP := by
    apply DFP.TwoLeg.EqModPow.sqrt_of_sq hrad hradcont hgapPcont
    · norm_num [rad, d, A, E, x4, x2, a, sixTerm, C, B, b,
        bRatioNum, h, p]
    · norm_num [gapP]
  let gap : ℝ → ℝ := fun ε => Real.sqrt (rad ε)
  let high : ℝ → ℝ := fun ε => (A ε + d ε + gap ε) / 2
  let low : ℝ → ℝ := fun ε => (A ε + d ε - gap ε) / 2
  let highP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3
  let lowP : ℝ → ℝ := fun ε => 2 * ε ^ 4
  have hhighNum : DFP.TwoLeg.EqModPow 5
      (fun ε => A ε + d ε + gap ε)
      (fun ε => AP ε + dP ε + gapP ε) := (hA.add hd).add hgap
  have hhighPoly : DFP.TwoLeg.EqModPow 5
      (fun ε => AP ε + dP ε + gapP ε)
      (fun ε => 2 * highP ε) :=
    DFP.TwoLeg.EqModPow.of_eq 5 (fun ε => by
      simp [AP, dP, gapP, highP]
      ring)
  have htwoRefl : DFP.TwoLeg.EqModPow 5 two two :=
    DFP.TwoLeg.EqModPow.refl 5 two
  have hhigh : high =₅ highP := by
    have hdiv := DFP.TwoLeg.EqModPow.div_approx hhighNum htwoRefl hhighPoly
      (by fun_prop) (by fun_prop) (by fun_prop) (by norm_num [two])
    exact DFP.TwoLeg.EqModPow.congr hdiv
      (fun ε => by simp [high, two]) (fun _ => rfl)
  have hlowNum : DFP.TwoLeg.EqModPow 5
      (fun ε => A ε + d ε - gap ε)
      (fun ε => AP ε + dP ε - gapP ε) := (hA.add hd).sub hgap
  have hlowPoly : DFP.TwoLeg.EqModPow 5
      (fun ε => AP ε + dP ε - gapP ε)
      (fun ε => 2 * lowP ε) :=
    DFP.TwoLeg.EqModPow.of_eq 5 (fun ε => by
      simp [AP, dP, gapP, lowP]
      ring)
  have hlow : low =₅ lowP := by
    have hdiv := DFP.TwoLeg.EqModPow.div_approx hlowNum htwoRefl hlowPoly
      (by fun_prop) (by fun_prop) (by fun_prop) (by norm_num [two])
    exact DFP.TwoLeg.EqModPow.congr hdiv
      (fun ε => by simp [low, two]) (fun _ => rfl)
  have hgapcont : ContinuousAt gap 0 := hradcont.sqrt
  have hhighcont : ContinuousAt high 0 := by fun_prop
  have hlowcont : ContinuousAt low 0 := by fun_prop
  let denomRad : ℝ → ℝ := fun ε => (d ε - low ε) ^ 2 + E ε ^ 2
  let denomP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  have hdlow := hd.sub hlow
  have hdlowSq := hdlow.mul hdlow (by fun_prop) (hdcont.sub hlowcont)
  have hdenomRadRaw : denomRad =₅
      (fun ε => (dP ε - lowP ε) ^ 2 + EP ε ^ 2) := by
    apply DFP.TwoLeg.EqModPow.congr (hdlowSq.add hEsq)
    · intro ε
      simp [denomRad]
      ring
    · intro ε
      ring
  have hdenomRadPoly : DFP.TwoLeg.EqModPow 5
      (fun ε => (dP ε - lowP ε) ^ 2 + EP ε ^ 2)
      (fun ε => denomP ε ^ 2) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => ε ^ 2 * (11 * ε + 8) / 4)
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
    apply DFP.TwoLeg.EqModPow.sqrt_of_sq hdenomRad hdenomRadcont hdenomPcont
    · norm_num [denomRad, d, low, A, E, gap, rad, x4, x2, a,
        sixTerm, C, B, b, bRatioNum, h, p]
    · norm_num [denomP]
  have hdenomcont : ContinuousAt denom 0 := hdenomRadcont.sqrt
  let LP : ℝ → ℝ := fun ε =>
    2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4
  have had := ha.mul hd (by fun_prop) hdcont
  have hbb := hb.mul hb (by fun_prop) hbcont
  have hLnum : DFP.TwoLeg.EqModPow 5
      (fun ε => a ε * d ε - b ε ^ 2)
      (fun ε => aP ε * dP ε - bP ε ^ 2) := by
    apply DFP.TwoLeg.EqModPow.congr (had.sub hbb)
    · intro ε
      ring
    · intro ε
      ring
  have hLpoly : DFP.TwoLeg.EqModPow 5
      (fun ε => aP ε * dP ε - bP ε ^ 2)
      (fun ε => highP ε * LP ε) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -ε * (31 * ε ^ 2 + 358 * ε + 20) / 5)
    · fun_prop
    · intro ε
      simp [aP, bP, dP, highP, LP]
      ring
  have hL : DFP.TwoLeg.EqModPow 5
      (fun ε => (a ε * d ε - b ε ^ 2) / high ε) LP :=
    DFP.TwoLeg.EqModPow.div_approx hLnum hhigh hLpoly
      (by fun_prop) (by fun_prop) hhighcont
      (by norm_num [high, A, d, gap, rad, E, a, b, x4,
        x2, sixTerm, C, B, bRatioNum, h, p])
  let QP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  have hdq := (hd.sub hlow).mul hq (by fun_prop) hqcont
  have hbv := hb.mul hv (by fun_prop) hvcont
  have hx4bv := (DFP.TwoLeg.EqModPow.refl 5 x4).mul hbv
    (by fun_prop) (hbcont.mul hvcont)
  have hQnum : DFP.TwoLeg.EqModPow 5
      (fun ε => (d ε - low ε) * q ε - x4 ε * b ε * v ε)
      (fun ε => (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε) := by
    apply DFP.TwoLeg.EqModPow.congr (hdq.sub hx4bv)
    · intro ε
      simp [x4]
      ring
    · intro ε
      simp [x4]
      ring
  have hQpoly : DFP.TwoLeg.EqModPow 5
      (fun ε => (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε)
      (fun ε => denomP ε * QP ε) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => ε ^ 2 *
        (84 * ε ^ 5 + 1024 * ε ^ 4 + 1216 * ε ^ 3 -
          33 * ε - 304) / 20)
    · fun_prop
    · intro ε
      simp [dP, lowP, qP, bP, vP, denomP, QP]
      ring
  have hQ : DFP.TwoLeg.EqModPow 5
      (fun ε => ((d ε - low ε) * q ε - x4 ε * b ε * v ε) / denom ε) QP :=
    DFP.TwoLeg.EqModPow.div_approx hQnum hdenom hQpoly
      (by fun_prop) (by fun_prop) hdenomcont
      (by norm_num [denom, denomRad, d, low, A, E, gap,
        rad, x4, x2, a, sixTerm, C, B, b, bRatioNum, h, p])
  let UP : ℝ → ℝ := fun ε =>
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4
  have hbq := hb.mul hq (by fun_prop) hqcont
  have hdlowv := (hd.sub hlow).mul hv (by fun_prop) hvcont
  have hUnum : DFP.TwoLeg.EqModPow 5
      (fun ε => b ε * q ε + (d ε - low ε) * v ε)
      (fun ε => bP ε * qP ε + (dP ε - lowP ε) * vP ε) :=
    hbq.add hdlowv
  have hUpoly : DFP.TwoLeg.EqModPow 5
      (fun ε => bP ε * qP ε + (dP ε - lowP ε) * vP ε)
      (fun ε => denomP ε * UP ε) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -ε ^ 2 * (19 * ε + 172) / 20)
    · fun_prop
    · intro ε
      simp [bP, qP, dP, lowP, vP, denomP, UP]
      ring
  have hU : DFP.TwoLeg.EqModPow 5
      (fun ε => (b ε * q ε + (d ε - low ε) * v ε) / denom ε) UP :=
    DFP.TwoLeg.EqModPow.div_approx hUnum hdenom hUpoly
      (by fun_prop) (by fun_prop) hdenomcont
      (by norm_num [denom, denomRad, d, low, A, E, gap,
        rad, x4, x2, a, sixTerm, C, B, b, bRatioNum, h, p])
  have hhighFormula : ∀ ε,
      RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) = high ε :=
    fun ε => by
      rw [RealSymmetric2.high_apply, RealSymmetric2.gap_apply]
  have hlowFormula : ∀ ε,
      RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε) = low ε :=
    fun ε => by
      rw [RealSymmetric2.low_apply, RealSymmetric2.gap_apply]
  have hdenomFormula : ∀ ε,
      RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) = denom ε :=
    fun ε => by
      rw [RealSymmetric2.lowDenom_apply, hlowFormula ε]
  have hspectralLRaw : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).1 =
        (a ε * d ε - b ε ^ 2) /
          RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.FirstLeg.spectralFactors_apply]
  have hspectralHRaw : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).2 =
        RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.FirstLeg.spectralFactors_apply]
  have hgradientQRaw : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).1 =
        ((d ε - RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε)) * q ε -
          x4 ε * b ε * v ε) /
            RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.FirstLeg.gradientFactors_apply]
  have hgradientURaw : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).2 =
        (b ε * q ε +
          (d ε - RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε)) * v ε) /
            RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.FirstLeg.gradientFactors_apply]
  have hspectralL : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).1 =
        (a ε * d ε - b ε ^ 2) / high ε := by
    intro ε
    rw [hspectralLRaw ε, hhighFormula ε]
  have hspectralH : ∀ ε,
      (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).2 = high ε := by
    intro ε
    rw [hspectralHRaw ε, hhighFormula ε]
  have hgradientQ : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).1 =
        ((d ε - low ε) * q ε - x4 ε * b ε * v ε) / denom ε := by
    intro ε
    rw [hgradientQRaw ε, hlowFormula ε, hdenomFormula ε]
  have hgradientU : ∀ ε,
      (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).2 =
        (b ε * q ε + (d ε - low ε) * v ε) / denom ε := by
    intro ε
    rw [hgradientURaw ε, hlowFormula ε, hdenomFormula ε]
  have hpath (ε : ℝ) : DFP.TwoLeg.slowGraphJetPath ε = (ε, p ε, h ε) := by
    simpa [p, h] using DFP.TwoLeg.slowGraphJetPath_apply ε
  exact ⟨
    DFP.TwoLeg.EqModPow.congr hL
      (fun ε => by rw [hpath ε]; exact hspectralL ε) (fun _ => rfl),
    DFP.TwoLeg.EqModPow.congr hhigh
      (fun ε => by rw [hpath ε]; exact hspectralH ε) (fun _ => rfl),
    DFP.TwoLeg.EqModPow.congr hQ
      (fun ε => by rw [hpath ε]; exact hgradientQ ε) (fun _ => rfl),
    DFP.TwoLeg.EqModPow.congr hU
      (fun ε => by rw [hpath ε]; exact hgradientU ε) (fun _ => rfl)⟩

local infix:50 " =₇ " => DFP.TwoLeg.EqModPow 7

set_option maxHeartbeats 2000000 in
-- The second-leg quotient germ normalization creates large rational ring terms.
/-- Along the polynomial slow graph, the final second-leg slope agrees through degree six
with its explicitly computed polynomial approximation. -/
theorem slowFinalSlopeRemainder :
    (fun ε : ℝ => slowFinalSlope ε - slowFinalSlopePolynomial ε) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 7) := by
  let p : ℝ → ℝ := fun ε =>
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3
  let path : ℝ → ℝ × ℝ × ℝ := fun ε => (ε, p ε, h ε)
  let L : ℝ → ℝ := fun ε =>
    (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).1
  let H : ℝ → ℝ := fun ε =>
    (DFP.FirstLeg.spectralFactors ε (p ε) (h ε)).2
  let Q : ℝ → ℝ := fun ε =>
    (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).1
  let U : ℝ → ℝ := fun ε =>
    (DFP.FirstLeg.gradientFactors ε (p ε) (h ε)).2
  let LP : ℝ → ℝ := fun ε =>
    2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4
  let HP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3
  let QP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  let UP : ℝ → ℝ := fun ε =>
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4
  rcases slowFirstLeg_factor_expansions with ⟨hLRaw, hHRaw, hQRaw, hURaw⟩
  have hL : L =₅ LP := by
    simpa only [L, LP, p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hLRaw
  have hH : H =₅ HP := by
    simpa only [H, HP, p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hHRaw
  have hQ : Q =₅ QP := by
    simpa only [Q, QP, p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hQRaw
  have hU : U =₅ UP := by
    simpa only [U, UP, p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hURaw
  have hpathCont : ContinuousAt path 0 := by
    dsimp [path, p, h]
    fun_prop
  have hfactorCont : ContinuousAt
      (fun ε : ℝ => DFP.FirstLeg.factors ε (p ε) (h ε)) 0 := by
    have hpathZero : path 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      norm_num [path, p, h]
    have hall := DFP.FirstLeg.factorsAnalytic.continuousAt
    rw [← hpathZero] at hall
    have hcomp := hall.comp (f := path) hpathCont
    simpa only [Function.comp_def, path] using hcomp
  have hLCont : ContinuousAt L 0 := by
    simpa only [L, DFP.FirstLeg.factors_apply] using hfactorCont.fst.fst
  have hHCont : ContinuousAt H 0 := by
    simpa only [H, DFP.FirstLeg.factors_apply] using hfactorCont.fst.snd
  have hQCont : ContinuousAt Q 0 := by
    simpa only [Q, DFP.FirstLeg.factors_apply] using hfactorCont.snd.fst.fst
  have hUCont : ContinuousAt U 0 := by
    simpa only [U, DFP.FirstLeg.factors_apply] using hfactorCont.snd.fst.snd
  have hLPCont : ContinuousAt LP 0 := by fun_prop
  have hHPCont : ContinuousAt HP 0 := by fun_prop
  have hQPCont : ContinuousAt QP 0 := by fun_prop
  have hUPCont : ContinuousAt UP 0 := by fun_prop
  let w1 : ℝ → ℝ := fun ε => ε * L ε * Q ε - 2 * H ε * U ε
  let w2 : ℝ → ℝ := fun ε => H ε * U ε - 2 * ε ^ 3 * L ε * Q ε
  let w1P : ℝ → ℝ := fun ε =>
    -2 + 2 * ε - (92 / 5) * ε ^ 3 + (289 / 5) * ε ^ 4
  let w2P : ℝ → ℝ := fun ε =>
    1 + (26 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4
  have hLQ := hL.mul hQ hLPCont hQCont
  have hHU := hH.mul hU hHPCont hUCont
  have hLQCont : ContinuousAt (fun ε => L ε * Q ε) 0 := hLCont.mul hQCont
  have hHUCont : ContinuousAt (fun ε => H ε * U ε) 0 := hHCont.mul hUCont
  have hId : DFP.TwoLeg.EqModPow 5 (fun ε : ℝ => ε) (fun ε => ε) :=
    DFP.TwoLeg.EqModPow.refl 5 _
  have hIdLQ := hId.mul hLQ continuousAt_id hLQCont
  have hTwo : DFP.TwoLeg.EqModPow 5 (fun _ : ℝ => (2 : ℝ))
      (fun _ => 2) := DFP.TwoLeg.EqModPow.refl 5 _
  have hTwoHU := hTwo.mul hHU continuousAt_const hHUCont
  have hw1Raw : DFP.TwoLeg.EqModPow 5 w1
      (fun ε => ε * (LP ε * QP ε) - 2 * (HP ε * UP ε)) := by
    simpa only [w1, mul_assoc] using hIdLQ.sub hTwoHU
  have hw1Poly : DFP.TwoLeg.EqModPow 5
      (fun ε => ε * (LP ε * QP ε) - 2 * (HP ε * UP ε)) w1P := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε =>
        -(5 * ε ^ 4 + 1494 * ε ^ 3 + 1236 * ε ^ 2 - 448 * ε + 48) / 10)
    · fun_prop
    · intro ε
      simp [LP, QP, HP, UP, w1P]
      ring
  have hw1 : DFP.TwoLeg.EqModPow 5 w1 w1P := hw1Raw.trans hw1Poly
  have hCube : DFP.TwoLeg.EqModPow 5 (fun ε : ℝ => ε ^ 3)
      (fun ε => ε ^ 3) := DFP.TwoLeg.EqModPow.refl 5 _
  have hCubeCont : ContinuousAt (fun ε : ℝ => ε ^ 3) 0 := by fun_prop
  have hCubeLQ := hCube.mul hLQ hCubeCont hLQCont
  have hCubeLQCont : ContinuousAt (fun ε => ε ^ 3 * (L ε * Q ε)) 0 :=
    hCubeCont.mul hLQCont
  have hTwoCubeLQ := hTwo.mul hCubeLQ continuousAt_const hCubeLQCont
  have hw2Raw : DFP.TwoLeg.EqModPow 5 w2
      (fun ε => HP ε * UP ε - 2 * (ε ^ 3 * (LP ε * QP ε))) := by
    simpa only [w2, mul_assoc] using hHU.sub hTwoCubeLQ
  have hw2Poly : DFP.TwoLeg.EqModPow 5
      (fun ε => HP ε * UP ε - 2 * (ε ^ 3 * (LP ε * QP ε))) w2P := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => ε *
        (5 * ε ^ 5 + 1494 * ε ^ 4 + 1192 * ε ^ 3 + 59 * ε - 668) / 5)
    · fun_prop
    · intro ε
      simp [LP, QP, HP, UP, w2P]
      ring
  have hw2 : DFP.TwoLeg.EqModPow 5 w2 w2P := hw2Raw.trans hw2Poly
  have hw1Cont : ContinuousAt w1 0 := by
    dsimp [w1]
    fun_prop
  have hw2Cont : ContinuousAt w2 0 := by
    dsimp [w2]
    fun_prop
  have hw1PCont : ContinuousAt w1P 0 := by fun_prop
  have hw2PCont : ContinuousAt w2P 0 := by fun_prop
  let beta : ℝ → ℝ := fun ε =>
    ε ^ 3 * L ε * Q ε * w1 ε + H ε * U ε * w2 ε
  let delta : ℝ → ℝ := fun ε => L ε * Q ε ^ 2 + H ε * U ε ^ 2
  let betaP : ℝ → ℝ := fun ε =>
    1 + (52 / 5) * ε ^ 3 + (9 / 5) * ε ^ 4
  let deltaP : ℝ → ℝ := fun ε => 3 + 72 * ε ^ 3 - 12 * ε ^ 4
  have hCubeLQw1 := hCubeLQ.mul hw1
    (hCubeCont.mul (hLPCont.mul hQPCont)) hw1Cont
  have hHUw2 := hHU.mul hw2 (hHPCont.mul hUPCont) hw2Cont
  have hbetaRaw : DFP.TwoLeg.EqModPow 5 beta
      (fun ε => ε ^ 3 * (LP ε * QP ε) * w1P ε +
        (HP ε * UP ε) * w2P ε) := by
    simpa only [beta, mul_assoc] using hCubeLQw1.add hHUw2
  have hbetaPoly : DFP.TwoLeg.EqModPow 5
      (fun ε => ε ^ 3 * (LP ε * QP ε) * w1P ε +
        (HP ε * UP ε) * w2P ε) betaP := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -ε *
        (2890 * ε ^ 9 + 862612 * ε ^ 8 + 414080 * ε ^ 7 -
          219228 * ε ^ 6 + 57766 * ε ^ 5 - 339848 * ε ^ 4 +
          90112 * ε ^ 3 + 839 * ε ^ 2 - 22276 * ε + 12256) / 100)
    · fun_prop
    · intro ε
      simp [LP, QP, w1P, HP, UP, w2P, betaP]
      ring
  have hbeta : DFP.TwoLeg.EqModPow 5 beta betaP := hbetaRaw.trans hbetaPoly
  have hQSq := hQ.mul hQ hQPCont hQCont
  have hUSq := hU.mul hU hUPCont hUCont
  have hLQSq := hL.mul hQSq hLPCont (hQCont.mul hQCont)
  have hHUSq := hH.mul hUSq hHPCont (hUCont.mul hUCont)
  have hdeltaRaw : DFP.TwoLeg.EqModPow 5 delta
      (fun ε => LP ε * (QP ε * QP ε) + HP ε * (UP ε * UP ε)) := by
    apply DFP.TwoLeg.EqModPow.congr (hLQSq.add hHUSq)
    · intro ε
      simp [delta]
      ring
    · intro ε
      ring
  have hdeltaPoly : DFP.TwoLeg.EqModPow 5
      (fun ε => LP ε * (QP ε * QP ε) + HP ε * (UP ε * UP ε)) deltaP := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => ε *
        (125 * ε ^ 6 + 37208 * ε ^ 5 + 64608 * ε ^ 4 - 1248 * ε ^ 3 +
          1271 * ε ^ 2 - 29904 * ε - 14976) / 100)
    · fun_prop
    · intro ε
      simp [LP, QP, HP, UP, deltaP]
      ring
  have hdelta : DFP.TwoLeg.EqModPow 5 delta deltaP :=
    hdeltaRaw.trans hdeltaPoly
  have hbetaCont : ContinuousAt beta 0 := by
    dsimp [beta]
    fun_prop
  have hdeltaCont : ContinuousAt delta 0 := by
    dsimp [delta]
    fun_prop
  have hbetaPCont : ContinuousAt betaP 0 := by fun_prop
  have hdeltaPCont : ContinuousAt deltaP 0 := by fun_prop
  let threeBeta : ℝ → ℝ := fun ε => 3 * beta ε
  let threeBetaP : ℝ → ℝ := fun ε => 3 * betaP ε
  have hthree : DFP.TwoLeg.EqModPow 5 (fun _ : ℝ => (3 : ℝ))
      (fun _ => 3) := DFP.TwoLeg.EqModPow.refl 5 _
  have hthreeBeta : DFP.TwoLeg.EqModPow 5 threeBeta threeBetaP := by
    simpa only [threeBeta, threeBetaP] using
      hthree.mul hbeta continuousAt_const hbetaCont
  have hthreeBetaCont : ContinuousAt threeBeta 0 := by fun_prop
  have hthreeBetaPCont : ContinuousAt threeBetaP 0 := by fun_prop
  have hthreeBetaZero : threeBeta 0 ≠ 0 := by
    have hzero := DFP.TwoLeg.EqModPow.eq_at_zero_of_pos (by norm_num) hthreeBeta
    rw [hzero]
    norm_num [threeBetaP, betaP]
  let numQ : ℝ → ℝ := fun ε => ε ^ 3 * delta ε * w1 ε
  let numQP : ℝ → ℝ := fun ε => ε ^ 3 * deltaP ε * w1P ε
  have hCubeDelta := hCube.mul hdelta hCubeCont hdeltaCont
  have hnumQ : DFP.TwoLeg.EqModPow 5 numQ numQP := by
    have hraw := hCubeDelta.mul hw1
      (hCubeCont.mul hdeltaPCont) hw1Cont
    simpa only [numQ, numQP, mul_assoc] using hraw
  let termQP : ℝ → ℝ := fun ε => -2 * ε ^ 3 + 2 * ε ^ 4
  have htermQPoly : DFP.TwoLeg.EqModPow 5 numQP
      (fun ε => threeBetaP ε * termQP ε) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => -(3 / 5) * ε *
        (1156 * ε ^ 5 - 7304 * ε ^ 4 + 2208 * ε ^ 3 +
          58 * ε ^ 2 - 483 * ε + 228))
    · fun_prop
    · intro ε
      simp [numQP, threeBetaP, betaP, termQP, deltaP, w1P]
      ring
  let termQ : ℝ → ℝ := fun ε => numQ ε / threeBeta ε
  have htermQ : DFP.TwoLeg.EqModPow 5 termQ termQP := by
    simpa only [termQ] using DFP.TwoLeg.EqModPow.div_approx
      hnumQ hthreeBeta htermQPoly hthreeBetaPCont (by fun_prop)
        hthreeBetaCont hthreeBetaZero
  let numV : ℝ → ℝ := fun ε => delta ε * w2 ε
  let numVP : ℝ → ℝ := fun ε => deltaP ε * w2P ε
  have hnumV : DFP.TwoLeg.EqModPow 5 numV numVP := by
    simpa only [numV, numVP] using hdelta.mul hw2 hdeltaPCont hw2Cont
  let termVP : ℝ → ℝ := fun ε =>
    1 + (94 / 5) * ε ^ 3 - (69 / 10) * ε ^ 4
  have htermVPoly : DFP.TwoLeg.EqModPow 5 numVP
      (fun ε => threeBetaP ε * termVP ε) := by
    apply DFP.TwoLeg.EqModPow.of_factor
      (q := fun ε => (3 / 50) * ε * (29 * ε - 68) * (29 * ε + 52))
    · fun_prop
    · intro ε
      simp [numVP, threeBetaP, betaP, termVP, deltaP, w2P]
      ring
  let termV : ℝ → ℝ := fun ε => numV ε / threeBeta ε
  have htermV : DFP.TwoLeg.EqModPow 5 termV termVP := by
    simpa only [termV] using DFP.TwoLeg.EqModPow.div_approx
      hnumV hthreeBeta htermVPoly hthreeBetaPCont (by fun_prop)
        hthreeBetaCont hthreeBetaZero
  let qFinal : ℝ → ℝ := fun ε => Q ε - termQ ε
  let qFinalP : ℝ → ℝ := fun ε => 1 - (9 / 2) * ε ^ 4
  have hqFinal : DFP.TwoLeg.EqModPow 5 qFinal qFinalP := by
    apply DFP.TwoLeg.EqModPow.congr (hQ.sub htermQ)
    · intro ε
      rfl
    · intro ε
      simp [QP, termQP, qFinalP]
      ring
  let vFinal : ℝ → ℝ := fun ε => U ε - termV ε
  let vFinalP : ℝ → ℝ := fun ε =>
    -(38 / 5) * ε ^ 3 + (29 / 5) * ε ^ 4
  have hvFinal : DFP.TwoLeg.EqModPow 5 vFinal vFinalP := by
    apply DFP.TwoLeg.EqModPow.congr (hU.sub htermV)
    · intro ε
      rfl
    · intro ε
      simp [UP, termVP, vFinalP]
      ring
  have hqFinalCont : ContinuousAt qFinal 0 := by
    dsimp [qFinal, termQ, numQ, threeBeta]
    fun_prop (disch := exact hthreeBetaZero)
  have hqFinalZero : qFinal 0 ≠ 0 := by
    have hzero := DFP.TwoLeg.EqModPow.eq_at_zero_of_pos (by norm_num) hqFinal
    rw [hzero]
    norm_num [qFinalP]
  let numerator : ℝ → ℝ := fun ε => ε ^ 2 * vFinal ε
  let numeratorP : ℝ → ℝ := fun ε => ε ^ 2 * vFinalP ε
  have hnumerator : DFP.TwoLeg.EqModPow 7 numerator numeratorP := by
    simpa only [numerator, numeratorP] using
      DFP.TwoLeg.EqModPow.mul_pow_left (k := 2) hvFinal
  let slopeP : ℝ → ℝ := fun ε =>
    -(38 / 5) * ε ^ 5 + (29 / 5) * ε ^ 6
  have hnumeratorP : DFP.TwoLeg.EqModPow 7 numeratorP slopeP :=
    DFP.TwoLeg.EqModPow.of_eq 7 (fun ε => by
      simp [numeratorP, vFinalP, slopeP]
      ring)
  have hnumeratorSlope : DFP.TwoLeg.EqModPow 7 numerator slopeP :=
    hnumerator.trans hnumeratorP
  have hqFinalFour : DFP.TwoLeg.EqModPow 4 qFinal qFinalP :=
    DFP.TwoLeg.EqModPow.mono hqFinal (by norm_num)
  let one : ℝ → ℝ := fun _ => 1
  have hqFinalPOne : DFP.TwoLeg.EqModPow 4 qFinalP one := by
    apply DFP.TwoLeg.EqModPow.of_factor (q := fun _ => -(9 / 2))
    · fun_prop
    · intro ε
      simp [qFinalP, one]
  have hqFinalOne : DFP.TwoLeg.EqModPow 4 qFinal one :=
    hqFinalFour.trans hqFinalPOne
  let slopeCoeff : ℝ → ℝ := fun ε => -(38 / 5) + (29 / 5) * ε
  have hslopePOrder : slopeP =O[𝓝 0] (fun ε : ℝ => ε ^ 5) := by
    have hcoeff : slopeCoeff =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
      (by fun_prop : ContinuousAt slopeCoeff 0).isBigO
    have hraw := hcoeff.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 5) (𝓝 0))
    refine hraw.congr' ?_ (Filter.Eventually.of_forall fun _ => by simp)
    exact Filter.Eventually.of_forall (fun ε => by
      simp [slopeCoeff, slopeP]
      ring)
  have hmulNine := (DFP.TwoLeg.EqModPow.to_isBigO hqFinalOne).mul hslopePOrder
  have hmulSeven : (fun ε => (qFinal ε - one ε) * slopeP ε) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 7) := by
    have hraw : (fun ε => (qFinal ε - one ε) * slopeP ε) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 9) := by
      simpa only [← pow_add, Nat.reduceAdd] using hmulNine
    exact hraw.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 9)) |>.isBigO
  have hqMul : DFP.TwoLeg.EqModPow 7
      (fun ε => qFinal ε * slopeP ε) slopeP := by
    apply DFP.TwoLeg.EqModPow.of_isBigO
    refine hmulSeven.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    exact Filter.Eventually.of_forall (fun ε => by
      simp [one]
      ring)
  have hslope : DFP.TwoLeg.EqModPow 7
      (fun ε => numerator ε / qFinal ε) slopeP :=
    DFP.TwoLeg.EqModPow.div_of_eq_mul
      (hnumeratorSlope.trans hqMul.symm) hqFinalCont hqFinalZero
  have hslopeFormula : ∀ ε,
      slowFinalSlope ε = numerator ε / qFinal ε := by
    intro ε
    rw [slowFinalSlope_apply, DFP.TwoLeg.slowGraphJetPath_apply]
  have hpolynomialFormula : ∀ ε,
      slowFinalSlopePolynomial ε = slopeP ε := by
    intro ε
    rw [slowFinalSlopePolynomial_apply]
  exact DFP.TwoLeg.EqModPow.to_isBigO
    (DFP.TwoLeg.EqModPow.congr hslope hslopeFormula hpolynomialFormula)

end DFP.TwoLeg.EndpointAngleJet
