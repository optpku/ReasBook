module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.FirstLegScaleExpansion
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.FirstLegScaleExpansion
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
-- second-leg `EqModPow 5` expressions and does not alter inference.
local infix:50 " =₅ " => EqModPow 5
set_option maxHeartbeats 1000000 in
-- The explicit two-leg rational and square-root normalization has a large elaboration term.
/-- Order-five germs of the second-leg radius, shape, and high factors on the pure scale axis. -/
theorem pureScale_factor_expansions :
    (fun ε : ℝ => radiusFactor ε 2 1) =₅
        (fun ε => 1 - (50 / 3) * ε ^ 3 + 3 * ε ^ 4) ∧
    (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1) =₅
        (fun ε => 2 + (116 / 3) * ε ^ 3 - 2 * ε ^ 4) ∧
    (fun ε : ℝ => (stateMap (ε, 2, 1)).2.2) =₅
        (fun ε => 1 + 8 * ε ^ 3) := by
  let L : ℝ → ℝ := fun ε => (DFP.FirstLeg.spectralFactors ε 2 1).1
  let H : ℝ → ℝ := fun ε => (DFP.FirstLeg.spectralFactors ε 2 1).2
  let Q : ℝ → ℝ := fun ε => (DFP.FirstLeg.gradientFactors ε 2 1).1
  let U : ℝ → ℝ := fun ε => (DFP.FirstLeg.gradientFactors ε 2 1).2
  let LP : ℝ → ℝ := fun ε => 2 + 4 * ε ^ 3 + 2 * ε ^ 4
  let HP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3
  let QP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  let UP : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3 - (1 / 2) * ε ^ 4
  rcases firstLeg_scale_factor_expansions with ⟨hL0, hH0, hQ0, hU0⟩
  have hL : L =₅ LP := by simpa [L, LP] using hL0
  have hH : H =₅ HP := by simpa [H, HP] using hH0
  have hQ : Q =₅ QP := by simpa [Q, QP] using hQ0
  have hU : U =₅ UP := by simpa [U, UP] using hU0
  let path : ℝ → ℝ × ℝ × ℝ := fun ε => (ε, 2, 1)
  have hpath : ContinuousAt path 0 := by fun_prop
  have hfac : ContinuousAt (fun ε : ℝ => DFP.FirstLeg.factors ε 2 1) 0 := by
    have hall := DFP.FirstLeg.factorsAnalytic.continuousAt.comp (f := path) hpath
    simpa [Function.comp_def, path] using hall
  have hLcont : ContinuousAt L 0 := by
    simpa only [L, DFP.FirstLeg.factors.eq_1] using hfac.fst.fst
  have hHcont : ContinuousAt H 0 := by
    simpa only [H, DFP.FirstLeg.factors.eq_1] using hfac.fst.snd
  have hQcont : ContinuousAt Q 0 := by
    simpa only [Q, DFP.FirstLeg.factors.eq_1] using hfac.snd.fst.fst
  have hUcont : ContinuousAt U 0 := by
    simpa only [U, DFP.FirstLeg.factors.eq_1] using hfac.snd.fst.snd
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors.eq_1] using congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors.eq_1] using
      congrArg (fun z => z.2.1) DFP.FirstLeg.factorsBase
  have hLbase : L 0 = 2 := by simp [L, hspectralBase]
  have hHbase : H 0 = 1 := by simp [H, hspectralBase]
  have hQbase : Q 0 = 1 := by simp [Q, hgradientBase]
  have hUbase : U 0 = 1 := by simp [U, hgradientBase]
  let X : ℝ → ℝ := fun ε => ε
  let x3 : ℝ → ℝ := fun ε => ε ^ 3
  let x6 : ℝ → ℝ := fun ε => ε ^ 6
  let two : ℝ → ℝ := fun _ => 2
  let three : ℝ → ℝ := fun _ => 3
  let zero : ℝ → ℝ := fun _ => 0
  have hLQ := hL.mul hQ (by fun_prop) hQcont
  have hHU := hH.mul hU (by fun_prop) hUcont
  have hXLQ := (EqModPow.refl 5 X).mul hLQ (by fun_prop)
    (hLcont.mul hQcont)
  have htwoHU := (EqModPow.refl 5 two).mul hHU (by fun_prop)
    (hHcont.mul hUcont)
  let w1 : ℝ → ℝ := fun ε => X ε * L ε * Q ε - 2 * H ε * U ε
  let w1P : ℝ → ℝ := fun ε => -2 + 2 * ε + 8 * ε ^ 3 + ε ^ 4
  have hw1Raw : w1 =₅
      (fun ε => X ε * LP ε * QP ε - 2 * HP ε * UP ε) := by
    apply eqModPow_congr_of_eq (hXLQ.sub htwoHU)
    · intro ε
      simp [w1, X, two]
      ring
    · intro ε
      simp [X, two]
      ring
  have hw1Poly :
      (fun ε => X ε * LP ε * QP ε - 2 * HP ε * UP ε) =₅ w1P := by
    apply EqModPow.of_factor
      (q := fun ε => -(5 * ε ^ 4 + 14 * ε ^ 3 + 10 * ε ^ 2 + 8 * ε + 3))
    · fun_prop
    · intro ε
      simp [X, LP, HP, QP, UP, w1P]
      ring
  have hw1 : w1 =₅ w1P := hw1Raw.trans hw1Poly
  have hw1cont : ContinuousAt w1 0 := by fun_prop
  have hx3LQ := (EqModPow.refl 5 x3).mul hLQ (by fun_prop)
    (hLcont.mul hQcont)
  have htwoX3LQ := (EqModPow.refl 5 two).mul hx3LQ (by fun_prop)
    (by fun_prop)
  let w2 : ℝ → ℝ := fun ε => H ε * U ε - 2 * ε ^ 3 * L ε * Q ε
  let w2P : ℝ → ℝ := fun ε => 1 - 8 * ε ^ 3 - (1 / 2) * ε ^ 4
  have hw2Raw : w2 =₅
      (fun ε => HP ε * UP ε - 2 * ε ^ 3 * LP ε * QP ε) := by
    apply eqModPow_congr_of_eq (hHU.sub htwoX3LQ)
    · intro ε
      simp [w2, x3, two]
      ring
    · intro ε
      simp [x3, two]
      ring
  have hw2Poly :
      (fun ε => HP ε * UP ε - 2 * ε ^ 3 * LP ε * QP ε) =₅ w2P := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (10 * ε ^ 5 + 28 * ε ^ 4 + 16 * ε ^ 3 + 7 * ε + 4))
    · fun_prop
    · intro ε
      simp [HP, UP, LP, QP, w2P]
      ring
  have hw2 : w2 =₅ w2P := hw2Raw.trans hw2Poly
  have hw2cont : ContinuousAt w2 0 := by fun_prop
  have hw1base : w1 0 = -2 := by norm_num [w1, X, hLbase, hHbase, hQbase, hUbase]
  have hw2base : w2 0 = 1 := by norm_num [w2, hLbase, hHbase, hQbase, hUbase]
  have hx3LQw1 := hx3LQ.mul hw1 (by fun_prop) hw1cont
  have hHUw2 := hHU.mul hw2 (by fun_prop) hw2cont
  let beta : ℝ → ℝ := fun ε =>
    ε ^ 3 * L ε * Q ε * w1 ε + H ε * U ε * w2 ε
  let betaP : ℝ → ℝ := fun ε => 1 - 16 * ε ^ 3 + 3 * ε ^ 4
  have hbetaRaw : beta =₅
      (fun ε => ε ^ 3 * LP ε * QP ε * w1P ε +
        HP ε * UP ε * w2P ε) := by
    apply eqModPow_congr_of_eq (hx3LQw1.add hHUw2)
    · intro ε
      dsimp [beta, x3]
      ring
    · intro ε
      dsimp [x3]
      ring
  have hbetaPoly :
      (fun ε => ε ^ 3 * LP ε * QP ε * w1P ε +
        HP ε * UP ε * w2P ε) =₅ betaP := by
    apply EqModPow.of_factor
      (q := fun ε => -ε *
        (20 * ε ^ 9 + 216 * ε ^ 8 + 480 * ε ^ 7 + 296 * ε ^ 6 +
          86 * ε ^ 5 + 88 * ε ^ 4 + 64 * ε ^ 3 + 23 * ε ^ 2 -
          60 * ε - 208) / 4)
    · fun_prop
    · intro ε
      simp [LP, HP, QP, UP, w1P, w2P, betaP]
      ring
  have hbeta : beta =₅ betaP := hbetaRaw.trans hbetaPoly
  have hbetacont : ContinuousAt beta 0 := by fun_prop
  have hbetabase : beta 0 = 1 := by
    norm_num [beta, hw1base, hw2base, hHbase, hUbase]
  have hbeta0 : beta 0 ≠ 0 := by rw [hbetabase]; norm_num
  have hw1sq := hw1.mul hw1 (by fun_prop) hw1cont
  have hw2sq := hw2.mul hw2 (by fun_prop) hw2cont
  have hLw1sq := hL.mul hw1sq (by fun_prop) (hw1cont.mul hw1cont)
  have hx6Lw1sq := (EqModPow.refl 5 x6).mul hLw1sq (by fun_prop)
    (hLcont.mul (hw1cont.mul hw1cont))
  have hHw2sq := hH.mul hw2sq (by fun_prop) (hw2cont.mul hw2cont)
  let gamma : ℝ → ℝ := fun ε =>
    ε ^ 6 * L ε * w1 ε ^ 2 + H ε * w2 ε ^ 2
  let gammaP : ℝ → ℝ := fun ε => 1 - 18 * ε ^ 3 - ε ^ 4
  have hgammaRaw : gamma =₅
      (fun ε => ε ^ 6 * LP ε * w1P ε ^ 2 + HP ε * w2P ε ^ 2) := by
    apply eqModPow_congr_of_eq (hx6Lw1sq.add hHw2sq)
    · intro ε
      simp [gamma, x6]
      ring
    · intro ε
      simp [x6]
      ring
  have hgammaPoly :
      (fun ε => ε ^ 6 * LP ε * w1P ε ^ 2 + HP ε * w2P ε ^ 2) =₅
        gammaP := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (8 * ε ^ 12 + 144 * ε ^ 11 + 768 * ε ^ 10 + 1056 * ε ^ 9 +
          296 * ε ^ 8 + 320 * ε ^ 7 + 32 * ε ^ 6 + 30 * ε ^ 5 +
          64 * ε ^ 4 - 704 * ε ^ 3 + 33 * ε ^ 2 - 24 * ε + 416) / 4)
    · fun_prop
    · intro ε
      simp [LP, HP, w1P, w2P, gammaP]
      ring
  have hgamma : gamma =₅ gammaP := hgammaRaw.trans hgammaPoly
  have hgammacont : ContinuousAt gamma 0 := by fun_prop
  have hgammabase : gamma 0 = 1 := by
    norm_num [gamma, hw2base, hHbase]
  have hgamma0 : gamma 0 ≠ 0 := by rw [hgammabase]; norm_num
  have hQsq := hQ.mul hQ (by fun_prop) hQcont
  have hUssq := hU.mul hU (by fun_prop) hUcont
  have hLQsq := hL.mul hQsq (by fun_prop) (hQcont.mul hQcont)
  have hHUsq := hH.mul hUssq (by fun_prop) (hUcont.mul hUcont)
  let delta : ℝ → ℝ := fun ε => L ε * Q ε ^ 2 + H ε * U ε ^ 2
  let deltaP : ℝ → ℝ := fun ε => 3 - 10 * ε ^ 3 - 9 * ε ^ 4
  have hdeltaRaw : delta =₅
      (fun ε => LP ε * QP ε ^ 2 + HP ε * UP ε ^ 2) := by
    apply eqModPow_congr_of_eq (hLQsq.add hHUsq)
    · intro ε
      simp [delta]
      ring
    · intro ε
      ring
  have hdeltaPoly :
      (fun ε => LP ε * QP ε ^ 2 + HP ε * UP ε ^ 2) =₅ deltaP := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (50 * ε ^ 6 + 178 * ε ^ 5 + 176 * ε ^ 4 + 32 * ε ^ 3 +
          11 * ε ^ 2 - 16 * ε + 16) / 4)
    · fun_prop
    · intro ε
      simp [LP, HP, QP, UP, deltaP]
      ring
  have hdelta : delta =₅ deltaP := hdeltaRaw.trans hdeltaPoly
  have hdeltacont : ContinuousAt delta 0 := by fun_prop
  have hLsq := hL.mul hL (by fun_prop) hLcont
  have hLsqQsq := hLsq.mul hQsq (by fun_prop) (hQcont.mul hQcont)
  let rA : ℝ → ℝ := fun ε => 4 + 64 * ε ^ 3 - 24 * ε ^ 4
  have hrAPoly :
      (fun ε => LP ε ^ 2 * QP ε ^ 2) =₅
        (fun ε => betaP ε * rA ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (25 * ε ^ 10 + 140 * ε ^ 9 + 276 * ε ^ 8 + 224 * ε ^ 7 +
          94 * ε ^ 6 + 84 * ε ^ 5 + 48 * ε ^ 4 + 61 * ε ^ 2 -
          632 * ε + 992))
    · fun_prop
    · intro ε
      simp [LP, QP, betaP, rA]
      ring
  have hrA :
      (fun ε => L ε ^ 2 * Q ε ^ 2 / beta ε) =₅ rA :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hLsqQsq (fun ε => by ring) (fun ε => by ring))
      hbeta hrAPoly (by fun_prop) (by fun_prop) hbetacont hbeta0
  have hrAcont : ContinuousAt (fun ε => L ε ^ 2 * Q ε ^ 2 / beta ε) 0 := by
    have hnum : ContinuousAt (fun ε => L ε ^ 2 * Q ε ^ 2) 0 :=
      (hLcont.pow 2).mul (hQcont.pow 2)
    exact hnum.div hbetacont hbeta0
  have hLsqW1sq := hLsq.mul hw1sq (by fun_prop) (hw1cont.mul hw1cont)
  have hx6LsqW1sq := (EqModPow.refl 5 x6).mul hLsqW1sq (by fun_prop)
    ((hLcont.mul hLcont).mul (hw1cont.mul hw1cont))
  have hx6PolyZero :
      (fun ε => ε ^ 6 * LP ε ^ 2 * w1P ε ^ 2) =₅ zero := by
    apply EqModPow.of_factor
      (q := fun ε => ε * LP ε ^ 2 * w1P ε ^ 2)
    · fun_prop
    · intro ε
      simp [zero]
      ring
  have hx6ExactZero :
      (fun ε => ε ^ 6 * L ε ^ 2 * w1 ε ^ 2) =₅ zero := by
    exact (eqModPow_congr_of_eq hx6LsqW1sq (fun ε => by simp [x6]; ring)
      (fun ε => by simp [x6]; ring)).trans hx6PolyZero
  have hx6DivZero :
      (fun ε => ε ^ 6 * L ε ^ 2 * w1 ε ^ 2 / gamma ε) =₅ zero := by
    apply EqModPow.div_of_eq_mul _ hgammacont hgamma0
    exact eqModPow_congr_of_eq hx6ExactZero (fun _ => rfl)
      (fun ε => by simp [zero])
  have hx6DivCont :
      ContinuousAt (fun ε => ε ^ 6 * L ε ^ 2 * w1 ε ^ 2 / gamma ε) 0 := by
    apply ContinuousAt.div _ hgammacont hgamma0
    fun_prop
  let a : ℝ → ℝ := fun ε =>
    L ε - ε ^ 6 * L ε ^ 2 * w1 ε ^ 2 / gamma ε +
      L ε ^ 2 * Q ε ^ 2 / beta ε
  let aP : ℝ → ℝ := fun ε => 6 + 68 * ε ^ 3 - 22 * ε ^ 4
  have haRaw : a =₅ (fun ε => LP ε - 0 + rA ε) := by
    apply eqModPow_congr_of_eq ((hL.sub hx6DivZero).add hrA)
    · intro ε
      rfl
    · intro ε
      rfl
  have ha : a =₅ aP :=
    haRaw.trans (eqModPow_of_eq 5 (fun ε => by simp [LP, rA, aP]; ring))
  have hacont : ContinuousAt a 0 := by
    exact (hLcont.sub hx6DivCont).add hrAcont
  have hLH := hL.mul hH (by fun_prop) hHcont
  have hLHw1 := hLH.mul hw1 (by fun_prop) hw1cont
  have hLHw1w2 := hLHw1.mul hw2 (by fun_prop) hw2cont
  have hx3LHw1w2 := (EqModPow.refl 5 x3).mul hLHw1w2 (by fun_prop)
    (((hLcont.mul hHcont).mul hw1cont).mul hw2cont)
  let rB1 : ℝ → ℝ := fun ε => -4 * ε ^ 3 + 4 * ε ^ 4
  have hrB1Poly :
      (fun ε => ε ^ 3 * LP ε * HP ε * w1P ε * w2P ε) =₅
        (fun ε => gammaP ε * rB1 ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (2 * ε ^ 12 + 52 * ε ^ 11 + 352 * ε ^ 10 + 515 * ε ^ 9 +
          40 * ε ^ 8 - 112 * ε ^ 7 - 194 * ε ^ 6 - 37 * ε ^ 5 +
          16 * ε ^ 4 - 112 * ε ^ 3 + 6 * ε ^ 2 + 36 * ε - 24))
    · fun_prop
    · intro ε
      simp [LP, HP, w1P, w2P, gammaP, rB1]
      ring
  have hrB1 :
      (fun ε => ε ^ 3 * L ε * H ε * w1 ε * w2 ε / gamma ε) =₅ rB1 :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hx3LHw1w2 (fun ε => by simp [x3]; ring)
        (fun ε => by simp [x3]; ring))
      hgamma hrB1Poly (by fun_prop) (by fun_prop) hgammacont hgamma0
  have hrB1cont :
      ContinuousAt (fun ε => ε ^ 3 * L ε * H ε * w1 ε * w2 ε / gamma ε) 0 := by
    apply ContinuousAt.div _ hgammacont hgamma0
    fun_prop
  have hLQHU := hLQ.mul hHU (by fun_prop) (hHcont.mul hUcont)
  let rB2 : ℝ → ℝ := fun ε => 2 + 24 * ε ^ 3 - 10 * ε ^ 4
  have hrB2Poly :
      (fun ε => LP ε * QP ε * HP ε * UP ε) =₅
        (fun ε => betaP ε * rB2 ε) := by
    apply EqModPow.of_factor
      (q := fun ε => -ε *
        (10 * ε ^ 9 + 68 * ε ^ 8 + 128 * ε ^ 7 + 59 * ε ^ 6 -
          48 * ε ^ 5 - 96 * ε ^ 4 - 64 * ε ^ 3 - 53 * ε ^ 2 +
          464 * ε - 768) / 2)
    · fun_prop
    · intro ε
      simp [LP, QP, HP, UP, betaP, rB2]
      ring
  have hrB2 :
      (fun ε => L ε * Q ε * H ε * U ε / beta ε) =₅ rB2 :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hLQHU (fun ε => by ring) (fun ε => by ring))
      hbeta hrB2Poly (by fun_prop) (by fun_prop) hbetacont hbeta0
  have hrB2cont :
      ContinuousAt (fun ε => L ε * Q ε * H ε * U ε / beta ε) 0 := by
    apply ContinuousAt.div _ hbetacont hbeta0
    fun_prop
  let b : ℝ → ℝ := fun ε =>
    -(ε ^ 3 * L ε * H ε * w1 ε * w2 ε / gamma ε) +
      L ε * Q ε * H ε * U ε / beta ε
  let bP : ℝ → ℝ := fun ε => 2 + 28 * ε ^ 3 - 14 * ε ^ 4
  have hbRaw : b =₅ (fun ε => -rB1 ε + rB2 ε) := by
    exact eqModPow_congr_of_eq (hrB1.neg.add hrB2) (fun _ => rfl) (fun _ => rfl)
  have hb : b =₅ bP :=
    hbRaw.trans (eqModPow_of_eq 5 (fun ε => by simp [rB1, rB2, bP]; ring))
  have hbcont : ContinuousAt b 0 := hrB1cont.neg.add hrB2cont
  have hHsq := hH.mul hH (by fun_prop) hHcont
  have hHsqW2sq := hHsq.mul hw2sq (by fun_prop) (hw2cont.mul hw2cont)
  let rD1 : ℝ → ℝ := fun ε => 1 - 2 * ε ^ 3
  have hrD1Poly :
      (fun ε => HP ε ^ 2 * w2P ε ^ 2) =₅
        (fun ε => gammaP ε * rD1 ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε * (ε + 16) * (2 * ε ^ 3 - 1) *
        (2 * ε ^ 4 + 32 * ε ^ 3 - ε - 24) / 4)
    · fun_prop
    · intro ε
      simp [HP, w2P, gammaP, rD1]
      ring
  have hrD1 :
      (fun ε => H ε ^ 2 * w2 ε ^ 2 / gamma ε) =₅ rD1 :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hHsqW2sq (fun ε => by ring) (fun ε => by ring))
      hgamma hrD1Poly (by fun_prop) (by fun_prop) hgammacont hgamma0
  have hrD1cont :
      ContinuousAt (fun ε => H ε ^ 2 * w2 ε ^ 2 / gamma ε) 0 := by
    apply ContinuousAt.div _ hgammacont hgamma0
    fun_prop
  have hHsqUsq := hHsq.mul hUssq (by fun_prop) (hUcont.mul hUcont)
  let rD2 : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3 - 4 * ε ^ 4
  have hrD2Poly :
      (fun ε => HP ε ^ 2 * UP ε ^ 2) =₅
        (fun ε => betaP ε * rD2 ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (4 * ε ^ 8 + 32 * ε ^ 7 + 64 * ε ^ 6 - 4 * ε ^ 5 -
          48 * ε ^ 4 - 128 * ε ^ 3 + 49 * ε ^ 2 - 328 * ε + 608) / 4)
    · fun_prop
    · intro ε
      simp [HP, UP, betaP, rD2]
      ring
  have hrD2 :
      (fun ε => H ε ^ 2 * U ε ^ 2 / beta ε) =₅ rD2 :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hHsqUsq (fun ε => by ring) (fun ε => by ring))
      hbeta hrD2Poly (by fun_prop) (by fun_prop) hbetacont hbeta0
  have hrD2cont :
      ContinuousAt (fun ε => H ε ^ 2 * U ε ^ 2 / beta ε) 0 := by
    have hnum : ContinuousAt (fun ε => H ε ^ 2 * U ε ^ 2) 0 :=
      (hHcont.pow 2).mul (hUcont.pow 2)
    exact hnum.div hbetacont hbeta0
  let d : ℝ → ℝ := fun ε =>
    H ε - H ε ^ 2 * w2 ε ^ 2 / gamma ε +
      H ε ^ 2 * U ε ^ 2 / beta ε
  let dP : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3 - 4 * ε ^ 4
  have hdRaw : d =₅ (fun ε => HP ε - rD1 ε + rD2 ε) := by
    exact eqModPow_congr_of_eq ((hH.sub hrD1).add hrD2)
      (fun _ => rfl) (fun _ => rfl)
  have hd : d =₅ dP :=
    hdRaw.trans (eqModPow_of_eq 5 (fun ε => by simp [HP, rD1, rD2, dP]))
  have hdcont : ContinuousAt d 0 := (hHcont.sub hrD1cont).add hrD2cont
  have hx3Delta := (EqModPow.refl 5 x3).mul hdelta (by fun_prop) hdeltacont
  have hx3DeltaPcont : ContinuousAt (fun ε => x3 ε * deltaP ε) 0 := by
    fun_prop
  have hx3DeltaW1 := hx3Delta.mul hw1 hx3DeltaPcont hw1cont
  let threeBeta : ℝ → ℝ := fun ε => 3 * beta ε
  let threeBetaP : ℝ → ℝ := fun ε => 3 * betaP ε
  have hthreeBeta : threeBeta =₅ threeBetaP := by
    apply eqModPow_congr_of_eq
      ((EqModPow.refl 5 three).mul hbeta (by fun_prop) hbetacont)
    · intro ε
      simp [threeBeta, three]
    · intro ε
      simp [threeBetaP, three]
  have hthreeBetacont : ContinuousAt threeBeta 0 := by fun_prop
  have hthreeBeta0 : threeBeta 0 ≠ 0 := by norm_num [threeBeta, hbetabase]
  let rQ : ℝ → ℝ := fun ε => -2 * ε ^ 3 + 2 * ε ^ 4
  have hrQPoly :
      (fun ε => ε ^ 3 * deltaP ε * w1P ε) =₅
        (fun ε => threeBetaP ε * rQ ε) := by
    apply EqModPow.of_factor
      (q := fun ε => -ε *
        (9 * ε ^ 5 + 82 * ε ^ 4 + 80 * ε ^ 3 + 36 * ε ^ 2 -
          115 * ε + 52))
    · fun_prop
    · intro ε
      simp [deltaP, w1P, threeBetaP, betaP, rQ]
      ring
  have hrQ :
      (fun ε => ε ^ 3 * delta ε * w1 ε / threeBeta ε) =₅ rQ :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hx3DeltaW1 (fun ε => by simp [x3])
        (fun ε => by simp [x3]))
      hthreeBeta hrQPoly (by fun_prop) (by fun_prop) hthreeBetacont hthreeBeta0
  have hrQcont :
      ContinuousAt (fun ε => ε ^ 3 * delta ε * w1 ε / threeBeta ε) 0 := by
    apply ContinuousAt.div _ hthreeBetacont hthreeBeta0
    fun_prop
  let q : ℝ → ℝ := fun ε => Q ε - ε ^ 3 * delta ε * w1 ε / threeBeta ε
  let qP : ℝ → ℝ := fun ε => 1 - (9 / 2) * ε ^ 4
  have hqRaw : q =₅ (fun ε => QP ε - rQ ε) := by
    exact eqModPow_congr_of_eq (hQ.sub hrQ) (fun _ => rfl) (fun _ => rfl)
  have hq : q =₅ qP :=
    hqRaw.trans (eqModPow_of_eq 5 (fun ε => by simp [QP, rQ, qP]; ring))
  have hqcont : ContinuousAt q 0 := hQcont.sub hrQcont
  have hdeltaW2 := hdelta.mul hw2 (by fun_prop) hw2cont
  let rV : ℝ → ℝ := fun ε => 1 + (14 / 3) * ε ^ 3 - (13 / 2) * ε ^ 4
  have hrVPoly :
      (fun ε => deltaP ε * w2P ε) =₅
        (fun ε => threeBetaP ε * rV ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε * (7 * ε - 16) * (9 * ε - 19))
    · fun_prop
    · intro ε
      simp [deltaP, w2P, threeBetaP, betaP, rV]
      ring
  have hrV :
      (fun ε => delta ε * w2 ε / threeBeta ε) =₅ rV :=
    eqModPow_div_approx hdeltaW2 hthreeBeta hrVPoly
      (by fun_prop) (by fun_prop) hthreeBetacont hthreeBeta0
  have hrVcont :
      ContinuousAt (fun ε => delta ε * w2 ε / threeBeta ε) 0 := by
    apply ContinuousAt.div _ hthreeBetacont hthreeBeta0
    fun_prop
  let v : ℝ → ℝ := fun ε => U ε - delta ε * w2 ε / threeBeta ε
  let vP : ℝ → ℝ := fun ε => -(20 / 3) * ε ^ 3 + 6 * ε ^ 4
  have hvRaw : v =₅ (fun ε => UP ε - rV ε) := by
    exact eqModPow_congr_of_eq (hU.sub hrV) (fun _ => rfl) (fun _ => rfl)
  have hv : v =₅ vP :=
    hvRaw.trans (eqModPow_of_eq 5 (fun ε => by simp [UP, rV, vP]; ring))
  have hvcont : ContinuousAt v 0 := hUcont.sub hrVcont
  have habase : a 0 = 6 := by
    norm_num [a, hLbase, hQbase, hw1base, hbetabase, hgammabase]
  have hbbase : b 0 = 2 := by
    norm_num [b, hLbase, hHbase, hQbase, hUbase, hw1base, hw2base,
      hbetabase, hgammabase]
  have hdbase : d 0 = 1 := by
    norm_num [d, hHbase, hUbase, hw2base, hbetabase, hgammabase]
  let x4 : ℝ → ℝ := fun ε => ε ^ 4
  let x2 : ℝ → ℝ := fun ε => ε ^ 2
  let A : ℝ → ℝ := fun ε => x4 ε * a ε
  let E : ℝ → ℝ := fun ε => x2 ε * b ε
  let AP : ℝ → ℝ := fun ε => 6 * ε ^ 4
  let EP : ℝ → ℝ := fun ε => 2 * ε ^ 2
  have hAraw : A =₅ (fun ε => x4 ε * aP ε) :=
    (EqModPow.refl 5 x4).mul ha (by fun_prop) hacont
  have hAtrunc : (fun ε => x4 ε * aP ε) =₅ AP := by
    apply EqModPow.of_factor (q := fun ε => -2 * ε ^ 2 * (11 * ε - 34))
    · fun_prop
    · intro ε
      simp [x4, aP, AP]
      ring
  have hA : A =₅ AP := hAraw.trans hAtrunc
  have hEraw : E =₅ (fun ε => x2 ε * bP ε) :=
    (EqModPow.refl 5 x2).mul hb (by fun_prop) hbcont
  have hEtrunc : (fun ε => x2 ε * bP ε) =₅ EP := by
    apply EqModPow.of_factor (q := fun ε => -14 * (ε - 2))
    · fun_prop
    · intro ε
      simp [x2, bP, EP]
      ring
  have hE : E =₅ EP := hEraw.trans hEtrunc
  have hAcont : ContinuousAt A 0 := by fun_prop
  have hEcont : ContinuousAt E 0 := by fun_prop
  let rad : ℝ → ℝ := fun ε => (d ε - A ε) ^ 2 + 4 * E ε ^ 2
  let gapP : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3 - 2 * ε ^ 4
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
    apply EqModPow.of_factor (q := fun ε => 32 * ε ^ 2 * (3 * ε - 4))
    · fun_prop
    · intro ε
      simp [dP, AP, EP, gapP]
      ring
  have hrad : rad =₅ (fun ε => gapP ε ^ 2) := hradRaw.trans hradPoly
  have hradcont : ContinuousAt rad 0 := by fun_prop
  have hgap : (fun ε => Real.sqrt (rad ε)) =₅ gapP := by
    apply EqModPow.sqrt_of_sq hrad hradcont (by fun_prop)
    · norm_num [rad, A, E, x4, x2, hdbase]
    · norm_num [gapP]
  let gap : ℝ → ℝ := fun ε => Real.sqrt (rad ε)
  let high : ℝ → ℝ := fun ε => (A ε + d ε + gap ε) / 2
  let low : ℝ → ℝ := fun ε => (A ε + d ε - gap ε) / 2
  let highP : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3
  let lowP : ℝ → ℝ := fun ε => 2 * ε ^ 4
  have hhighNum := (hA.add hd).add hgap
  have hhighPoly :
      (fun ε => AP ε + dP ε + gapP ε) =₅ (fun ε => 2 * highP ε) :=
    eqModPow_of_eq 5 (fun ε => by simp [AP, dP, gapP, highP]; ring)
  have hhigh : high =₅ highP := by
    have hdiv := eqModPow_div_approx hhighNum (EqModPow.refl 5 two)
      hhighPoly (by fun_prop) (by fun_prop) (by fun_prop) (by norm_num [two])
    exact eqModPow_congr_of_eq hdiv (fun _ => rfl) (fun _ => rfl)
  have hlowNum := (hA.add hd).sub hgap
  have hlowPoly :
      (fun ε => AP ε + dP ε - gapP ε) =₅ (fun ε => 2 * lowP ε) :=
    eqModPow_of_eq 5 (fun ε => by simp [AP, dP, gapP, lowP]; ring)
  have hlow : low =₅ lowP := by
    have hdiv := eqModPow_div_approx hlowNum (EqModPow.refl 5 two)
      hlowPoly (by fun_prop) (by fun_prop) (by fun_prop) (by norm_num [two])
    exact eqModPow_congr_of_eq hdiv (fun _ => rfl) (fun _ => rfl)
  have hgapcont : ContinuousAt gap 0 := hradcont.sqrt
  have hhighcont : ContinuousAt high 0 := by fun_prop
  have hlowcont : ContinuousAt low 0 := by fun_prop
  have hhighbase : high 0 = 1 := by
    norm_num [high, A, gap, rad, E, x4, x2, hdbase]
  have hhigh0 : high 0 ≠ 0 := by rw [hhighbase]; norm_num
  let denomRad : ℝ → ℝ := fun ε => (d ε - low ε) ^ 2 + E ε ^ 2
  let denomP : ℝ → ℝ := fun ε => 1 + 8 * ε ^ 3 - 4 * ε ^ 4
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
    apply EqModPow.of_factor (q := fun ε => 4 * ε ^ 2 * (5 * ε - 8))
    · fun_prop
    · intro ε
      simp [dP, lowP, EP, denomP]
      ring
  have hdenomRad : denomRad =₅ (fun ε => denomP ε ^ 2) :=
    hdenomRadRaw.trans hdenomRadPoly
  have hdenomRadcont : ContinuousAt denomRad 0 := by fun_prop
  let denom : ℝ → ℝ := fun ε => Real.sqrt (denomRad ε)
  have hdenom : denom =₅ denomP := by
    apply EqModPow.sqrt_of_sq hdenomRad hdenomRadcont (by fun_prop)
    · norm_num [denomRad, d, low, A, E, gap, rad, x4, x2, hdbase]
    · norm_num [denomP]
  have hdenomcont : ContinuousAt denom 0 := hdenomRadcont.sqrt
  have hdenombase : denom 0 = 1 := by
    norm_num [denom, denomRad, d, low, A, E, gap, rad, x4, x2, hdbase]
  have hdenom0 : denom 0 ≠ 0 := by rw [hdenombase]; norm_num
  let L2P : ℝ → ℝ := fun ε => 2 - 12 * ε ^ 3 + 10 * ε ^ 4
  have had := ha.mul hd (by fun_prop) hdcont
  have hbb := hb.mul hb (by fun_prop) hbcont
  have hL2num :
      (fun ε => a ε * d ε - b ε ^ 2) =₅
        (fun ε => aP ε * dP ε - bP ε ^ 2) := by
    apply eqModPow_congr_of_eq (had.sub hbb)
    · intro ε
      ring
    · intro ε
      ring
  have hL2poly :
      (fun ε => aP ε * dP ε - bP ε ^ 2) =₅
        (fun ε => highP ε * L2P ε) := by
    apply EqModPow.of_factor
      (q := fun ε => -4 * ε * (27 * ε ^ 2 - 64 * ε + 36))
    · fun_prop
    · intro ε
      simp [aP, bP, dP, highP, L2P]
      ring
  have hL2local :
      (fun ε => (a ε * d ε - b ε ^ 2) / high ε) =₅ L2P :=
    eqModPow_div_approx hL2num hhigh hL2poly
      (by fun_prop) (by fun_prop) hhighcont hhigh0
  let Q2P : ℝ → ℝ := fun ε => 1 - (13 / 2) * ε ^ 4
  have hdq := (hd.sub hlow).mul hq (by fun_prop) hqcont
  have hbv := hb.mul hv (by fun_prop) hvcont
  have hx4bv := (EqModPow.refl 5 x4).mul hbv (by fun_prop)
    (hbcont.mul hvcont)
  have hQ2num :
      (fun ε => (d ε - low ε) * q ε - x4 ε * b ε * v ε) =₅
        (fun ε => (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε) := by
    apply eqModPow_congr_of_eq (hdq.sub hx4bv)
    · intro ε
      simp [x4]
      ring
    · intro ε
      simp [x4]
      ring
  have hQ2poly :
      (fun ε => (dP ε - lowP ε) * qP ε - ε ^ 4 * bP ε * vP ε) =₅
        (fun ε => denomP ε * Q2P ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε ^ 2 *
        (252 * ε ^ 5 - 784 * ε ^ 4 + 560 * ε ^ 3 - 33 * ε + 88) / 3)
    · fun_prop
    · intro ε
      simp [dP, lowP, qP, bP, vP, denomP, Q2P]
      ring
  have hQ2local :
      (fun ε => ((d ε - low ε) * q ε - x4 ε * b ε * v ε) / denom ε) =₅ Q2P :=
    eqModPow_div_approx hQ2num hdenom hQ2poly
      (by fun_prop) (by fun_prop) hdenomcont hdenom0
  let U2P : ℝ → ℝ := fun ε => 2 + (16 / 3) * ε ^ 3 - 9 * ε ^ 4
  have hbq := hb.mul hq (by fun_prop) hqcont
  have hdlowv := (hd.sub hlow).mul hv (by fun_prop) hvcont
  have hU2num :
      (fun ε => b ε * q ε + (d ε - low ε) * v ε) =₅
        (fun ε => bP ε * qP ε + (dP ε - lowP ε) * vP ε) :=
    hbq.add hdlowv
  have hU2poly :
      (fun ε => bP ε * qP ε + (dP ε - lowP ε) * vP ε) =₅
        (fun ε => denomP ε * U2P ε) := by
    apply EqModPow.of_factor
      (q := fun ε => -ε * (27 * ε ^ 2 - 166 * ε + 288) / 3)
    · fun_prop
    · intro ε
      simp [bP, qP, dP, lowP, vP, denomP, U2P]
      ring
  have hU2local :
      (fun ε => (b ε * q ε + (d ε - low ε) * v ε) / denom ε) =₅ U2P :=
    eqModPow_div_approx hU2num hdenom hU2poly
      (by fun_prop) (by fun_prop) hdenomcont hdenom0
  have hhighFormula : ∀ ε,
      RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) = high ε := by
    intro ε
    simp only [high, A, E, gap, rad, RealSymmetric2.high.eq_1,
      RealSymmetric2.gap.eq_1]
  have hlowFormula : ∀ ε,
      RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε) = low ε := by
    intro ε
    simp only [low, A, E, gap, rad, RealSymmetric2.low.eq_1,
      RealSymmetric2.gap.eq_1]
  have hdenomFormula : ∀ ε,
      RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) = denom ε := by
    intro ε
    simp only [denom, denomRad, low, A, E, gap, rad, RealSymmetric2.lowDenom.eq_1,
      RealSymmetric2.low.eq_1, RealSymmetric2.gap.eq_1]
  have hspectralLRaw : ∀ ε,
      (DFP.SecondLeg.spectralFactors ε 2 1).1 =
        (a ε * d ε - b ε ^ 2) /
          RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.SecondLeg.spectralFactors.eq_1]
  have hspectralHRaw : ∀ ε,
      (DFP.SecondLeg.spectralFactors ε 2 1).2 =
        RealSymmetric2.high (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.SecondLeg.spectralFactors.eq_1]
  have hgradientQRaw : ∀ ε,
      (DFP.SecondLeg.gradientFactors ε 2 1).1 =
        ((d ε - RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε)) * q ε -
          x4 ε * b ε * v ε) /
            RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.SecondLeg.gradientFactors.eq_1]
  have hgradientURaw : ∀ ε,
      (DFP.SecondLeg.gradientFactors ε 2 1).2 =
        (b ε * q ε +
          (d ε - RealSymmetric2.low (x4 ε * a ε) (x2 ε * b ε) (d ε)) * v ε) /
            RealSymmetric2.lowDenom (x4 ε * a ε) (x2 ε * b ε) (d ε) := by
    intro ε
    rw [DFP.SecondLeg.gradientFactors.eq_1]
  have hL2 :
      (fun ε : ℝ => (DFP.SecondLeg.spectralFactors ε 2 1).1) =₅ L2P :=
    eqModPow_congr_of_eq hL2local
      (fun ε => by rw [hspectralLRaw ε, hhighFormula ε]) (fun _ => rfl)
  have hH2 :
      (fun ε : ℝ => (DFP.SecondLeg.spectralFactors ε 2 1).2) =₅ highP :=
    eqModPow_congr_of_eq hhigh
      (fun ε => by rw [hspectralHRaw ε, hhighFormula ε]) (fun _ => rfl)
  have hQ2 :
      (fun ε : ℝ => (DFP.SecondLeg.gradientFactors ε 2 1).1) =₅ Q2P :=
    eqModPow_congr_of_eq hQ2local
      (fun ε => by rw [hgradientQRaw ε, hlowFormula ε, hdenomFormula ε])
      (fun _ => rfl)
  have hU2 :
      (fun ε : ℝ => (DFP.SecondLeg.gradientFactors ε 2 1).2) =₅ U2P :=
    eqModPow_congr_of_eq hU2local
      (fun ε => by rw [hgradientURaw ε, hlowFormula ε, hdenomFormula ε])
      (fun _ => rfl)
  let L2 : ℝ → ℝ := fun ε => (DFP.SecondLeg.spectralFactors ε 2 1).1
  let H2 : ℝ → ℝ := fun ε => (DFP.SecondLeg.spectralFactors ε 2 1).2
  let Q2 : ℝ → ℝ := fun ε => (DFP.SecondLeg.gradientFactors ε 2 1).1
  let U2 : ℝ → ℝ := fun ε => (DFP.SecondLeg.gradientFactors ε 2 1).2
  have hL2' : L2 =₅ L2P := by simpa [L2] using hL2
  have hH2' : H2 =₅ highP := by simpa [H2] using hH2
  have hQ2' : Q2 =₅ Q2P := by simpa [Q2] using hQ2
  have hU2' : U2 =₅ U2P := by simpa [U2] using hU2
  have hfac2 : ContinuousAt (fun ε : ℝ => DFP.SecondLeg.factors ε 2 1) 0 := by
    have hall := DFP.SecondLeg.factorsAnalytic.continuousAt.comp (f := path) hpath
    simpa [Function.comp_def, path] using hall
  have hL2cont : ContinuousAt L2 0 := by
    simpa only [L2, DFP.SecondLeg.factors.eq_1] using hfac2.fst.fst
  have hH2cont : ContinuousAt H2 0 := by
    simpa only [H2, DFP.SecondLeg.factors.eq_1] using hfac2.fst.snd
  have hQ2cont : ContinuousAt Q2 0 := by
    simpa only [Q2, DFP.SecondLeg.factors.eq_1] using hfac2.snd.fst.fst
  have hU2cont : ContinuousAt U2 0 := by
    simpa only [U2, DFP.SecondLeg.factors.eq_1] using hfac2.snd.fst.snd
  have hfactorBase := DFP.SecondLeg.factorsBase
  have hL2base : L2 0 = 2 := by
    simpa only [L2, DFP.SecondLeg.factors.eq_1] using congrArg (fun z => z.1.1) hfactorBase
  have hH2base : H2 0 = 1 := by
    simpa only [H2, DFP.SecondLeg.factors.eq_1] using congrArg (fun z => z.1.2) hfactorBase
  have hQ2base : Q2 0 = 1 := by
    simpa only [Q2, DFP.SecondLeg.factors.eq_1] using congrArg (fun z => z.2.1.1) hfactorBase
  have hU2base : U2 0 = 2 := by
    simpa only [U2, DFP.SecondLeg.factors.eq_1] using congrArg (fun z => z.2.1.2) hfactorBase
  let RP : ℝ → ℝ := fun ε => 1 - (50 / 3) * ε ^ 3 + 3 * ε ^ 4
  have hRnum := hL2'.mul hQ2' (by fun_prop) hQ2cont
  have hRden := hH2'.mul hU2' (by fun_prop) hU2cont
  have hRpoly :
      (fun ε => L2P ε * Q2P ε) =₅
        (fun ε => (highP ε * U2P ε) * RP ε) := by
    apply EqModPow.of_factor
      (q := fun ε => 2 * ε *
        (972 * ε ^ 5 - 5976 * ε ^ 4 + 3200 * ε ^ 3 - 171 * ε ^ 2 -
          288 * ε + 1408) / 9)
    · fun_prop
    · intro ε
      simp [L2P, Q2P, highP, U2P, RP]
      ring
  have hR :
      (fun ε => L2 ε * Q2 ε / (H2 ε * U2 ε)) =₅ RP :=
    eqModPow_div_approx hRnum hRden hRpoly
      (by fun_prop) (by fun_prop) (hH2cont.mul hU2cont)
      (by norm_num [hH2base, hU2base])
  let PP : ℝ → ℝ := fun ε => 2 + (116 / 3) * ε ^ 3 - 2 * ε ^ 4
  have hU2sq := hU2'.mul hU2' (by fun_prop) hU2cont
  have hQ2sq := hQ2'.mul hQ2' (by fun_prop) hQ2cont
  have hPnum := hH2'.mul hU2sq (by fun_prop) (hU2cont.mul hU2cont)
  have hPden := hL2'.mul hQ2sq (by fun_prop) (hQ2cont.mul hQ2cont)
  have hPpoly :
      (fun ε => highP ε * U2P ε ^ 2) =₅
        (fun ε => (L2P ε * Q2P ε ^ 2) * PP ε) := by
    apply EqModPow.of_factor
      (q := fun ε => ε *
        (7605 * ε ^ 10 - 156156 * ε ^ 9 + 176436 * ε ^ 8 -
          8424 * ε ^ 6 + 33600 * ε ^ 5 - 61200 * ε ^ 4 +
          2048 * ε ^ 3 + 1260 * ε ^ 2 - 912 * ε + 5968) / 9)
    · fun_prop
    · intro ε
      simp [highP, U2P, L2P, Q2P, PP]
      ring
  have hP :
      (fun ε => H2 ε * U2 ε ^ 2 / (L2 ε * Q2 ε ^ 2)) =₅ PP :=
    eqModPow_div_approx
      (eqModPow_congr_of_eq hPnum (fun ε => by ring) (fun ε => by ring))
      (eqModPow_congr_of_eq hPden (fun ε => by ring) (fun ε => by ring))
      hPpoly (by fun_prop) (by fun_prop)
      (hL2cont.mul (hQ2cont.pow 2))
      (by norm_num [hL2base, hQ2base])
  have hradiusFormula : ∀ ε,
      radiusFactor ε 2 1 = L2 ε * Q2 ε / (H2 ε * U2 ε) := by
    intro ε
    simp only [DFP.TwoLeg.radiusFactor.eq_1, DFP.SecondLeg.canonicalFactors.eq_1,
      L2, H2, Q2, U2]
  have hshapeFormula : ∀ ε,
      (stateMap (ε, 2, 1)).2.1 =
        H2 ε * U2 ε ^ 2 / (L2 ε * Q2 ε ^ 2) := by
    intro ε
    simp only [DFP.TwoLeg.stateMap_apply, DFP.SecondLeg.canonicalFactors.eq_1,
      L2, H2, Q2, U2]
  have hhighStateFormula : ∀ ε,
      (stateMap (ε, 2, 1)).2.2 = H2 ε := by
    intro ε
    simp only [DFP.TwoLeg.stateMap_apply, H2]
  exact ⟨eqModPow_congr_of_eq hR hradiusFormula (fun _ => rfl),
    eqModPow_congr_of_eq hP hshapeFormula (fun _ => rfl),
    eqModPow_congr_of_eq hH2' hhighStateFormula (fun _ => rfl)⟩
end DFP.TwoLeg
