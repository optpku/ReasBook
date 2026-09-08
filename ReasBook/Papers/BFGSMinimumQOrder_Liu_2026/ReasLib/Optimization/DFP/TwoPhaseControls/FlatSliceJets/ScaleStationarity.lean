module

public import ReasLib.Analysis.Calculus.ContDiff.CrossDerivative
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

private lemma firstLegFactorsScale_hasDerivAt (p h : ℝ) :
    HasDerivAt
      (fun ε : ℝ ↦ (DFP.FirstLeg.spectralFactors ε p h,
        DFP.FirstLeg.gradientFactors ε p h))
      ((0, 0), (0, 0)) 0 := by
  let X : ℝ → ℝ := fun ε ↦ ε
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let P : ℝ → ℝ := fun _ ↦ p
  let H : ℝ → ℝ := fun _ ↦ h
  have hX : HasDerivAt X 1 0 := hasDerivAt_id 0
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have htwo : HasDerivAt two 0 0 := hasDerivAt_const 0 2
  have hthree : HasDerivAt three 0 0 := hasDerivAt_const 0 3
  have hP : HasDerivAt P 0 0 := hasDerivAt_const 0 p
  have hH : HasDerivAt H 0 0 := hasDerivAt_const 0 h
  let onePlusCube := one + X ^ 3
  let onePlus := one + X
  have honePlusCube : HasDerivAt onePlusCube 0 0 := by
    exact (hone.add (hX.pow 3)).congr_deriv (g' := 0) (by norm_num)
  have honePlus : HasDerivAt onePlus 1 0 := by
    exact (hone.add hX).congr_deriv (g' := 1) (by norm_num)
  let B := one + ((two * X ^ 3) + X ^ 4)
  have hB : HasDerivAt B 0 0 := by
    exact (hone.add (((htwo.mul (hX.pow 3))).add (hX.pow 4))).congr_deriv
      (g' := 0) (by norm_num)
  let C := onePlusCube ^ 2 + (P * X ^ 6) * onePlus ^ 2
  have hC : HasDerivAt C 0 0 := by
    exact ((honePlusCube.pow 2).add
      ((hP.mul (hX.pow 6)).mul (honePlus.pow 2))).congr_deriv
        (g' := 0) (by norm_num)
  have hB_ne : B 0 ≠ 0 := by norm_num [B, one, two, X]
  have hC_ne : C 0 ≠ 0 := by norm_num [C, onePlusCube, onePlus, one, P, X]
  let a := H * P - (((H * P ^ 2) * X ^ 6) * onePlus ^ 2) / C + one / B
  let b := one / B - ((((H * P) * X ^ 3) * onePlus) * onePlusCube) / C
  let d := H - (H * onePlusCube ^ 2) / C + one / B
  let q := one - (((two * (P + one)) * X ^ 3) * onePlus) / (three * B)
  let v := P - ((two * (P + one)) * onePlusCube) / (three * B)
  have ha : HasDerivAt a 0 0 := by
    exact (((hH.mul hP).sub
      ((((hH.mul (hP.pow 2)).mul (hX.pow 6)).mul (honePlus.pow 2)).div hC hC_ne)).add
        (hone.div hB hB_ne)).congr_deriv (g' := 0)
          (by norm_num [a, B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hb : HasDerivAt b 0 0 := by
    exact ((hone.div hB hB_ne).sub
      (((((hH.mul hP).mul (hX.pow 3)).mul honePlus).mul honePlusCube).div hC hC_ne)).congr_deriv
        (g' := 0)
          (by norm_num [b, B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hd : HasDerivAt d 0 0 := by
    exact ((hH.sub ((hH.mul (honePlusCube.pow 2)).div hC hC_ne)).add
      (hone.div hB hB_ne)).congr_deriv (g' := 0)
        (by norm_num [d, B, C, onePlusCube, one, two, P, H, X])
  have hq : HasDerivAt q 0 0 := by
    exact (hone.sub (((((htwo.mul (hP.add hone)).mul (hX.pow 3)).mul honePlus)).div
      (hthree.mul hB) (by norm_num [B, one, two, three, X]))).congr_deriv
        (g' := 0)
          (by norm_num [q, B, onePlus, one, two, three, P, X])
  have hv : HasDerivAt v 0 0 := by
    exact (hP.sub ((((htwo.mul (hP.add hone)).mul honePlusCube)).div
      (hthree.mul hB) (by norm_num [B, one, two, three, X]))).congr_deriv
        (g' := 0)
          (by norm_num [v, B, onePlusCube, one, two, three, P, X])
  let A := X ^ 4 * a
  let E := X ^ 2 * b
  have hA : HasDerivAt A 0 0 := by
    exact ((hX.pow 4).mul ha).congr_deriv (g' := 0) (by norm_num [A, X])
  have hE : HasDerivAt E 0 0 := by
    exact ((hX.pow 2).mul hb).congr_deriv (g' := 0) (by norm_num [E, X])
  let rad := (d - A) ^ 2 + (fun ε ↦ 4 * (E ^ 2) ε)
  have hrad : HasDerivAt rad 0 0 := by
    exact (((hd.sub hA).pow 2).add ((hE.pow 2).const_mul 4)).congr_deriv
      (g' := 0)
        (by norm_num [rad, d, A, E, a, b, B, C, onePlusCube, onePlus,
          one, two, P, H, X])
  have hrad_ne : rad 0 ≠ 0 := by
    norm_num [rad, d, A, E, a, b, B, C, onePlusCube, onePlus,
      one, two, P, H, X]
  let gap := fun ε ↦ Real.sqrt (rad ε)
  have hgap : HasDerivAt gap 0 0 := by
    exact (hrad.sqrt hrad_ne).congr_deriv (g' := 0)
      (by norm_num [gap, rad, d, A, E, a, b, B, C, onePlusCube,
        onePlus, one, two, P, H, X])
  let high := (A + d + gap) / two
  let low := (A + d - gap) / two
  have hhigh : HasDerivAt high 0 0 := by
    exact (((hA.add hd).add hgap).div htwo (by norm_num [two])).congr_deriv
      (g' := 0) (by norm_num [high, two])
  have hlow : HasDerivAt low 0 0 := by
    exact (((hA.add hd).sub hgap).div htwo (by norm_num [two])).congr_deriv
      (g' := 0) (by norm_num [low, two])
  let denomRad := (d - low) ^ 2 + E ^ 2
  have hdenomRad : HasDerivAt denomRad 0 0 := by
    exact (((hd.sub hlow).pow 2).add (hE.pow 2)).congr_deriv
      (g' := 0)
        (by norm_num [denomRad, d, low, high, gap, rad, A, E, a, b,
          B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hdenomRad_ne : denomRad 0 ≠ 0 := by
    norm_num [denomRad, d, low, high, gap, rad, A, E, a, b,
      B, C, onePlusCube, onePlus, one, two, P, H, X]
  let denom := fun ε ↦ Real.sqrt (denomRad ε)
  have hdenom : HasDerivAt denom 0 0 := by
    exact (hdenomRad.sqrt hdenomRad_ne).congr_deriv (g' := 0)
      (by norm_num [denom, denomRad, d, low, high, gap, rad, A, E, a, b,
        B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hhigh_ne : high 0 ≠ 0 := by
    norm_num [high, gap, rad, d, A, E, a, b, B, C, onePlusCube,
      onePlus, one, two, P, H, X]
  have hdenom_ne : denom 0 ≠ 0 := by
    norm_num [denom, denomRad, d, low, high, gap, rad, A, E, a, b,
      B, C, onePlusCube, onePlus, one, two, P, H, X]
  let spectralLow := (a * d - b ^ 2) / high
  let gradientLow := ((d - low) * q - (X ^ 4 * b) * v) / denom
  let gradientHigh := (b * q + (d - low) * v) / denom
  have hspectralLow : HasDerivAt spectralLow 0 0 := by
    exact (((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh_ne).congr_deriv
      (g' := 0)
        (by norm_num [spectralLow, a, b, d, high, gap, rad, A, E,
          B, C, onePlusCube, onePlus, one, two, P, H, X])
  have hgradientLow : HasDerivAt gradientLow 0 0 := by
    exact ((((hd.sub hlow).mul hq).sub (((hX.pow 4).mul hb).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientLow, a, b, d, q, v, low, high, gap, rad,
          A, E, denom, denomRad, B, C, onePlusCube, onePlus, one, two,
          three, P, H, X])
  have hgradientHigh : HasDerivAt gradientHigh 0 0 := by
    exact (((hb.mul hq).add ((hd.sub hlow).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientHigh, a, b, d, q, v, low, high, gap, rad,
          A, E, denom, denomRad, B, C, onePlusCube, onePlus, one, two,
          three, P, H, X])
  have hfactorData := (hspectralLow.prodMk hhigh).prodMk
    (hgradientLow.prodMk hgradientHigh)
  apply hfactorData.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε ↦ by
    simp [DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom, spectralLow, gradientLow, gradientHigh, denom,
      denomRad, low, high, gap, rad, A, E, a, b, d, q, v, B, C,
      onePlusCube, onePlus, one, two, three, P, H, X]
    ring_nf
    simp)

private lemma firstLeg_spectralFactors_zero (p h : ℝ) :
    DFP.FirstLeg.spectralFactors 0 p h = (h * p, 1) := by
  norm_num [DFP.FirstLeg.spectralFactors, RealSymmetric2.low,
    RealSymmetric2.high, RealSymmetric2.gap]

private lemma firstLeg_gradientFactors_zero (p h : ℝ) :
    DFP.FirstLeg.gradientFactors 0 p h = (1, (p + 1) / 3) := by
  norm_num [DFP.FirstLeg.gradientFactors, RealSymmetric2.low,
    RealSymmetric2.gap, RealSymmetric2.lowDenom]
  ring

private lemma secondLegFactorsScale_hasDerivAt (p h : ℝ)
    (hp : 0 < p) (hh : 0 < h) :
    HasDerivAt (fun ε : ℝ ↦ DFP.SecondLeg.factors ε p h)
      ((0, 0), (0, 0), (0, 0)) 0 := by
  let X : ℝ → ℝ := fun ε ↦ ε
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let L := fun ε ↦ (DFP.FirstLeg.spectralFactors ε p h).1
  let H := fun ε ↦ (DFP.FirstLeg.spectralFactors ε p h).2
  let Q := fun ε ↦ (DFP.FirstLeg.gradientFactors ε p h).1
  let U := fun ε ↦ (DFP.FirstLeg.gradientFactors ε p h).2
  have hX : HasDerivAt X 1 0 := hasDerivAt_id 0
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have htwo : HasDerivAt two 0 0 := hasDerivAt_const 0 2
  have hthree : HasDerivAt three 0 0 := hasDerivAt_const 0 3
  have hspectral : HasDerivAt
      (fun ε ↦ DFP.FirstLeg.spectralFactors ε p h) (0, 0) 0 := by
    simpa using
      (firstLegFactorsScale_hasDerivAt p h).hasFDerivAt.fst.hasDerivAt
  have hgradient : HasDerivAt
      (fun ε ↦ DFP.FirstLeg.gradientFactors ε p h) (0, 0) 0 := by
    simpa using
      (firstLegFactorsScale_hasDerivAt p h).hasFDerivAt.snd.hasDerivAt
  have hL : HasDerivAt L 0 0 := by
    simpa [L] using hspectral.hasFDerivAt.fst.hasDerivAt
  have hH : HasDerivAt H 0 0 := by
    simpa [H] using hspectral.hasFDerivAt.snd.hasDerivAt
  have hQ : HasDerivAt Q 0 0 := by
    simpa [Q] using hgradient.hasFDerivAt.fst.hasDerivAt
  have hU : HasDerivAt U 0 0 := by
    simpa [U] using hgradient.hasFDerivAt.snd.hasDerivAt
  have hspectralBase := firstLeg_spectralFactors_zero p h
  have hgradientBase := firstLeg_gradientFactors_zero p h
  have hL_pos : 0 < L 0 := by
    simp only [L, hspectralBase]
    exact mul_pos hh hp
  have hU_pos : 0 < U 0 := by
    simp only [U, hgradientBase]
    nlinarith
  have hL_ne : L 0 ≠ 0 := ne_of_gt hL_pos
  have hU_ne : U 0 ≠ 0 := ne_of_gt hU_pos
  let w₁ := X * L * Q - (two * H) * U
  let w₂ := H * U - ((two * X ^ 3) * L) * Q
  have hw₁ : HasDerivAt w₁ (h * p) 0 := by
    exact (((hX.mul hL).mul hQ).sub ((htwo.mul hH).mul hU)).congr_deriv
      (g' := h * p)
        (by norm_num [w₁, X, L, H, Q, U, hspectralBase, hgradientBase])
  have hw₂ : HasDerivAt w₂ 0 0 := by
    exact ((hH.mul hU).sub (((htwo.mul (hX.pow 3)).mul hL).mul hQ)).congr_deriv
      (g' := 0)
        (by norm_num [w₂, X, L, H, Q, U, hspectralBase, hgradientBase])
  let beta := (((X ^ 3 * L) * Q) * w₁) + (H * U) * w₂
  let gamma := ((X ^ 6 * L) * w₁ ^ 2) + H * w₂ ^ 2
  let delta := L * Q ^ 2 + H * U ^ 2
  have hbeta : HasDerivAt beta 0 0 := by
    exact (((((hX.pow 3).mul hL).mul hQ).mul hw₁).add
      ((hH.mul hU).mul hw₂)).congr_deriv (g' := 0)
        (by norm_num [beta, w₁, w₂, X, L, H, Q, U,
          hspectralBase, hgradientBase])
  have hgamma : HasDerivAt gamma 0 0 := by
    exact ((((hX.pow 6).mul hL).mul (hw₁.pow 2)).add
      (hH.mul (hw₂.pow 2))).congr_deriv (g' := 0)
        (by norm_num [gamma, w₁, w₂, X, L, H, Q, U,
          hspectralBase, hgradientBase])
  have hdelta : HasDerivAt delta 0 0 := by
    exact ((hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))).congr_deriv
      (g' := 0)
        (by norm_num [delta, L, H, Q, U, hspectralBase, hgradientBase])
  have hbeta_zero : beta 0 = U 0 ^ 2 := by
    simp [beta, w₁, w₂, X, L, H, Q, U, hspectralBase, hgradientBase]
    ring
  have hgamma_zero : gamma 0 = U 0 ^ 2 := by
    simp [gamma, w₁, w₂, X, L, H, Q, U, hspectralBase, hgradientBase]
  have hdelta_zero : delta 0 = L 0 + U 0 ^ 2 := by
    simp [delta, L, H, Q, U, hspectralBase, hgradientBase]
  have hbeta_ne : beta 0 ≠ 0 := by
    rw [hbeta_zero]
    exact pow_ne_zero 2 hU_ne
  have hgamma_ne : gamma 0 ≠ 0 := by
    rw [hgamma_zero]
    exact pow_ne_zero 2 hU_ne
  let a := L - (((X ^ 6 * L ^ 2) * w₁ ^ 2) / gamma) +
    (L ^ 2 * Q ^ 2) / beta
  let b := -((((X ^ 3 * L) * H) * w₁ * w₂) / gamma) +
    ((L * Q) * H * U) / beta
  let d := H - (H ^ 2 * w₂ ^ 2) / gamma + (H ^ 2 * U ^ 2) / beta
  let q := Q - (((X ^ 3 * delta) * w₁) / (three * beta))
  let v := U - (delta * w₂) / (three * beta)
  have ha : HasDerivAt a 0 0 := by
    exact ((hL.sub (((((hX.pow 6).mul (hL.pow 2)).mul (hw₁.pow 2)).div
      hgamma hgamma_ne))).add (((hL.pow 2).mul (hQ.pow 2)).div hbeta hbeta_ne)).congr_deriv
        (g' := 0) (by norm_num)
  have hb : HasDerivAt b 0 0 := by
    exact ((((((((hX.pow 3).mul hL).mul hH).mul hw₁).mul hw₂).div
      hgamma hgamma_ne).neg).add ((((hL.mul hQ).mul hH).mul hU).div
        hbeta hbeta_ne)).congr_deriv (g' := 0) (by norm_num)
  have hd : HasDerivAt d 0 0 := by
    exact ((hH.sub (((hH.pow 2).mul (hw₂.pow 2)).div hgamma hgamma_ne)).add
      (((hH.pow 2).mul (hU.pow 2)).div hbeta hbeta_ne)).congr_deriv
        (g' := 0) (by norm_num)
  have hq : HasDerivAt q 0 0 := by
    exact (hQ.sub ((((hX.pow 3).mul hdelta).mul hw₁).div
      (hthree.mul hbeta) (mul_ne_zero (by norm_num) hbeta_ne))).congr_deriv
        (g' := 0) (by norm_num)
  have hv : HasDerivAt v 0 0 := by
    exact (hU.sub ((hdelta.mul hw₂).div (hthree.mul hbeta)
      (mul_ne_zero (by norm_num) hbeta_ne))).congr_deriv
        (g' := 0) (by norm_num)
  have ha_zero : a 0 = L 0 + L 0 ^ 2 / U 0 ^ 2 := by
    rw [show a 0 =
      L 0 - X 0 ^ 6 * L 0 ^ 2 * w₁ 0 ^ 2 / gamma 0 +
        L 0 ^ 2 * Q 0 ^ 2 / beta 0 by rfl]
    rw [hbeta_zero]
    simp [X, Q, hgradientBase]
  have hb_zero : b 0 = L 0 / U 0 := by
    rw [show b 0 =
      -(X 0 ^ 3 * L 0 * H 0 * w₁ 0 * w₂ 0 / gamma 0) +
        L 0 * Q 0 * H 0 * U 0 / beta 0 by rfl]
    rw [hbeta_zero]
    simp [X, H, Q, hspectralBase, hgradientBase]
    field_simp [hU_ne]
  have hd_zero : d 0 = 1 := by
    rw [show d 0 =
      H 0 - H 0 ^ 2 * w₂ 0 ^ 2 / gamma 0 +
        H 0 ^ 2 * U 0 ^ 2 / beta 0 by rfl]
    rw [hbeta_zero, hgamma_zero]
    simp [w₂, X, H, hspectralBase, hU_ne]
  have hq_zero : q 0 = 1 := by
    simp [q, X, Q, hgradientBase]
  have hv_zero : v 0 = U 0 - (L 0 + U 0 ^ 2) / (3 * U 0) := by
    rw [show v 0 = U 0 - delta 0 * w₂ 0 / (three 0 * beta 0) by rfl]
    rw [hdelta_zero, hbeta_zero]
    simp [w₂, X, H, three, hspectralBase]
    field_simp [hU_ne]
  let A := X ^ 4 * a
  let E := X ^ 2 * b
  have hA : HasDerivAt A 0 0 := by
    exact ((hX.pow 4).mul ha).congr_deriv (g' := 0) (by norm_num [A, X])
  have hE : HasDerivAt E 0 0 := by
    exact ((hX.pow 2).mul hb).congr_deriv (g' := 0) (by norm_num [E, X])
  let rad := (d - A) ^ 2 + (fun ε ↦ 4 * (E ^ 2) ε)
  have hrad : HasDerivAt rad 0 0 := by
    exact (((hd.sub hA).pow 2).add ((hE.pow 2).const_mul 4)).congr_deriv
      (g' := 0) (by norm_num)
  have hrad_zero : rad 0 = 1 := by
    simp [rad, A, E, X, hd_zero]
  have hrad_ne : rad 0 ≠ 0 := by rw [hrad_zero]; norm_num
  let gap := fun ε ↦ Real.sqrt (rad ε)
  have hgap : HasDerivAt gap 0 0 := by
    exact (hrad.sqrt hrad_ne).congr_deriv (g' := 0)
      (by simp)
  have hgap_zero : gap 0 = 1 := by
    rw [show gap 0 = Real.sqrt (rad 0) by rfl, hrad_zero]
    norm_num
  let high := (A + d + gap) / two
  let low := (A + d - gap) / two
  have hhigh : HasDerivAt high 0 0 := by
    exact (((hA.add hd).add hgap).div htwo (by norm_num [two])).congr_deriv
      (g' := 0) (by norm_num)
  have hlow : HasDerivAt low 0 0 := by
    exact (((hA.add hd).sub hgap).div htwo (by norm_num [two])).congr_deriv
      (g' := 0) (by norm_num)
  have hhigh_zero : high 0 = 1 := by
    simp [high, A, X, hd_zero, hgap_zero, two]
  have hlow_zero : low 0 = 0 := by
    simp [low, A, X, hd_zero, hgap_zero, two]
  let denomRad := (d - low) ^ 2 + E ^ 2
  have hdenomRad : HasDerivAt denomRad 0 0 := by
    exact (((hd.sub hlow).pow 2).add (hE.pow 2)).congr_deriv
      (g' := 0) (by norm_num)
  have hdenomRad_zero : denomRad 0 = 1 := by
    simp [denomRad, hd_zero, hlow_zero, E, X]
  have hdenomRad_ne : denomRad 0 ≠ 0 := by
    rw [hdenomRad_zero]
    norm_num
  let denom := fun ε ↦ Real.sqrt (denomRad ε)
  have hdenom : HasDerivAt denom 0 0 := by
    exact (hdenomRad.sqrt hdenomRad_ne).congr_deriv (g' := 0)
      (by simp)
  have hdenom_zero : denom 0 = 1 := by
    rw [show denom 0 = Real.sqrt (denomRad 0) by rfl, hdenomRad_zero]
    norm_num
  have hhigh_ne : high 0 ≠ 0 := by rw [hhigh_zero]; norm_num
  have hdenom_ne : denom 0 ≠ 0 := by rw [hdenom_zero]; norm_num
  let spectralLow := (a * d - b ^ 2) / high
  let gradientLow := ((d - low) * q - (X ^ 4 * b) * v) / denom
  let gradientHigh := (b * q + (d - low) * v) / denom
  have hspectralLow : HasDerivAt spectralLow 0 0 := by
    exact (((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh_ne).congr_deriv
      (g' := 0) (by norm_num)
  have hgradientLow : HasDerivAt gradientLow 0 0 := by
    exact ((((hd.sub hlow).mul hq).sub (((hX.pow 4).mul hb).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0) (by norm_num)
  have hgradientHigh : HasDerivAt gradientHigh 0 0 := by
    exact (((hb.mul hq).add ((hd.sub hlow).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0) (by norm_num)
  have hspectralLow_zero : spectralLow 0 = L 0 := by
    change (a 0 * d 0 - b 0 ^ 2) / high 0 = L 0
    rw [hd_zero, hhigh_zero, ha_zero, hb_zero]
    norm_num
    field_simp [hU_ne]
    ring
  have hgradientLow_zero : gradientLow 0 = 1 := by
    simp [gradientLow, hd_zero, hlow_zero, hq_zero, X, hdenom_zero]
  have hgradientHigh_zero :
      gradientHigh 0 = 2 * (L 0 + U 0 ^ 2) / (3 * U 0) := by
    change (b 0 * q 0 + (d 0 - low 0) * v 0) / denom 0 = _
    rw [hq_zero, hd_zero, hlow_zero, hdenom_zero, hb_zero, hv_zero]
    norm_num
    field_simp [hU_ne]
    ring
  have hgradientHigh_pos : 0 < gradientHigh 0 := by
    rw [hgradientHigh_zero]
    positivity
  have hspectralLow_ne : spectralLow 0 ≠ 0 := by
    rw [hspectralLow_zero]
    exact hL_ne
  have hgradientLow_ne : gradientLow 0 ≠ 0 := by
    rw [hgradientLow_zero]
    norm_num
  have hgradientHigh_ne : gradientHigh 0 ≠ 0 := ne_of_gt hgradientHigh_pos
  let canonicalRadius := (spectralLow * gradientLow) / (high * gradientHigh)
  let canonicalShape := (high * gradientHigh ^ 2) /
    (spectralLow * gradientLow ^ 2)
  have hcanonicalRadius : HasDerivAt canonicalRadius 0 0 := by
    exact ((hspectralLow.mul hgradientLow).div (hhigh.mul hgradientHigh)
      (mul_ne_zero hhigh_ne hgradientHigh_ne)).congr_deriv
        (g' := 0) (by norm_num)
  have hcanonicalShape : HasDerivAt canonicalShape 0 0 := by
    exact ((hhigh.mul (hgradientHigh.pow 2)).div
      (hspectralLow.mul (hgradientLow.pow 2))
      (mul_ne_zero hspectralLow_ne (pow_ne_zero 2 hgradientLow_ne))).congr_deriv
        (g' := 0) (by norm_num)
  have hfactorData := (hspectralLow.prodMk hhigh).prodMk
    ((hgradientLow.prodMk hgradientHigh).prodMk
      (hcanonicalRadius.prodMk hcanonicalShape))
  apply hfactorData.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε ↦ by
    simp [DFP.SecondLeg.factors, DFP.SecondLeg.spectralFactors,
      DFP.SecondLeg.gradientFactors, DFP.SecondLeg.canonicalFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom, canonicalRadius, canonicalShape, spectralLow,
      gradientLow, gradientHigh, denom, denomRad, low, high, gap, rad, A, E,
      a, b, d, q, v, beta, gamma, delta, w₁, w₂, X, L, H, Q, U, two,
      three])

/-- Helper for Infrastructure I.16a and Lemma 4.15: on a positive transverse
slice, every second-leg removable factor is stationary in the signed scale. The
wrapper exposes the source calculation without its local algebraic scaffolding. -/
theorem secondLegFactors_scale_hasDerivAt (p h : ℝ)
    (hp : 0 < p) (hh : 0 < h) :
    HasDerivAt (fun ε : ℝ ↦ DFP.SecondLeg.factors ε p h)
      ((0, 0), (0, 0), (0, 0)) 0 := by
  exact secondLegFactorsScale_hasDerivAt p h hp hh

/-- The normalized radius factor is stationary in the signed-scale direction
at every positive point of the zero-scale slice. -/
theorem radiusFactor_scale_hasDerivAt (p h : ℝ) (hp : 0 < p) (hh : 0 < h) :
    HasDerivAt (fun ε : ℝ ↦ radiusFactor ε p h) 0 0 := by
  have hcanonicalRaw :=
    (secondLegFactorsScale_hasDerivAt p h hp hh).hasFDerivAt.snd.snd.hasDerivAt
  have hcanonical := hcanonicalRaw.congr_deriv (g' := ((0, 0) : ℝ × ℝ)) (by norm_num)
  have hradiusRaw := hcanonical.hasFDerivAt.fst.hasDerivAt
  have hradius := hradiusRaw.congr_deriv (g' := (0 : ℝ)) (by norm_num)
  simpa only [DFP.SecondLeg.factors, radiusFactor] using hradius

/-- The recovered shape is stationary in the signed-scale direction at every
positive point of the zero-scale slice. -/
theorem stateMap_shape_scale_hasDerivAt (p h : ℝ) (hp : 0 < p) (hh : 0 < h) :
    HasDerivAt (fun ε : ℝ ↦ (stateMap (ε, p, h)).2.1) 0 0 := by
  have hcanonicalRaw :=
    (secondLegFactorsScale_hasDerivAt p h hp hh).hasFDerivAt.snd.snd.hasDerivAt
  have hcanonical := hcanonicalRaw.congr_deriv (g' := ((0, 0) : ℝ × ℝ)) (by norm_num)
  have hshapeRaw := hcanonical.hasFDerivAt.snd.hasDerivAt
  have hshape := hshapeRaw.congr_deriv (g' := (0 : ℝ)) (by norm_num)
  simpa only [DFP.SecondLeg.factors, stateMap] using hshape

/-- The recovered high coordinate is stationary in the signed-scale direction
at every positive point of the zero-scale slice. -/
theorem stateMap_high_scale_hasDerivAt (p h : ℝ) (hp : 0 < p) (hh : 0 < h) :
    HasDerivAt (fun ε : ℝ ↦ (stateMap (ε, p, h)).2.2) 0 0 := by
  have hspectralRaw :=
    (secondLegFactorsScale_hasDerivAt p h hp hh).hasFDerivAt.fst.hasDerivAt
  have hspectral := hspectralRaw.congr_deriv (g' := ((0, 0) : ℝ × ℝ)) (by norm_num)
  have hhighRaw := hspectral.hasFDerivAt.snd.hasDerivAt
  have hhigh := hhighRaw.congr_deriv (g' := (0 : ℝ)) (by norm_num)
  simpa only [DFP.SecondLeg.factors, stateMap] using hhigh

private theorem iteratedFDeriv_scale_transverse_eq_zero
    (f : (ℝ × ℝ × ℝ) → ℝ)
    (hf : AnalyticAt ℝ f (0, 2, 1))
    (hscale : ∀ p h : ℝ, 0 < p → 0 < h →
      HasDerivAt (fun ε : ℝ ↦ f (ε, p, h)) 0 0)
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2 f (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  let a : ℝ × ℝ × ℝ := (0, 2, 1)
  let u : ℝ × ℝ × ℝ := (1, 0, 0)
  let line : ℝ → ℝ × ℝ × ℝ := fun t ↦ a + t • v
  have hline : Tendsto line (𝓝 0) (𝓝 a) := by
    have hc : ContinuousAt line 0 := by
      dsimp only [line]
      fun_prop
    have hline_zero : line 0 = a := by simp [line]
    rw [← hline_zero]
    exact hc
  have hanalytic : ∀ᶠ t in 𝓝 (0 : ℝ), AnalyticAt ℝ f (line t) :=
    hline.eventually hf.eventually_analyticAt
  have hp_nhds : ∀ᶠ x in 𝓝 a, 0 < x.2.1 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) a := by fun_prop
    apply hc.eventually
    exact Ioi_mem_nhds (by norm_num [a])
  have hh_nhds : ∀ᶠ x in 𝓝 a, 0 < x.2.2 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) a := by fun_prop
    apply hc.eventually
    exact Ioi_mem_nhds (by norm_num [a])
  have hp_line : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (line t).2.1 :=
    hline.eventually hp_nhds
  have hh_line : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (line t).2.2 :=
    hline.eventually hh_nhds
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ f (a + t • v) u = 0 := by
    filter_upwards [hanalytic, hp_line, hh_line] with t hft hpt hht
    let x : ℝ × ℝ × ℝ := line t
    have hx_scale : x.1 = 0 := by
      simp [x, line, a, hv]
    have hx_eq : ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) = x := by
      ext <;> simp [hx_scale]
    have hinner : HasDerivAt
        (fun ε : ℝ ↦ ((ε, x.2.1, x.2.2) : ℝ × ℝ × ℝ)) u 0 := by
      have hpconst : HasDerivAt (fun _ : ℝ ↦ x.2.1) 0 0 :=
        hasDerivAt_const 0 x.2.1
      have hhconst : HasDerivAt (fun _ : ℝ ↦ x.2.2) 0 0 :=
        hasDerivAt_const 0 x.2.2
      simpa only [u, id_eq] using (hasDerivAt_id (0 : ℝ)).prodMk
        (hpconst.prodMk hhconst)
    have hft' : DifferentiableAt ℝ f ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) := by
      simpa only [hx_eq] using hft.differentiableAt
    have hchain := hft'.hasFDerivAt.comp_hasDerivAt 0 hinner
    have hstationary := hscale x.2.1 x.2.2 hpt hht
    have hvalue :
        fderiv ℝ f ((0, x.2.1, x.2.2) : ℝ × ℝ × ℝ) u = 0 :=
      hchain.unique hstationary
    change fderiv ℝ f x u = 0
    simpa only [hx_eq] using hvalue
  have hf2 : ContDiffAt ℝ 2 f (0, 2, 1) := hf.contDiffAt
  simpa only [a, u] using
    hf2.iteratedFDeriv_two_apply_eq_zero_of_eventually_fderiv_line_eq_zero
      ((1, 0, 0) : ℝ × ℝ × ℝ) v (by simpa only [a, u] using hzero)

/-- Helper for Infrastructure I.16a and Lemma 4.15: scale stationarity of an
analytic scalar family annihilates its scale/transverse mixed Hessian at the
canceled base point. -/
theorem iteratedFDeriv_scale_transverse_eq_zero_of_scaleStationarity
    (f : (ℝ × ℝ × ℝ) → ℝ)
    (hf : AnalyticAt ℝ f (0, 2, 1))
    (hscale : ∀ p h : ℝ, 0 < p → 0 < h →
      HasDerivAt (fun ε : ℝ ↦ f (ε, p, h)) 0 0)
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2 f (0, 2, 1)
      ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  exact iteratedFDeriv_scale_transverse_eq_zero f hf hscale v hv

/-- Every transverse mixed Hessian of the normalized radius with the scale
direction vanishes at the base point. -/
theorem radiusFactor_scale_transverse_cross_eq_zero
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦ radiusFactor x.1 x.2.1 x.2.2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  refine iteratedFDeriv_scale_transverse_eq_zero _ analyticAt_radiusFactor
    ?_ v hv
  intro p h hp hh
  exact radiusFactor_scale_hasDerivAt p h hp hh

/-- Every transverse mixed Hessian of the recovered shape with the scale
direction vanishes at the base point. -/
theorem stateMap_shape_scale_transverse_cross_eq_zero
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.1)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  have hf : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.1) (0, 2, 1) :=
    analyticAt_fst.comp (analyticAt_snd.comp stateMapAnalytic)
  refine iteratedFDeriv_scale_transverse_eq_zero _ hf ?_ v hv
  intro p h hp hh
  exact stateMap_shape_scale_hasDerivAt p h hp hh

/-- Every transverse mixed Hessian of the recovered high coordinate with the
scale direction vanishes at the base point. -/
theorem stateMap_high_scale_transverse_cross_eq_zero
    (v : ℝ × ℝ × ℝ) (hv : v.1 = 0) :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), v] = 0 := by
  have hf : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.2) (0, 2, 1) :=
    analyticAt_snd.comp (analyticAt_snd.comp stateMapAnalytic)
  refine iteratedFDeriv_scale_transverse_eq_zero _ hf ?_ v hv
  intro p h hp hh
  exact stateMap_high_scale_hasDerivAt p h hp hh

theorem radiusFactor_scale_shape_cross_eq_zero :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦ radiusFactor x.1 x.2.1 x.2.2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 1, 0)] = 0 :=
  radiusFactor_scale_transverse_cross_eq_zero (0, 1, 0) rfl

theorem radiusFactor_scale_high_cross_eq_zero :
    iteratedFDeriv ℝ 2
        (fun x : ℝ × ℝ × ℝ ↦ radiusFactor x.1 x.2.1 x.2.2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 0, 1)] = 0 :=
  radiusFactor_scale_transverse_cross_eq_zero (0, 0, 1) rfl

theorem stateMap_shape_scale_shape_cross_eq_zero :
    iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.1)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 1, 0)] = 0 :=
  stateMap_shape_scale_transverse_cross_eq_zero (0, 1, 0) rfl

theorem stateMap_shape_scale_high_cross_eq_zero :
    iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.1)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 0, 1)] = 0 :=
  stateMap_shape_scale_transverse_cross_eq_zero (0, 0, 1) rfl

theorem stateMap_high_scale_shape_cross_eq_zero :
    iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 1, 0)] = 0 :=
  stateMap_high_scale_transverse_cross_eq_zero (0, 1, 0) rfl

theorem stateMap_high_scale_high_cross_eq_zero :
    iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.2)
        (0, 2, 1) ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, 0, 1)] = 0 :=
  stateMap_high_scale_transverse_cross_eq_zero (0, 0, 1) rfl

end DFP.TwoLeg
