module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

namespace DFP.TwoLeg

/-- The first-leg removable spectral and gradient factors are stationary along the
signed-scale line through the base point. -/
private lemma firstLegFactorsScale_hasDerivAt :
    HasDerivAt
      (fun ε : ℝ ↦ (DFP.FirstLeg.spectralFactors ε 2 1,
        DFP.FirstLeg.gradientFactors ε 2 1))
      ((0, 0), (0, 0)) 0 := by
  let X : ℝ → ℝ := fun ε ↦ ε
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let six : ℝ → ℝ := fun _ ↦ 6
  have hX : HasDerivAt X 1 0 := hasDerivAt_id 0
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have htwo : HasDerivAt two 0 0 := hasDerivAt_const 0 2
  have hthree : HasDerivAt three 0 0 := hasDerivAt_const 0 3
  have hsix : HasDerivAt six 0 0 := hasDerivAt_const 0 6
  let onePlusCube := one + X ^ 3
  let onePlus := one + X
  have honePlusCube : HasDerivAt onePlusCube 0 0 := by
    exact (hone.add (hX.pow 3)).congr_deriv (g' := 0) (by norm_num)
  have honePlus : HasDerivAt onePlus 1 0 := by
    exact (hone.add hX).congr_deriv (g' := 1) (by norm_num)
  let B := one + ((fun ε ↦ 2 * (X ^ 3) ε) + X ^ 4)
  have hB : HasDerivAt B 0 0 := by
    exact (hone.add (((hX.pow 3).const_mul 2).add (hX.pow 4))).congr_deriv
      (g' := 0) (by norm_num)
  let C := onePlusCube ^ 2 + (fun ε ↦ 2 * (X ^ 6) ε) * onePlus ^ 2
  have hC : HasDerivAt C 0 0 := by
    exact ((honePlusCube.pow 2).add
      (((hX.pow 6).const_mul 2).mul (honePlus.pow 2))).congr_deriv
        (g' := 0) (by norm_num)
  have hB_ne : B 0 ≠ 0 := by norm_num [B, one, X]
  have hC_ne : C 0 ≠ 0 := by norm_num [C, onePlusCube, onePlus, one, X]
  let a := two - ((fun ε ↦ 4 * (X ^ 6) ε) * onePlus ^ 2) / C + one / B
  let b := one / B - (((fun ε ↦ 2 * (X ^ 3) ε) * onePlus) * onePlusCube) / C
  let d := one - onePlusCube ^ 2 / C + one / B
  let q := one - ((six * X ^ 3) * onePlus) / (three * B)
  let v := two - (six * onePlusCube) / (three * B)
  have ha : HasDerivAt a 0 0 := by
    exact ((htwo.sub ((((hX.pow 6).const_mul 4).mul (honePlus.pow 2)).div hC hC_ne)).add
      (hone.div hB hB_ne)).congr_deriv (g' := 0) (by norm_num [B, C, one, two, X])
  have hb : HasDerivAt b 0 0 := by
    exact ((hone.div hB hB_ne).sub
      (((((hX.pow 3).const_mul 2).mul honePlus).mul honePlusCube).div hC hC_ne)).congr_deriv
        (g' := 0) (by norm_num [B, C, onePlusCube, onePlus, one, X])
  have hd : HasDerivAt d 0 0 := by
    exact ((hone.sub ((honePlusCube.pow 2).div hC hC_ne)).add
      (hone.div hB hB_ne)).congr_deriv
        (g' := 0) (by norm_num [B, C, onePlusCube, one, X])
  have hq : HasDerivAt q 0 0 := by
    exact (hone.sub (((hsix.mul (hX.pow 3)).mul honePlus).div
      (hthree.mul hB) (by norm_num [B, one, three, X]))).congr_deriv
        (g' := 0) (by norm_num [B, onePlus, one, X])
  have hv : HasDerivAt v 0 0 := by
    exact (htwo.sub ((hsix.mul honePlusCube).div
      (hthree.mul hB) (by norm_num [B, one, three, X]))).congr_deriv
        (g' := 0) (by norm_num [B, onePlusCube, one, two, X])
  let A := X ^ 4 * a
  let E := X ^ 2 * b
  have hA : HasDerivAt A 0 0 := by
    exact ((hX.pow 4).mul ha).congr_deriv (g' := 0) (by norm_num [a, A, X])
  have hE : HasDerivAt E 0 0 := by
    exact ((hX.pow 2).mul hb).congr_deriv (g' := 0) (by norm_num [b, E, X])
  let rad := (d - A) ^ 2 + (fun ε ↦ 4 * (E ^ 2) ε)
  have hrad : HasDerivAt rad 0 0 := by
    exact (((hd.sub hA).pow 2).add ((hE.pow 2).const_mul 4)).congr_deriv
      (g' := 0) (by norm_num [a, b, d, A, E, rad, B, C, onePlusCube,
        onePlus, one, two, X])
  have hrad_ne : rad 0 ≠ 0 := by
    norm_num [a, b, d, A, E, rad, B, C, onePlusCube, onePlus, one, two, X]
  let gap := fun ε ↦ Real.sqrt (rad ε)
  have hgap : HasDerivAt gap 0 0 := by
    exact (hrad.sqrt hrad_ne).congr_deriv (g' := 0) (by norm_num [gap, rad, a, b,
      d, A, E, B, C, onePlusCube, onePlus, one, two, X])
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
      (g' := 0) (by norm_num [denomRad, d, low, high, gap, rad, a, b, A, E,
        B, C, onePlusCube, onePlus, one, two, X])
  have hdenomRad_ne : denomRad 0 ≠ 0 := by
    norm_num [denomRad, d, low, high, gap, rad, a, b, A, E, B, C,
      onePlusCube, onePlus, one, two, X]
  let denom := fun ε ↦ Real.sqrt (denomRad ε)
  have hdenom : HasDerivAt denom 0 0 := by
    exact (hdenomRad.sqrt hdenomRad_ne).congr_deriv (g' := 0)
      (by norm_num [denom, denomRad, d, low, high, gap, rad, a, b, A, E,
        B, C, onePlusCube, onePlus, one, two, X])
  have hhigh_ne : high 0 ≠ 0 := by
    norm_num [high, gap, rad, a, b, d, A, E, B, C, onePlusCube, onePlus,
      one, two, X]
  have hdenom_ne : denom 0 ≠ 0 := by
    norm_num [denom, denomRad, d, low, high, gap, rad, a, b, A, E,
      B, C, onePlusCube, onePlus, one, two, X]
  let spectralLow := (a * d - b ^ 2) / high
  let gradientLow := ((d - low) * q - (X ^ 4 * b) * v) / denom
  let gradientHigh := (b * q + (d - low) * v) / denom
  have hspectralLow : HasDerivAt spectralLow 0 0 := by
    exact (((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh_ne).congr_deriv
      (g' := 0) (by norm_num [spectralLow, a, b, d, high, gap, rad, A, E,
        B, C, onePlusCube, onePlus, one, two, X])
  have hgradientLow : HasDerivAt gradientLow 0 0 := by
    exact ((((hd.sub hlow).mul hq).sub (((hX.pow 4).mul hb).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientLow, a, b, d, q, v, low, high, gap, rad, A, E,
          denom, denomRad, B, C, onePlusCube, onePlus, one, two, three, six, X])
  have hgradientHigh : HasDerivAt gradientHigh 0 0 := by
    exact (((hb.mul hq).add ((hd.sub hlow).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientHigh, a, b, d, q, v, low, high, gap, rad, A, E,
          denom, denomRad, B, C, onePlusCube, onePlus, one, two, three, six, X])
  -- Repackage the scalar derivative facts as the two public removable factor pairs.
  have hfactorData := (hspectralLow.prodMk hhigh).prodMk
    (hgradientLow.prodMk hgradientHigh)
  apply hfactorData.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε ↦ by
    simp [DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom, spectralLow, gradientLow, gradientHigh, denom,
      denomRad, low, high, gap, rad, A, E, a, b, d, q, v, B, C, onePlusCube,
      onePlus, one, two, three, six, X]
    ring_nf
    simp)

/-- The second-leg removable factors are stationary along the signed-scale line
through the base point. -/
private lemma secondLegFactorsScale_hasDerivAt :
    HasDerivAt (fun ε : ℝ ↦ DFP.SecondLeg.factors ε 2 1)
      ((0, 0), (0, 0), (0, 0)) 0 := by
  let X : ℝ → ℝ := fun ε ↦ ε
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let six : ℝ → ℝ := fun _ ↦ 6
  let L := fun ε ↦ (DFP.FirstLeg.spectralFactors ε 2 1).1
  let H := fun ε ↦ (DFP.FirstLeg.spectralFactors ε 2 1).2
  let Q := fun ε ↦ (DFP.FirstLeg.gradientFactors ε 2 1).1
  let U := fun ε ↦ (DFP.FirstLeg.gradientFactors ε 2 1).2
  have hX : HasDerivAt X 1 0 := hasDerivAt_id 0
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have htwo : HasDerivAt two 0 0 := hasDerivAt_const 0 2
  have hthree : HasDerivAt three 0 0 := hasDerivAt_const 0 3
  have hsix : HasDerivAt six 0 0 := hasDerivAt_const 0 6
  have hspectral : HasDerivAt
      (fun ε ↦ DFP.FirstLeg.spectralFactors ε 2 1) (0, 0) 0 := by
    simpa using firstLegFactorsScale_hasDerivAt.hasFDerivAt.fst.hasDerivAt
  have hgradient : HasDerivAt
      (fun ε ↦ DFP.FirstLeg.gradientFactors ε 2 1) (0, 0) 0 := by
    simpa using firstLegFactorsScale_hasDerivAt.hasFDerivAt.snd.hasDerivAt
  have hL : HasDerivAt L 0 0 := by
    simpa [L] using hspectral.hasFDerivAt.fst.hasDerivAt
  have hH : HasDerivAt H 0 0 := by
    simpa [H] using hspectral.hasFDerivAt.snd.hasDerivAt
  have hQ : HasDerivAt Q 0 0 := by
    simpa [Q] using hgradient.hasFDerivAt.fst.hasDerivAt
  have hU : HasDerivAt U 0 0 := by
    simpa [U] using hgradient.hasFDerivAt.snd.hasDerivAt
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  let w₁ := X * L * Q - (two * H) * U
  let w₂ := H * U - ((two * X ^ 3) * L) * Q
  have hw₁ : HasDerivAt w₁ 2 0 := by
    exact (((hX.mul hL).mul hQ).sub ((htwo.mul hH).mul hU)).congr_deriv
      (g' := 2) (by norm_num [w₁, X, L, H, Q, U, hspectralBase, hgradientBase])
  have hw₂ : HasDerivAt w₂ 0 0 := by
    exact ((hH.mul hU).sub (((htwo.mul (hX.pow 3)).mul hL).mul hQ)).congr_deriv
      (g' := 0) (by norm_num [w₂, X, L, H, Q, U, hspectralBase, hgradientBase])
  let beta := (((X ^ 3 * L) * Q) * w₁) + (H * U) * w₂
  let gamma := ((X ^ 6 * L) * w₁ ^ 2) + H * w₂ ^ 2
  let delta := L * Q ^ 2 + H * U ^ 2
  have hbeta : HasDerivAt beta 0 0 := by
    exact (((((hX.pow 3).mul hL).mul hQ).mul hw₁).add
      ((hH.mul hU).mul hw₂)).congr_deriv (g' := 0)
        (by norm_num [beta, w₁, w₂, X, L, H, Q, U, hspectralBase, hgradientBase])
  have hgamma : HasDerivAt gamma 0 0 := by
    exact ((((hX.pow 6).mul hL).mul (hw₁.pow 2)).add
      (hH.mul (hw₂.pow 2))).congr_deriv (g' := 0)
        (by norm_num [gamma, w₁, w₂, X, L, H, Q, U, hspectralBase, hgradientBase])
  have hdelta : HasDerivAt delta 0 0 := by
    exact ((hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))).congr_deriv
      (g' := 0) (by norm_num [delta, L, H, Q, U, hspectralBase, hgradientBase])
  have hbeta_ne : beta 0 ≠ 0 := by
    norm_num [beta, w₁, w₂, X, L, H, Q, U, hspectralBase, hgradientBase]
  have hgamma_ne : gamma 0 ≠ 0 := by
    norm_num [gamma, w₁, w₂, X, L, H, Q, U, hspectralBase, hgradientBase]
  let a := L - (((X ^ 6 * L ^ 2) * w₁ ^ 2) / gamma) + (L ^ 2 * Q ^ 2) / beta
  let b := -((((X ^ 3 * L) * H) * w₁ * w₂) / gamma) + ((L * Q) * H * U) / beta
  let d := H - (H ^ 2 * w₂ ^ 2) / gamma + (H ^ 2 * U ^ 2) / beta
  let q := Q - (((X ^ 3 * delta) * w₁) / (three * beta))
  let v := U - (delta * w₂) / (three * beta)
  have ha : HasDerivAt a 0 0 := by
    exact ((hL.sub (((((hX.pow 6).mul (hL.pow 2)).mul (hw₁.pow 2)).div
      hgamma hgamma_ne))).add (((hL.pow 2).mul (hQ.pow 2)).div hbeta hbeta_ne)).congr_deriv
        (g' := 0) (by norm_num [a, beta, gamma, w₁, w₂, X, L, H, Q, U,
          hspectralBase, hgradientBase])
  have hb : HasDerivAt b 0 0 := by
    exact ((((((((hX.pow 3).mul hL).mul hH).mul hw₁).mul hw₂).div
      hgamma hgamma_ne).neg).add ((((hL.mul hQ).mul hH).mul hU).div hbeta hbeta_ne)).congr_deriv
        (g' := 0) (by norm_num [b, beta, gamma, w₁, w₂, X, L, H, Q, U,
          hspectralBase, hgradientBase])
  have hd : HasDerivAt d 0 0 := by
    exact ((hH.sub (((hH.pow 2).mul (hw₂.pow 2)).div hgamma hgamma_ne)).add
      (((hH.pow 2).mul (hU.pow 2)).div hbeta hbeta_ne)).congr_deriv
        (g' := 0) (by norm_num [d, beta, gamma, w₁, w₂, X, L, H, Q, U,
          hspectralBase, hgradientBase])
  have hq : HasDerivAt q 0 0 := by
    exact (hQ.sub ((((hX.pow 3).mul hdelta).mul hw₁).div
      (hthree.mul hbeta) (by norm_num [three, beta, w₁, w₂, X, L, H, Q, U,
        hspectralBase, hgradientBase]))).congr_deriv (g' := 0)
          (by norm_num [q, beta, delta, w₁, w₂, three, X, L, H, Q, U,
            hspectralBase, hgradientBase])
  have hv : HasDerivAt v 0 0 := by
    exact (hU.sub ((hdelta.mul hw₂).div (hthree.mul hbeta)
      (by norm_num [three, beta, w₁, w₂, X, L, H, Q, U,
        hspectralBase, hgradientBase]))).congr_deriv (g' := 0)
          (by norm_num [v, beta, delta, w₁, w₂, three, X, L, H, Q, U,
            hspectralBase, hgradientBase])
  let A := X ^ 4 * a
  let E := X ^ 2 * b
  have hA : HasDerivAt A 0 0 := by
    exact ((hX.pow 4).mul ha).congr_deriv (g' := 0) (by norm_num [A, a, X])
  have hE : HasDerivAt E 0 0 := by
    exact ((hX.pow 2).mul hb).congr_deriv (g' := 0) (by norm_num [E, b, X])
  let rad := (d - A) ^ 2 + (fun ε ↦ 4 * (E ^ 2) ε)
  have hrad : HasDerivAt rad 0 0 := by
    exact (((hd.sub hA).pow 2).add ((hE.pow 2).const_mul 4)).congr_deriv
      (g' := 0) (by norm_num [rad, d, A, E, a, b, beta, gamma, delta, w₁, w₂,
        X, L, H, Q, U, three, hspectralBase, hgradientBase])
  have hrad_ne : rad 0 ≠ 0 := by
    norm_num [rad, d, A, E, a, b, beta, gamma, delta, w₁, w₂, X, L, H, Q,
      U, three, hspectralBase, hgradientBase]
  let gap := fun ε ↦ Real.sqrt (rad ε)
  have hgap : HasDerivAt gap 0 0 := by
    exact (hrad.sqrt hrad_ne).congr_deriv (g' := 0) (by norm_num [gap, rad, d, A,
      E, a, b, beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
      hspectralBase, hgradientBase])
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
      (g' := 0) (by norm_num [denomRad, low, high, gap, rad, d, A, E, a, b,
        beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
        hspectralBase, hgradientBase])
  have hdenomRad_ne : denomRad 0 ≠ 0 := by
    norm_num [denomRad, low, high, gap, rad, d, A, E, a, b, beta, gamma,
      delta, w₁, w₂, X, L, H, Q, U, three, hspectralBase, hgradientBase]
  let denom := fun ε ↦ Real.sqrt (denomRad ε)
  have hdenom : HasDerivAt denom 0 0 := by
    exact (hdenomRad.sqrt hdenomRad_ne).congr_deriv (g' := 0)
      (by norm_num [denom, denomRad, low, high, gap, rad, d, A, E, a, b,
        beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
        hspectralBase, hgradientBase])
  have hhigh_ne : high 0 ≠ 0 := by
    norm_num [high, gap, rad, d, A, E, a, b, beta, gamma, delta, w₁, w₂,
      X, L, H, Q, U, three, hspectralBase, hgradientBase]
  have hdenom_ne : denom 0 ≠ 0 := by
    norm_num [denom, denomRad, low, high, gap, rad, d, A, E, a, b, beta,
      gamma, delta, w₁, w₂, X, L, H, Q, U, three, hspectralBase, hgradientBase]
  let spectralLow := (a * d - b ^ 2) / high
  let gradientLow := ((d - low) * q - (X ^ 4 * b) * v) / denom
  let gradientHigh := (b * q + (d - low) * v) / denom
  have hspectralLow : HasDerivAt spectralLow 0 0 := by
    exact (((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh_ne).congr_deriv
      (g' := 0) (by norm_num [spectralLow, high, gap, rad, d, A, E, a, b,
        beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
        hspectralBase, hgradientBase])
  have hgradientLow : HasDerivAt gradientLow 0 0 := by
    exact ((((hd.sub hlow).mul hq).sub (((hX.pow 4).mul hb).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientLow, denom, denomRad, low, high, gap, rad, d, q, v,
          A, E, a, b, beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
          hspectralBase, hgradientBase])
  have hgradientHigh : HasDerivAt gradientHigh 0 0 := by
    exact (((hb.mul hq).add ((hd.sub hlow).mul hv)).div
      hdenom hdenom_ne).congr_deriv (g' := 0)
        (by norm_num [gradientHigh, denom, denomRad, low, high, gap, rad, d, q, v,
          A, E, a, b, beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
          hspectralBase, hgradientBase])
  let canonicalRadius := (spectralLow * gradientLow) / (high * gradientHigh)
  let canonicalShape := (high * gradientHigh ^ 2) / (spectralLow * gradientLow ^ 2)
  have hcanonicalRadius : HasDerivAt canonicalRadius 0 0 := by
    exact ((hspectralLow.mul hgradientLow).div (hhigh.mul hgradientHigh)
      (by norm_num [high, gradientHigh, denom, denomRad, low, gap, rad, d, q, v,
        A, E, a, b, beta, gamma, delta, w₁, w₂, X, L, H, Q, U, three,
        hspectralBase, hgradientBase])).congr_deriv (g' := 0)
          (by norm_num [canonicalRadius, spectralLow, gradientLow, high, gradientHigh,
            denom, denomRad, low, gap, rad, d, q, v, A, E, a, b, beta, gamma,
            delta, w₁, w₂, X, L, H, Q, U, three, hspectralBase, hgradientBase])
  have hcanonicalShape : HasDerivAt canonicalShape 0 0 := by
    exact ((hhigh.mul (hgradientHigh.pow 2)).div
      (hspectralLow.mul (hgradientLow.pow 2))
      (by norm_num [spectralLow, gradientLow, high, gradientHigh, denom, denomRad,
        low, gap, rad, d, q, v, A, E, a, b, beta, gamma, delta, w₁, w₂,
        X, L, H, Q, U, three, hspectralBase, hgradientBase])).congr_deriv (g' := 0)
          (by norm_num [canonicalShape, spectralLow, gradientLow, high, gradientHigh,
            denom, denomRad, low, gap, rad, d, q, v, A, E, a, b, beta, gamma,
            delta, w₁, w₂, X, L, H, Q, U, three, hspectralBase, hgradientBase])
  -- Assemble the three second-leg factor pairs and identify them with the public formulas.
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

/-- The transverse state coordinates are stationary in the signed-scale direction
at the base point. -/
private lemma stateMapTransverseScale_hasDerivAt :
    HasDerivAt (fun ε : ℝ ↦ (stateMap (ε, 2, 1)).2) (0, 0) 0 := by
  have hspectral := secondLegFactorsScale_hasDerivAt.hasFDerivAt.fst.hasDerivAt
  have hcanonical := secondLegFactorsScale_hasDerivAt.hasFDerivAt.snd.snd.hasDerivAt
  have hshape := hcanonical.hasFDerivAt.snd.hasDerivAt
  have hhigh := hspectral.hasFDerivAt.snd.hasDerivAt
  have hshapeZero := hshape.congr_deriv (g' := 0) (by norm_num)
  have hhighZero := hhigh.congr_deriv (g' := 0) (by norm_num)
  -- The transverse state is exactly the shape/high pair of the second-leg factors.
  apply (hshapeZero.prodMk hhighZero).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε ↦
    congrArg Prod.snd (stateMap_apply ε 2 1))

/-- Along the zero-scale slice, the transverse state has the derivative prescribed
by the limiting rational map. -/
private lemma stateMapTransverseZeroSlice_hasDerivAt (u w : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (stateMap (0, 2 + t * u, 1 + t * w)).2)
      ((-(1 : ℝ) / 9) * u + ((2 : ℝ) / 3) * w, 0) 0 := by
  let p : ℝ → ℝ := fun t ↦ 2 + t * u
  let h : ℝ → ℝ := fun t ↦ 1 + t * w
  let one : ℝ → ℝ := fun _ ↦ 1
  let four : ℝ → ℝ := fun _ ↦ 4
  let nine : ℝ → ℝ := fun _ ↦ 9
  let eightyOne : ℝ → ℝ := fun _ ↦ 81
  have hp : HasDerivAt p u 0 := by
    simpa only [p, id_eq, zero_add, one_mul] using
      ((hasDerivAt_id 0).mul_const u).const_add 2
  have hh : HasDerivAt h w 0 := by
    simpa only [h, id_eq, zero_add, one_mul] using
      ((hasDerivAt_id 0).mul_const w).const_add 1
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have hfour : HasDerivAt four 0 0 := hasDerivAt_const 0 4
  have hnine : HasDerivAt nine 0 0 := hasDerivAt_const 0 9
  have heightyOne : HasDerivAt eightyOne 0 0 := hasDerivAt_const 0 81
  let residual := (nine * h) * p + (p + one) ^ 2
  have hresidual : HasDerivAt residual (15 * u + 18 * w) 0 := by
    exact (((hnine.mul hh).mul hp).add ((hp.add hone).pow 2)).congr_deriv
      (g' := 15 * u + 18 * w) (by norm_num [residual, p, h, one, nine]; ring)
  let denominator := ((eightyOne * h) * p) * (p + one) ^ 2
  have hdenominator : HasDerivAt denominator (1701 * u + 1458 * w) 0 := by
    exact (((heightyOne.mul hh).mul hp).mul ((hp.add hone).pow 2)).congr_deriv
      (g' := 1701 * u + 1458 * w)
        (by norm_num [denominator, p, h, one, eightyOne]; ring)
  have hdenominator_ne : denominator 0 ≠ 0 := by
    norm_num [denominator, p, h, one, eightyOne]
  let shape := (four * residual ^ 2) / denominator
  have hshape : HasDerivAt shape ((-(1 : ℝ) / 9) * u + ((2 : ℝ) / 3) * w) 0 := by
    exact ((hfour.mul (hresidual.pow 2)).div hdenominator hdenominator_ne).congr_deriv
      (g' := (-(1 : ℝ) / 9) * u + ((2 : ℝ) / 3) * w)
        (by norm_num [shape, residual, denominator, p, h, one, four, nine,
          eightyOne]; ring)
  have hp_pos : ∀ᶠ t in nhds 0, 0 < p t := by
    apply hp.continuousAt.eventually
    exact Ioi_mem_nhds (by norm_num [p])
  have hh_pos : ∀ᶠ t in nhds 0, 0 < h t := by
    apply hh.continuousAt.eventually
    exact Ioi_mem_nhds (by norm_num [h])
  have hexplicit := hshape.prodMk (hasDerivAt_const (x := 0) (c := (1 : ℝ)))
  -- Positivity near the base identifies the public map with this rational formula.
  apply hexplicit.congr_of_eventuallyEq
  filter_upwards [hp_pos, hh_pos] with t hpt hht
  simpa only [p, h, shape, residual, denominator, one, four, nine, eightyOne,
    Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply] using
      stateMap_zero_transverse (p t) (h t) hpt hht

/-- The derivative of the signed scale coordinate at the base is projection onto
the scale direction. -/
private lemma signedEpsilon_fderiv_apply (v : ℝ × ℝ × ℝ) :
    fderiv ℝ (fun x : ℝ × ℝ × ℝ ↦ signedEpsilon x.1 x.2.1 x.2.2)
      (0, 2, 1) v = v.1 := by
  have hfst : DifferentiableAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) :=
    differentiableAt_fst
  have hradius := analyticAt_radiusFactor.differentiableAt
  have hradius_ne : radiusFactor 0 2 1 ≠ 0 := by
    rw [radiusFactor_base]
    norm_num
  have hsqrt := hradius.sqrt hradius_ne
  -- The product-rule term involving the radius derivative is killed by the zero scale.
  unfold signedEpsilon
  rw [fderiv_fun_mul hfst hsqrt]
  rw [fderiv_fst]
  simp [radiusFactor_base]

/-- The transverse Fréchet derivative at the base has the displayed triangular
action on the shape and high-eigenvalue coordinates. -/
private lemma stateMapTransverse_fderiv_apply (v : ℝ × ℝ × ℝ) :
    fderiv ℝ (fun x ↦ (stateMap x).2) (0, 2, 1) v =
      ((-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0) := by
  let transverse := fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2
  have htransverse : DifferentiableAt ℝ transverse (0, 2, 1) :=
    stateMapAnalytic.differentiableAt.snd
  have hscaleLine : HasDerivAt (fun t : ℝ ↦ ((t, 2, 1) : ℝ × ℝ × ℝ))
      (1, 0, 0) 0 := by
    have htwo : HasDerivAt (fun _ : ℝ ↦ (2 : ℝ)) 0 0 := hasDerivAt_const 0 2
    have hone : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    exact (hasDerivAt_id 0).prodMk (htwo.prodMk hone)
  have htransverseLine (u w : ℝ) :
      HasDerivAt (fun t : ℝ ↦ ((0, 2 + t * u, 1 + t * w) : ℝ × ℝ × ℝ))
        (0, u, w) 0 := by
    have hp := (hasDerivAt_const (x := 0) (c := (2 : ℝ))).add
      ((hasDerivAt_id 0).mul_const u)
    have hh := (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
      ((hasDerivAt_id 0).mul_const w)
    convert (hasDerivAt_const (x := 0) (c := (0 : ℝ))).prodMk (hp.prodMk hh) using 1
    all_goals norm_num
  have hscaleChain := htransverse.hasFDerivAt.comp_hasDerivAt 0 hscaleLine
  have hscale : fderiv ℝ transverse (0, 2, 1) (1, 0, 0) = (0, 0) := by
    exact hscaleChain.unique stateMapTransverseScale_hasDerivAt
  have htransverseAtSliceBase : DifferentiableAt ℝ transverse
      (0, 2 + 0 * v.2.1, 1 + 0 * v.2.2) := by
    simpa using htransverse
  have hsliceChain := htransverseAtSliceBase.hasFDerivAt.comp_hasDerivAt 0
    (htransverseLine v.2.1 v.2.2)
  have hslice : fderiv ℝ transverse (0, 2, 1) (0, v.2.1, v.2.2) =
      ((-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0) := by
    simpa only [zero_mul, add_zero] using
      hsliceChain.unique (stateMapTransverseZeroSlice_hasDerivAt v.2.1 v.2.2)
  have hv_decomp : v = v.1 • ((1, 0, 0) : ℝ × ℝ × ℝ) +
      (0, v.2.1, v.2.2) := by
    ext <;> simp
  -- Linearity combines the stationary scale direction with the explicit zero slice.
  rw [show (fun x ↦ (stateMap x).2) = transverse from rfl, hv_decomp, map_add,
    map_smul, hscale, hslice]
  simp

/-- At `(0, 2, 1)`, the derivative of the two-leg state map has the displayed
triangular action on tangent coordinates. -/
theorem stateMap_fderiv_apply (v : ℝ × ℝ × ℝ) :
    fderiv ℝ stateMap ((0, 2, 1) : ℝ × ℝ × ℝ) v =
      (v.1, (-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0) := by
  -- Package differentiability of the two coordinates into one product derivative.
  have hscale := analyticAt_signedEpsilon.differentiableAt.hasFDerivAt
  have htransverse := stateMapAnalytic.differentiableAt.snd.hasFDerivAt
  have hproduct := hscale.prodMk htransverse
  have hstateFunction : stateMap = fun x ↦
      (signedEpsilon x.1 x.2.1 x.2.2, (stateMap x).2) := by
    funext x
    rfl
  -- Apply the product derivative and then use the two coordinate computations.
  rw [hstateFunction, hproduct.fderiv]
  simp only [ContinuousLinearMap.prod_apply, signedEpsilon_fderiv_apply,
    stateMapTransverse_fderiv_apply]

/-- The derivative of the two-leg state map at `(0, 2, 1)` has center
eigenvalue `1`. -/
theorem stateMap_centerEigenvalue :
    Module.End.HasEigenvalue
      (fderiv ℝ stateMap ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (1 : ℝ) := by
  -- The scale coordinate vector is fixed by the triangular derivative.
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := ((1, 0, 0) : ℝ × ℝ × ℝ)) (Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩)
  · rw [Module.End.mem_eigenspace_iff]
    norm_num [stateMap_fderiv_apply]
  · norm_num

/-- The derivative of the two-leg state map at `(0, 2, 1)` has transverse
eigenvalue `-1 / 9`. -/
theorem stateMap_transverseEigenvalue_negNinth :
    Module.End.HasEigenvalue
      (fderiv ℝ stateMap ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap
        (-(1 : ℝ) / 9) := by
  -- The second coordinate axis is preserved, with multiplier `-1 / 9`.
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := ((0, 1, 0) : ℝ × ℝ × ℝ)) (Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩)
  · rw [Module.End.mem_eigenspace_iff]
    norm_num [stateMap_fderiv_apply]
  · norm_num

/-- The derivative of the two-leg state map at `(0, 2, 1)` has transverse
eigenvalue `0`. -/
theorem stateMap_transverseEigenvalue_zero :
    Module.End.HasEigenvalue
      (fderiv ℝ stateMap ((0, 2, 1) : ℝ × ℝ × ℝ)).toLinearMap (0 : ℝ) := by
  -- The vector `(0, 6, 1)` cancels the two terms in the transverse row.
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := ((0, 6, 1) : ℝ × ℝ × ℝ)) (Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩)
  · rw [Module.End.mem_eigenspace_iff]
    norm_num [stateMap_fderiv_apply]
  · norm_num

end DFP.TwoLeg
