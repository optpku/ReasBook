module

import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GraphJetSmoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.NormJet

/-- The five normalized step- and gradient-norm projections have one common order-seven
uniform finite-jet family on every closed ball of graph coefficients. -/
theorem uniformOn (B : ℝ) :
    let norms := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      let observable := DFP.TwoLeg.observableMap
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε)
      (observable.firstStepNorm, observable.secondStepNorm,
        observable.initialGradientNorm, observable.intermediateGradientNorm,
        observable.finalGradientNorm)
    FiniteTaylorJet.IsUniformOn norms
      (fun θ ↦ FiniteTaylorJet.ofFunction ℝ 7 (norms θ) 0) 0
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) := by
  dsimp only
  apply FiniteTaylorJet.isUniformOn_of_contDiffAt 7 _ 0 _ (isCompact_closedBall _ _)
  intro θ _
  let path : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) → ℝ × ℝ × ℝ := fun z ↦
    (z.2, 2 + z.1.1.1 * z.2 ^ 3 + z.1.2.1 * z.2 ^ 4,
      1 + z.1.1.2 * z.2 ^ 3 + z.1.2.2 * z.2 ^ 4)
  have hpath : ContDiffAt ℝ 7 path (θ, 0) := by
    dsimp only [path]
    fun_prop
  have hbase : path (θ, 0) = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    norm_num [path]
  have hfirstOuter := DFP.TwoLeg.CenterCancellation.firstStepNorm_contDiffAt 7
  have hsecondOuter := DFP.TwoLeg.CenterCancellation.secondStepNorm_contDiffAt 7
  have hinitialOuter := DFP.TwoLeg.initialGradientNorm_contDiffAt 7
  have hintermediateOuter := DFP.TwoLeg.intermediateGradientNorm_contDiffAt 7
  have hfinalOuter := DFP.TwoLeg.finalGradientNorm_contDiffAt 7
  rw [← hbase] at hfirstOuter hsecondOuter hinitialOuter hintermediateOuter hfinalOuter
  have hfirst := hfirstOuter.comp (θ, 0) hpath
  have hsecond := hsecondOuter.comp (θ, 0) hpath
  have hinitial := hinitialOuter.comp (θ, 0) hpath
  have hintermediate := hintermediateOuter.comp (θ, 0) hpath
  have hfinal := hfinalOuter.comp (θ, 0) hpath
  have hcombined := hfirst.prodMk
    (hsecond.prodMk (hinitial.prodMk (hintermediate.prodMk hfinal)))
  apply hcombined.congr_of_eventuallyEq
  filter_upwards [] with z
  rcases z with ⟨η, ε⟩
  simp only [Function.uncurry_apply_pair, Function.comp_apply, path]
  rw [DFP.TwoLeg.graphJetPath_apply]

/-- The initial normalized gradient norm is the positive square root of its two
coordinate squares. -/
private theorem initialGradientNorm_eq_sqrt (ε p h : ℝ) :
    (DFP.TwoLeg.observableMap (ε, p, h)).initialGradientNorm =
      Real.sqrt (1 + (p * ε ^ 2) ^ 2) := by
  have hnorms := congrArg Prod.fst
    (DFP.TwoLeg.observableMap_gradientNorms ε p h)
  simp only [] at hnorms
  rw [hnorms]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- The intermediate normalized gradient norm is the positive square root of its two
coordinate squares. -/
private theorem intermediateGradientNorm_eq_sqrt (ε p h : ℝ) :
    (DFP.TwoLeg.observableMap (ε, p, h)).intermediateGradientNorm =
      Real.sqrt
        ((DFP.FirstLeg.outputGradient ε p h 0) ^ 2 +
          (DFP.FirstLeg.outputGradient ε p h 1) ^ 2) := by
  have hnorms := congrArg (fun norms ↦ norms.2.1)
    (DFP.TwoLeg.observableMap_gradientNorms ε p h)
  simp only [] at hnorms
  rw [hnorms]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- On the first-leg low chart, the final normalized gradient norm is the
positive square root of its two frame-coordinate squares. -/
private theorem finalGradientNorm_eq_sqrt_of_lowChart (ε p h : ℝ)
    (hchart :
      let M := DFP.FirstLeg.outputMetric ε p h
      M 0 0 < M 1 1) :
    (DFP.TwoLeg.observableMap (ε, p, h)).finalGradientNorm =
      Real.sqrt
        ((DFP.SecondLeg.outputGradient ε p h 0) ^ 2 +
          (DFP.SecondLeg.outputGradient ε p h 1) ^ 2) := by
  have hnorms := congrArg (fun norms ↦ norms.2.2)
    (DFP.TwoLeg.observableMap_gradientNorms ε p h)
  simp only [] at hnorms
  let M := DFP.FirstLeg.outputMetric ε p h
  have hframe : DFP.FirstLeg.frame ε p h ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    change EuclideanPlane.frame
      (RealSymmetric2.lowVector (M 0 0) (M 0 1) (M 1 1)) ∈
        Matrix.specialOrthogonalGroup (Fin 2) ℝ
    exact RealSymmetric2.frame_mem_specialOrthogonalGroup
      (M 0 0) (M 0 1) (M 1 1) hchart
  rw [hnorms, Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup _ hframe]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- The canceled second-step displacement factor in the first output eigenframe. -/
private def secondStepDisplacementFactor (ε p h : ℝ) : Fin 2 → ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let delta := L * Q ^ 2 + H * U ^ 2
  ![-(delta * ε ^ 2 * L * Q / (3 * beta)),
    -(delta * H * U / (3 * beta))]

/-- On the first-leg low chart, the second step norm is `ε ^ 2` times the norm
of its canceled displacement factor. -/
private theorem secondStepNorm_eq_scale_sqrt_of_lowChart (ε p h : ℝ)
    (hchart :
      let M := DFP.FirstLeg.outputMetric ε p h
      M 0 0 < M 1 1) :
    (DFP.TwoLeg.observableMap (ε, p, h)).secondStepNorm =
      ε ^ 2 * Real.sqrt
        ((secondStepDisplacementFactor ε p h 0) ^ 2 +
          (secondStepDisplacementFactor ε p h 1) ^ 2) := by
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![ε ^ 4 * spectral.1, spectral.2]
  let g : Fin 2 → ℝ := ![gradient.1, ε ^ 2 * gradient.2]
  let Hg := H.mulVec g
  let A := (TwoPhaseControls.second ε).matrix
  let alpha := (TwoPhaseControls.second ε).tau * dotProduct g Hg /
    dotProduct Hg (A.mulVec Hg)
  let raw : Fin 2 → ℝ := -(alpha • Hg)
  have hnorms := congrArg Prod.snd
    (DFP.TwoLeg.observableMap_stepNorms ε p h)
  have hnorms' :
      (DFP.TwoLeg.observableMap (ε, p, h)).secondStepNorm =
        ‖WithLp.toLp 2 ((DFP.FirstLeg.frame ε p h).mulVec raw)‖ := by
    simpa only [spectral, gradient, H, g, Hg, A, alpha, raw] using hnorms
  have hraw : raw = ε ^ 2 • secondStepDisplacementFactor ε p h := by
    ext i
    fin_cases i
    · simp [raw, alpha, Hg, A, H, g, spectral, gradient,
        secondStepDisplacementFactor,
        TwoPhaseControls.second_tau, TwoPhaseControls.second_matrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      by_cases hε : ε = 0
      · simp [hε]
      · field_simp [hε]
        ring
    · simp [raw, alpha, Hg, A, H, g, spectral, gradient,
        secondStepDisplacementFactor,
        TwoPhaseControls.second_tau, TwoPhaseControls.second_matrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      by_cases hε : ε = 0
      · simp [hε]
      · field_simp [hε]
        ring
  let M := DFP.FirstLeg.outputMetric ε p h
  have hframe : DFP.FirstLeg.frame ε p h ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    change EuclideanPlane.frame
      (RealSymmetric2.lowVector (M 0 0) (M 0 1) (M 1 1)) ∈
        Matrix.specialOrthogonalGroup (Fin 2) ℝ
    exact RealSymmetric2.frame_mem_specialOrthogonalGroup
      (M 0 0) (M 0 1) (M 1 1) hchart
  rw [hnorms', Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup _ hframe]
  rw [hraw]
  have htoLp :
      WithLp.toLp 2 (ε ^ 2 • secondStepDisplacementFactor ε p h) =
        ε ^ 2 • WithLp.toLp 2 (secondStepDisplacementFactor ε p h) := rfl
  rw [htoLp, norm_smul]
  have hnormPower : ‖ε ^ 2‖ = ε ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact sq_nonneg ε
  rw [hnormPower]
  congr 1
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- Multiplying congruent germs by `ε ^ k` raises their congruence order by
`k`. -/
private theorem eqModPow_mul_pow_left {n k : ℕ} {f g : ℝ → ℝ}
    (hfg : EqModPow n f g) :
    EqModPow (n + k) (fun ε ↦ ε ^ k * f ε) (fun ε ↦ ε ^ k * g ε) := by
  have hproduct :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ k) (𝓝 0)).mul
      (EqModPow.to_isBigO hfg)
  have hleft (ε : ℝ) :
      ε ^ k * (f ε - g ε) = ε ^ k * f ε - ε ^ k * g ε := by
    ring
  have hproduct' := hproduct.congr_left hleft
  apply EqModPow.of_isBigO
  simpa only [← pow_add, Nat.add_comm] using hproduct'

/-- Scalar multiplication preserves the order of a real germ congruence. -/
private theorem eqModPow_const_mul_left {n : ℕ} {f g : ℝ → ℝ}
    (c : ℝ) (hfg : EqModPow n f g) :
    EqModPow n (fun ε ↦ c * f ε) (fun ε ↦ c * g ε) := by
  have hscaled := (EqModPow.to_isBigO hfg).const_mul_left c
  have hidentity (ε : ℝ) : c * (f ε - g ε) = c * f ε - c * g ε := by
    ring
  exact EqModPow.of_isBigO (hscaled.congr_left hidentity)

/-- A germ congruence known to order `m` remains valid at every lower order `n`. -/
private theorem eqModPow_mono {n m : ℕ} {f g : ℝ → ℝ}
    (hfg : EqModPow m f g) (hnm : n ≤ m) : EqModPow n f g := by
  obtain rfl | hlt := hnm.eq_or_lt
  · exact hfg
  · apply EqModPow.of_isBigO
    exact (EqModPow.to_isBigO hfg).trans
      (Asymptotics.isLittleO_pow_pow hlt).isBigO

/-- Positive-order congruent real germs take the same value at the origin. -/
private theorem eqModPow_apply_zero {n : ℕ} {f g : ℝ → ℝ}
    (hn : 0 < n) (hfg : EqModPow n f g) : f 0 = g 0 := by
  have hzeroRule := mem_of_mem_nhds (EqModPow.to_isBigO hfg).eq_zero_imp
  have hzeroPower : (0 : ℝ) ^ n = 0 := zero_pow (Nat.ne_of_gt hn)
  exact sub_eq_zero.mp (hzeroRule hzeroPower)

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
private theorem slowGraphFirstLegFactorGerms :
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
  refine ⟨?_, ?_, ?_, ?_⟩
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


set_option maxHeartbeats 2000000 in
-- The exact canceled second-step factor inherits the explicit first-leg germ computation.
/-- The canceled second-step factor norm has its stated order-four germ on the
polynomial slow graph. -/
private theorem slowGraphSecondStepFactorNormGerm :
    EqModPow 5
      (fun ε : ℝ ↦
        Real.sqrt
          ((secondStepDisplacementFactor ε
                (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
                (1 + 8 * ε ^ 3) 0) ^ 2 +
            (secondStepDisplacementFactor ε
                (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
                (1 + 8 * ε ^ 3) 1) ^ 2))
      (fun ε : ℝ ↦
        1 + (114 / 5) * ε ^ 3 - (49 / 10) * ε ^ 4) := by
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
  rcases slowGraphFirstLegFactorGerms with ⟨hLRaw, hHRaw, hQRaw, hURaw⟩
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
  let L5 : ℝ → ℝ := fun ε ↦
    2 + (298 / 5) * ε ^ 3 + (1 / 5) * ε ^ 4
  let H5 : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3
  let Q5 : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4
  let U5 : ℝ → ℝ := fun ε ↦
    1 + (56 / 5) * ε ^ 3 - (11 / 10) * ε ^ 4
  let beta5 : ℝ → ℝ := fun ε ↦
    1 + (52 / 5) * ε ^ 3 + (9 / 5) * ε ^ 4
  let delta5 : ℝ → ℝ := fun ε ↦
    3 + 72 * ε ^ 3 - 12 * ε ^ 4
  have hFiveEight : 5 ≤ 8 := by
    norm_num
  have hLRawFive : EqModPow 5 L LP := eqModPow_mono hL hFiveEight
  have hHRawFive : EqModPow 5 H HP := eqModPow_mono hH hFiveEight
  have hQRawFive : EqModPow 5 Q QP := eqModPow_mono hQ hFiveEight
  have hURawFive : EqModPow 5 U UP := eqModPow_mono hU hFiveEight
  have hbetaRawFive : EqModPow 5 beta betaP := eqModPow_mono hbeta hFiveEight
  have hdeltaRawFive : EqModPow 5 delta deltaP := eqModPow_mono hdelta hFiveEight
  have hLPFive : EqModPow 5 LP L5 := by
    apply EqModPow.of_factor
      (q := fun ε ↦ 418 * ε + (128 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [LP, L5]
      ring
  have hHPFive : EqModPow 5 HP H5 := by
    apply EqModPow.of_factor (q := fun ε ↦ 6 * ε + 2 * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [HP, H5]
      ring
  have hQPFive : EqModPow 5 QP Q5 := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -(112 / 5) * ε - (157 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [QP, Q5]
      ring
  have hUPFive : EqModPow 5 UP U5 := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -(278 / 5) * ε - (9 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [UP, U5]
      ring
  have hbetaPFive : EqModPow 5 betaP beta5 := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -(8884 / 25) * ε + (5874 / 25) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [betaP, beta5]
      ring
  have hdeltaPFive : EqModPow 5 deltaP delta5 := by
    apply EqModPow.of_factor
      (q := fun ε ↦ (1836 / 25) * ε - (10016 / 25) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [deltaP, delta5]
      ring
  have hLFive : EqModPow 5 L L5 := hLRawFive.trans hLPFive
  have hHFive : EqModPow 5 H H5 := hHRawFive.trans hHPFive
  have hQFive : EqModPow 5 Q Q5 := hQRawFive.trans hQPFive
  have hUFive : EqModPow 5 U U5 := hURawFive.trans hUPFive
  have hbetaFive : EqModPow 5 beta beta5 := hbetaRawFive.trans hbetaPFive
  have hdeltaFive : EqModPow 5 delta delta5 :=
    hdeltaRawFive.trans hdeltaPFive
  have hL5Cont : ContinuousAt L5 0 := by
    dsimp only [L5]
    fun_prop
  have hH5Cont : ContinuousAt H5 0 := by
    dsimp only [H5]
    fun_prop
  have hQ5Cont : ContinuousAt Q5 0 := by
    dsimp only [Q5]
    fun_prop
  have hU5Cont : ContinuousAt U5 0 := by
    dsimp only [U5]
    fun_prop
  have hbeta5Cont : ContinuousAt beta5 0 := by
    dsimp only [beta5]
    fun_prop
  have hdelta5Cont : ContinuousAt delta5 0 := by
    dsimp only [delta5]
    fun_prop
  have hLQFive : EqModPow 5 (fun ε ↦ L ε * Q ε)
      (fun ε ↦ L5 ε * Q5 ε) :=
    hLFive.mul hQFive hL5Cont hQCont
  have hHUFive : EqModPow 5 (fun ε ↦ H ε * U ε)
      (fun ε ↦ H5 ε * U5 ε) :=
    hHFive.mul hUFive hH5Cont hUCont
  have hLQ5Cont : ContinuousAt (fun ε ↦ L5 ε * Q5 ε) 0 :=
    hL5Cont.mul hQ5Cont
  have hHU5Cont : ContinuousAt (fun ε ↦ H5 ε * U5 ε) 0 :=
    hH5Cont.mul hU5Cont
  let numeratorY : ℝ → ℝ := fun ε ↦ delta ε * (H ε * U ε)
  let numeratorY5 : ℝ → ℝ := fun ε ↦ delta5 ε * (H5 ε * U5 ε)
  let denominator : ℝ → ℝ := fun ε ↦ 3 * beta ε
  let denominator5 : ℝ → ℝ := fun ε ↦ 3 * beta5 ε
  let yModel : ℝ → ℝ := fun ε ↦
    1 + (114 / 5) * ε ^ 3 - (69 / 10) * ε ^ 4
  have hNumeratorY : EqModPow 5 numeratorY numeratorY5 := by
    have hproduct := hdeltaFive.mul hHUFive hdelta5Cont hHUCont
    simpa only [numeratorY, numeratorY5] using hproduct
  have hDenominator : EqModPow 5 denominator denominator5 := by
    have hscaled := eqModPow_const_mul_left 3 hbetaFive
    simpa only [denominator, denominator5] using hscaled
  have hNumeratorYPolynomial : EqModPow 5 numeratorY5
      (fun ε ↦ denominator5 ε * yModel ε) := by
    apply EqModPow.of_factor
      (q := fun ε ↦
        -3 * ε *
          (440 * ε ^ 5 - 7120 * ε ^ 4 + 26880 * ε ^ 3 -
            841 * ε ^ 2 + 1514 * ε + 1936) / 50)
    · fun_prop
    · intro ε
      dsimp only [numeratorY5, denominator5, delta5, H5, U5, beta5, yModel]
      ring
  have hdenominatorCont : ContinuousAt denominator 0 := by
    dsimp only [denominator]
    fun_prop
  have hdenominator5Cont : ContinuousAt denominator5 0 := by
    dsimp only [denominator5]
    fun_prop
  have hyModelCont : ContinuousAt yModel 0 := by
    dsimp only [yModel]
    fun_prop
  have hdenominatorZero : denominator 0 ≠ 0 := by
    dsimp only [denominator]
    have hthreeNe : (3 : ℝ) ≠ 0 := by
      norm_num
    exact mul_ne_zero hthreeNe hbetaZero
  have hratioY : EqModPow 5
      (fun ε ↦ numeratorY ε / denominator ε) yModel :=
    eqModPow_div_approx hNumeratorY hDenominator hNumeratorYPolynomial
      hdenominator5Cont hyModelCont hdenominatorCont hdenominatorZero
  have hThreeFive : 3 ≤ 5 := by
    norm_num
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let three : ℝ → ℝ := fun _ ↦ 3
  let six : ℝ → ℝ := fun _ ↦ 6
  have hLThreeRaw : EqModPow 3 L L5 := eqModPow_mono hLFive hThreeFive
  have hQThreeRaw : EqModPow 3 Q Q5 := eqModPow_mono hQFive hThreeFive
  have hdeltaThreeRaw : EqModPow 3 delta delta5 :=
    eqModPow_mono hdeltaFive hThreeFive
  have hbetaThreeRaw : EqModPow 3 beta beta5 :=
    eqModPow_mono hbetaFive hThreeFive
  have hL5Three : EqModPow 3 L5 two := by
    apply EqModPow.of_factor
      (q := fun ε ↦ (298 / 5) + (1 / 5) * ε)
    · fun_prop
    · intro ε
      dsimp only [L5, two]
      ring
  have hQ5Three : EqModPow 3 Q5 one := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -2 - (5 / 2) * ε)
    · fun_prop
    · intro ε
      dsimp only [Q5, one]
      ring
  have hdelta5Three : EqModPow 3 delta5 three := by
    apply EqModPow.of_factor (q := fun ε ↦ 72 - 12 * ε)
    · fun_prop
    · intro ε
      dsimp only [delta5, three]
      ring
  have hbeta5Three : EqModPow 3 beta5 one := by
    apply EqModPow.of_factor
      (q := fun ε ↦ (52 / 5) + (9 / 5) * ε)
    · fun_prop
    · intro ε
      dsimp only [beta5, one]
      ring
  have hLThree : EqModPow 3 L two := hLThreeRaw.trans hL5Three
  have hQThree : EqModPow 3 Q one := hQThreeRaw.trans hQ5Three
  have hdeltaThree : EqModPow 3 delta three :=
    hdeltaThreeRaw.trans hdelta5Three
  have hbetaThree : EqModPow 3 beta one := hbetaThreeRaw.trans hbeta5Three
  have honeCont : ContinuousAt one 0 := by
    dsimp only [one]
    fun_prop
  have htwoCont : ContinuousAt two 0 := by
    dsimp only [two]
    fun_prop
  have hthreeCont : ContinuousAt three 0 := by
    dsimp only [three]
    fun_prop
  have hLQThreeRaw : EqModPow 3 (fun ε ↦ L ε * Q ε)
      (fun ε ↦ two ε * one ε) :=
    hLThree.mul hQThree htwoCont hQCont
  have hLQThree : EqModPow 3 (fun ε ↦ L ε * Q ε) two := by
    apply hLQThreeRaw.congr
    · intro _
      rfl
    · intro ε
      dsimp only [one, two]
      ring
  have hNumeratorXThreeRaw : EqModPow 3
      (fun ε ↦ delta ε * (L ε * Q ε))
      (fun ε ↦ three ε * two ε) :=
    hdeltaThree.mul hLQThree hthreeCont hLQCont
  let numeratorX : ℝ → ℝ := fun ε ↦ delta ε * (L ε * Q ε)
  have hNumeratorXThree : EqModPow 3 numeratorX six := by
    apply hNumeratorXThreeRaw.congr
    · intro _
      rfl
    · intro ε
      dsimp only [three, two, six]
      ring
  have hDenominatorThreeRaw : EqModPow 3 denominator
      (fun ε ↦ 3 * one ε) := by
    have hscaled := eqModPow_const_mul_left 3 hbetaThree
    simpa only [denominator] using hscaled
  have hDenominatorThree : EqModPow 3 denominator three := by
    apply hDenominatorThreeRaw.congr
    · intro _
      rfl
    · intro ε
      dsimp only [one, three]
      ring
  have hDenominatorTimesTwo : EqModPow 3
      (fun ε ↦ denominator ε * two ε) six := by
    have hproduct := hDenominatorThree.mul (EqModPow.refl 3 two)
      hthreeCont htwoCont
    apply hproduct.congr
    · intro _
      rfl
    · intro ε
      dsimp only [three, two, six]
      ring
  have hNumeratorXProduct : EqModPow 3 numeratorX
      (fun ε ↦ denominator ε * two ε) :=
    hNumeratorXThree.trans hDenominatorTimesTwo.symm
  have hratioX : EqModPow 3
      (fun ε ↦ numeratorX ε / denominator ε) two :=
    EqModPow.div_of_eq_mul hNumeratorXProduct hdenominatorCont hdenominatorZero
  have hratioXLift : EqModPow 5
      (fun ε ↦ ε ^ 2 * (numeratorX ε / denominator ε))
      (fun ε ↦ ε ^ 2 * two ε) := by
    have hlift := eqModPow_mul_pow_left (n := 3) (k := 2) hratioX
    simpa only [Nat.reduceAdd] using hlift
  let xFactor : ℝ → ℝ := fun ε ↦
    -(delta ε * ε ^ 2 * L ε * Q ε / (3 * beta ε))
  let yFactor : ℝ → ℝ := fun ε ↦
    -(delta ε * H ε * U ε / (3 * beta ε))
  let xModel : ℝ → ℝ := fun ε ↦ -2 * ε ^ 2
  let yNegativeModel : ℝ → ℝ := fun ε ↦ -yModel ε
  have hxFactor : EqModPow 5 xFactor xModel := by
    have hneg := hratioXLift.neg
    apply hneg.congr
    · intro ε
      dsimp only [xFactor, numeratorX, denominator]
      ring
    · intro ε
      dsimp only [xModel, two]
      ring
  have hyFactor : EqModPow 5 yFactor yNegativeModel := by
    have hneg := hratioY.neg
    apply hneg.congr
    · intro ε
      dsimp only [yFactor, numeratorY, denominator]
      ring
    · intro ε
      rfl
  have hxFactorCont : ContinuousAt xFactor 0 := by
    dsimp only [xFactor]
    fun_prop
  have hyFactorCont : ContinuousAt yFactor 0 := by
    dsimp only [yFactor]
    fun_prop
  have hxModelCont : ContinuousAt xModel 0 := by
    dsimp only [xModel]
    fun_prop
  have hyNegativeModelCont : ContinuousAt yNegativeModel 0 := by
    dsimp only [yNegativeModel, yModel]
    fun_prop
  have hxSquare : EqModPow 5 (fun ε ↦ xFactor ε ^ 2)
      (fun ε ↦ xModel ε ^ 2) := by
    have hsquare := hxFactor.mul hxFactor hxModelCont hxFactorCont
    simpa only [pow_two] using hsquare
  have hySquare : EqModPow 5 (fun ε ↦ yFactor ε ^ 2)
      (fun ε ↦ yNegativeModel ε ^ 2) := by
    have hsquare := hyFactor.mul hyFactor hyNegativeModelCont hyFactorCont
    simpa only [pow_two] using hsquare
  let radicand : ℝ → ℝ := fun ε ↦ xFactor ε ^ 2 + yFactor ε ^ 2
  let model : ℝ → ℝ := fun ε ↦
    1 + (114 / 5) * ε ^ 3 - (49 / 10) * ε ^ 4
  have hradicandRaw : EqModPow 5 radicand
      (fun ε ↦ xModel ε ^ 2 + yNegativeModel ε ^ 2) := by
    have hsum := hxSquare.add hySquare
    simpa only [radicand] using hsum
  have hradicandPolynomial : EqModPow 5
      (fun ε ↦ xModel ε ^ 2 + yNegativeModel ε ^ 2)
      (fun ε ↦ model ε ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε ↦ 2 * ε ^ 2 * (59 * ε - 228) / 5)
    · fun_prop
    · intro ε
      dsimp only [xModel, yNegativeModel, yModel, model]
      ring
  have hradicand : EqModPow 5 radicand (fun ε ↦ model ε ^ 2) :=
    hradicandRaw.trans hradicandPolynomial
  have hzeroFive : 0 < 5 := by
    norm_num
  have hxZero : xFactor 0 = 0 := by
    have hzero := eqModPow_apply_zero hzeroFive hxFactor
    norm_num [xModel] at hzero ⊢
    exact hzero
  have hyZero : yFactor 0 = -1 := by
    have hzero := eqModPow_apply_zero hzeroFive hyFactor
    norm_num [yNegativeModel, yModel] at hzero ⊢
    exact hzero
  have hradicandCont : ContinuousAt radicand 0 := by
    dsimp only [radicand]
    fun_prop
  have hmodelCont : ContinuousAt model 0 := by
    dsimp only [model]
    fun_prop
  have hradicandPos : 0 < radicand 0 := by
    norm_num [radicand, hxZero, hyZero]
  have hmodelPos : 0 < model 0 := by
    norm_num [model]
  have hsqrt : EqModPow 5 (fun ε ↦ Real.sqrt (radicand ε)) model :=
    EqModPow.sqrt_of_sq hradicand hradicandCont hmodelCont
      hradicandPos hmodelPos
  apply hsqrt.congr
  · intro ε
    dsimp only [radicand, xFactor, yFactor, numeratorX, numeratorY,
      denominator, delta, beta, w₁, w₂, L, H, Q, U, p, h]
    simp only [secondStepDisplacementFactor, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  · intro _
    rfl


/-- Along a path whose shape coordinate agrees with the polynomial slow graph
through order four, the initial normalized gradient norm equals
`1 + 2 * ε ^ 4` up to `O(ε ^ 6)`. -/
theorem slowInitialGradientRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
        (1 + 2 * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let radicand : ℝ → ℝ := fun ε ↦ 1 + (p ε * ε ^ 2) ^ 2
  let model : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 4
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  have hpZero : p 0 = 2 := by
    have hzeroRule := mem_of_mem_nhds hpDiff.eq_zero_imp
    have hzeroPower : (0 : ℝ) ^ 5 = 0 := by
      norm_num
    have hzeroValue := hzeroRule hzeroPower
    norm_num [p₀] at hzeroValue
    exact sub_eq_zero.mp hzeroValue
  have hpContinuous : ContinuousAt p 0 := by
    simpa only [ContinuousAt, hpZero] using hpTendsto
  have hthreeFive : 3 < 5 := by
    norm_num
  have hthreeFour : 3 < 4 := by
    norm_num
  have hfiveThree :
      (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow hthreeFive).isBigO
  have hfourThree :
      (fun ε : ℝ ↦ ε ^ 4) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow hthreeFour).isBigO
  have hp₀SubTwo : (fun ε ↦ p₀ ε - 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hcubic :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)).const_mul_left
        (198 / 5 : ℝ)
    have hquartic := hfourThree.const_mul_left (9 / 5 : ℝ)
    have hraw := hcubic.sub hquartic
    have hidentity (ε : ℝ) :
        (198 / 5 : ℝ) * ε ^ 3 - (9 / 5 : ℝ) * ε ^ 4 = p₀ ε - 2 := by
      dsimp only [p₀]
      ring
    exact hraw.congr_left hidentity
  have hpSubTwo : (fun ε ↦ p ε - 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hsum := (hpDiff.trans hfiveThree).add hp₀SubTwo
    have hidentity (ε : ℝ) : (p ε - p₀ ε) + (p₀ ε - 2) = p ε - 2 := by
      ring
    exact hsum.congr_left hidentity
  have hpPlusTwo : (fun ε ↦ p ε + 2) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    have htendsto : Tendsto (fun ε ↦ p ε + 2) (𝓝 0) (𝓝 4) := by
      convert hpTendsto.add tendsto_const_nhds using 1
      norm_num
    exact htendsto.isBigO_one ℝ
  have hpSquareSubFour :
      (fun ε ↦ p ε ^ 2 - 4) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hproduct := hpSubTwo.mul hpPlusTwo
    have hidentity (ε : ℝ) : (p ε - 2) * (p ε + 2) = p ε ^ 2 - 4 := by
      ring
    simpa only [mul_one] using hproduct.congr_left hidentity
  have hmainSeventh :
      (fun ε ↦ (p ε ^ 2 - 4) * ε ^ 4) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) := by
    have hproduct := hpSquareSubFour.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 4) (𝓝 0))
    simpa only [← pow_add, Nat.reduceAdd] using hproduct
  have hsixSeven : 6 < 7 := by
    norm_num
  have hsixEight : 6 < 8 := by
    norm_num
  have hsevenSix :
      (fun ε : ℝ ↦ ε ^ 7) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) :=
    (Asymptotics.isLittleO_pow_pow hsixSeven).isBigO
  have heightSix :
      (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) :=
    (Asymptotics.isLittleO_pow_pow hsixEight).isBigO
  have hradicandSquare : EqModPow 6 radicand (fun ε ↦ model ε ^ 2) := by
    have hmain := hmainSeventh.trans hsevenSix
    have htail := heightSix.const_mul_left (4 : ℝ)
    have hdifference := hmain.sub htail
    have hidentity (ε : ℝ) :
        radicand ε - model ε ^ 2 =
          (p ε ^ 2 - 4) * ε ^ 4 - 4 * ε ^ 8 := by
      dsimp only [radicand, model]
      ring
    have hidentity' (ε : ℝ) :
        (p ε ^ 2 - 4) * ε ^ 4 - 4 * ε ^ 8 =
          radicand ε - model ε ^ 2 := (hidentity ε).symm
    exact EqModPow.of_isBigO (hdifference.congr_left hidentity')
  have hradicandContinuous : ContinuousAt radicand 0 := by
    dsimp only [radicand]
    fun_prop
  have hmodelContinuous : ContinuousAt model 0 := by
    dsimp only [model]
    fun_prop
  have hradicandPos : 0 < radicand 0 := by
    norm_num [radicand, hpZero]
  have hmodelPos : 0 < model 0 := by
    norm_num [model]
  have hsqrt := EqModPow.sqrt_of_sq hradicandSquare hradicandContinuous
    hmodelContinuous hradicandPos hmodelPos
  have hremainder := EqModPow.to_isBigO hsqrt
  have hleft (ε : ℝ) :
      Real.sqrt (radicand ε) - model ε =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
          (1 + 2 * ε ^ 4) := by
    rw [initialGradientNorm_eq_sqrt]
  exact hremainder.congr' (Eventually.of_forall hleft)
    (Eventually.of_forall fun _ ↦ rfl)

/-- Along a path whose shape coordinate agrees with the polynomial slow graph
through order four, the intermediate normalized gradient norm equals
`1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6` up to `O(ε ^ 7)`. -/
theorem slowIntermediateGradientRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
        (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  let D : ℝ → ℝ := fun ε ↦ 3 * B ε
  let q : ℝ → ℝ := fun ε ↦
    1 - 2 * (p ε + 1) * ε ^ 3 * (1 + ε) / D ε
  let v : ℝ → ℝ := fun ε ↦
    p ε - 2 * (p ε + 1) * (1 + ε ^ 3) / D ε
  let q₀ : ℝ → ℝ := fun ε ↦
    1 - 2 * (p₀ ε + 1) * ε ^ 3 * (1 + ε) / D ε
  let v₀ : ℝ → ℝ := fun ε ↦
    p₀ ε - 2 * (p₀ ε + 1) * (1 + ε ^ 3) / D ε
  let model : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6
  let radicand : ℝ → ℝ := fun ε ↦ q ε ^ 2 + (ε ^ 2 * v ε) ^ 2
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  have hpZero : p 0 = 2 := by
    have hzeroRule := mem_of_mem_nhds hpDiff.eq_zero_imp
    have hzeroPower : (0 : ℝ) ^ 5 = 0 := by
      norm_num
    have hzeroValue := hzeroRule hzeroPower
    norm_num [p₀] at hzeroValue
    exact sub_eq_zero.mp hzeroValue
  have hpContinuous : ContinuousAt p 0 := by
    simpa only [ContinuousAt, hpZero] using hpTendsto
  have hDContinuous : ContinuousAt D 0 := by
    dsimp only [D, B]
    fun_prop
  have hDZero : D 0 ≠ 0 := by
    norm_num [D, B]
  have hDInvContinuous : ContinuousAt (fun ε ↦ (D ε)⁻¹) 0 :=
    hDContinuous.inv₀ hDZero
  have hDInvOrder : (fun ε ↦ (D ε)⁻¹) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hDInvContinuous.isBigO
  have honePlusOrder : (fun ε : ℝ ↦ 1 + ε) =O[𝓝 0]
      (fun _ : ℝ ↦ (1 : ℝ)) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ 1 + ε) 0 := by
      fun_prop
    exact hcontinuous.isBigO
  have hqDiffEighth : (fun ε ↦ q ε - q₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
    have hscale := hpDiff.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0))
    have hscale' : (fun ε ↦ (p ε - p₀ ε) * ε ^ 3) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [← pow_add, Nat.reduceAdd] using hscale
    have hbounded := hscale'.mul honePlusOrder
    have hbounded' :
        (fun ε ↦ (p ε - p₀ ε) * ε ^ 3 * (1 + ε)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [mul_one] using hbounded
    have hquotient := hbounded'.mul hDInvOrder
    have hquotient' :
        (fun ε ↦ (p ε - p₀ ε) * ε ^ 3 * (1 + ε) * (D ε)⁻¹) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [mul_one] using hquotient
    have hscaled := hquotient'.const_mul_left (-2 : ℝ)
    have hidentity (ε : ℝ) :
        -2 * ((p ε - p₀ ε) * ε ^ 3 * (1 + ε) * (D ε)⁻¹) =
          q ε - q₀ ε := by
      dsimp only [q, q₀]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    exact hscaled.congr_left hidentity
  let qFactor : ℝ → ℝ := fun ε ↦
    ((-288 / 5 : ℝ) + (48 / 5) * ε + (672 / 5) * ε ^ 2 +
      (336 / 5) * ε ^ 3) / D ε
  have hqFactorContinuous : ContinuousAt qFactor 0 := by
    dsimp only [qFactor]
    fun_prop
  have hqFactorOrder : qFactor =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hqFactorContinuous.isBigO
  have hqFactorProduct : (fun ε ↦ qFactor ε * ε ^ 7) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    simpa only [one_mul] using hqFactorOrder.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 7) (𝓝 0))
  have hq₀ModelEventually :
      (fun ε ↦ qFactor ε * ε ^ 7) =ᶠ[𝓝 0] (fun ε ↦ q₀ ε - model ε) := by
    filter_upwards [hDContinuous.eventually_ne hDZero] with ε hDε
    dsimp only [qFactor, q₀, model, p₀]
    field_simp [hDε]
    dsimp only [D, B]
    ring
  have hq₀Model : (fun ε ↦ q₀ ε - model ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    hqFactorProduct.congr' hq₀ModelEventually (Eventually.of_forall fun _ ↦ rfl)
  have hsevenEight : 7 < 8 := by
    norm_num
  have heightSeven : (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isLittleO_pow_pow hsevenEight).isBigO
  have hqModel : (fun ε ↦ q ε - model ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    have hsum := (hqDiffEighth.trans heightSeven).add hq₀Model
    have hidentity (ε : ℝ) : (q ε - q₀ ε) + (q₀ ε - model ε) =
        q ε - model ε := by
      ring
    exact hsum.congr_left hidentity
  let vDiffFactor : ℝ → ℝ := fun ε ↦
    1 - 2 * (1 + ε ^ 3) / D ε
  have hvDiffFactorContinuous : ContinuousAt vDiffFactor 0 := by
    dsimp only [vDiffFactor]
    fun_prop
  have hvDiffFactorOrder : vDiffFactor =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hvDiffFactorContinuous.isBigO
  have hvDiff : (fun ε ↦ v ε - v₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hproduct := hpDiff.mul hvDiffFactorOrder
    have hproduct' : (fun ε ↦ (p ε - p₀ ε) * vDiffFactor ε) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [mul_one] using hproduct
    have hidentity (ε : ℝ) :
        (p ε - p₀ ε) * vDiffFactor ε = v ε - v₀ ε := by
      dsimp only [vDiffFactor, v, v₀]
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      ring
    exact hproduct'.congr_left hidentity
  let v₀Factor : ℝ → ℝ := fun ε ↦
    ((228 / 5 : ℝ) + (21 / 5) * ε + (792 / 5) * ε ^ 3 +
      (558 / 5) * ε ^ 4 - (27 / 5) * ε ^ 5) / D ε
  have hv₀FactorContinuous : ContinuousAt v₀Factor 0 := by
    dsimp only [v₀Factor]
    fun_prop
  have hv₀FactorOrder : v₀Factor =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hv₀FactorContinuous.isBigO
  have hv₀FactorProduct : (fun ε ↦ v₀Factor ε * ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    simpa only [one_mul] using hv₀FactorOrder.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0))
  have hv₀Eventually : (fun ε ↦ v₀Factor ε * ε ^ 3) =ᶠ[𝓝 0] v₀ := by
    filter_upwards [hDContinuous.eventually_ne hDZero] with ε hDε
    dsimp only [v₀Factor, v₀, p₀]
    field_simp [hDε]
    dsimp only [D, B]
    ring
  have hv₀Order : v₀ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    hv₀FactorProduct.congr' hv₀Eventually (Eventually.of_forall fun _ ↦ rfl)
  have hthreeFive : 3 < 5 := by
    norm_num
  have hfiveThree : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow hthreeFive).isBigO
  have hvOrder : v =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hsum := (hvDiff.trans hfiveThree).add hv₀Order
    have hidentity (ε : ℝ) : (v ε - v₀ ε) + v₀ ε = v ε := by
      ring
    exact hsum.congr_left hidentity
  have hwOrder : (fun ε ↦ ε ^ 2 * v ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hproduct :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0)).mul hvOrder
    simpa only [← pow_add, Nat.reduceAdd] using hproduct
  have hwSquareTenth : (fun ε ↦ (ε ^ 2 * v ε) ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 10) := by
    simpa only [← pow_mul, Nat.reduceMul] using hwOrder.pow 2
  have hsevenTen : 7 < 10 := by
    norm_num
  have htenSeven : (fun ε : ℝ ↦ ε ^ 10) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isLittleO_pow_pow hsevenTen).isBigO
  have hqContinuous : ContinuousAt q 0 := by
    dsimp only [q]
    fun_prop
  have hmodelContinuous : ContinuousAt model 0 := by
    dsimp only [model]
    fun_prop
  have hqSquare : EqModPow 7 (fun ε ↦ q ε ^ 2) (fun ε ↦ model ε ^ 2) := by
    have hqCongruence := EqModPow.of_isBigO hqModel
    have hproduct := hqCongruence.mul hqCongruence hmodelContinuous hqContinuous
    simpa only [pow_two] using hproduct
  have hradicandSquare : EqModPow 7 radicand (fun ε ↦ model ε ^ 2) := by
    have hsum := (EqModPow.to_isBigO hqSquare).add (hwSquareTenth.trans htenSeven)
    have hidentity (ε : ℝ) :
        (q ε ^ 2 - model ε ^ 2) + (ε ^ 2 * v ε) ^ 2 =
          radicand ε - model ε ^ 2 := by
      dsimp only [radicand]
      ring
    exact EqModPow.of_isBigO (hsum.congr_left hidentity)
  have hvContinuous : ContinuousAt v 0 := by
    dsimp only [v]
    fun_prop
  have hradicandContinuous : ContinuousAt radicand 0 := by
    dsimp only [radicand]
    fun_prop
  have hradicandPos : 0 < radicand 0 := by
    norm_num [radicand, q, v, D, B, hpZero]
  have hmodelPos : 0 < model 0 := by
    norm_num [model]
  have hsqrt := EqModPow.sqrt_of_sq hradicandSquare hradicandContinuous
    hmodelContinuous hradicandPos hmodelPos
  have hremainder := EqModPow.to_isBigO hsqrt
  have hleft (ε : ℝ) :
      Real.sqrt (radicand ε) - model ε =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
          (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6) := by
    rw [intermediateGradientNorm_eq_sqrt]
    congr 2
  exact hremainder.congr' (Eventually.of_forall hleft)
    (Eventually.of_forall fun _ ↦ rfl)

set_option maxHeartbeats 1000000 in
-- The explicit two-leg rational and square-root normalization has a large elaboration term.
/-- Along a path whose shape and high-eigenvalue coordinates agree with the
polynomial slow graph through order four, the final normalized gradient norm
equals `1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6` up to `O(ε ^ 7)`. -/
theorem slowFinalGradientRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
        (1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  let C : ℝ → ℝ := fun ε ↦
    (1 + ε ^ 3) ^ 2 + p ε * ε ^ 6 * (1 + ε) ^ 2
  let a : ℝ → ℝ := fun ε ↦
    h ε * p ε - h ε * (p ε) ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C ε +
      1 / B ε
  let b : ℝ → ℝ := fun ε ↦
    1 / B ε - h ε * p ε * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C ε
  let d : ℝ → ℝ := fun ε ↦
    h ε - h ε * (1 + ε ^ 3) ^ 2 / C ε + 1 / B ε
  let A : ℝ → ℝ := fun ε ↦ ε ^ 4 * a ε
  let E : ℝ → ℝ := fun ε ↦ ε ^ 2 * b ε
  let disc : ℝ → ℝ := fun ε ↦ (d ε - A ε) ^ 2 + 4 * (E ε) ^ 2
  let gap : ℝ → ℝ := fun ε ↦ Real.sqrt (disc ε)
  let low : ℝ → ℝ := fun ε ↦ (A ε + d ε - gap ε) / 2
  let high : ℝ → ℝ := fun ε ↦ (A ε + d ε + gap ε) / 2
  let denomRad : ℝ → ℝ := fun ε ↦
    (d ε - low ε) ^ 2 + (E ε) ^ 2
  let denom : ℝ → ℝ := fun ε ↦ Real.sqrt (denomRad ε)
  let q₁ : ℝ → ℝ := fun ε ↦
    1 - 2 * (p ε + 1) * ε ^ 3 * (1 + ε) / (3 * B ε)
  let v₁ : ℝ → ℝ := fun ε ↦
    p ε - 2 * (p ε + 1) * (1 + ε ^ 3) / (3 * B ε)
  let L : ℝ → ℝ := fun ε ↦ (a ε * d ε - (b ε) ^ 2) / high ε
  let H : ℝ → ℝ := high
  let Q : ℝ → ℝ := fun ε ↦
    ((d ε - low ε) * q₁ ε - ε ^ 4 * b ε * v₁ ε) / denom ε
  let U : ℝ → ℝ := fun ε ↦
    (b ε * q₁ ε + (d ε - low ε) * v₁ ε) / denom ε
  let w₁ : ℝ → ℝ := fun ε ↦ ε * L ε * Q ε - 2 * H ε * U ε
  let w₂ : ℝ → ℝ := fun ε ↦ H ε * U ε - 2 * ε ^ 3 * L ε * Q ε
  let beta : ℝ → ℝ := fun ε ↦
    ε ^ 3 * L ε * Q ε * w₁ ε + H ε * U ε * w₂ ε
  let delta : ℝ → ℝ := fun ε ↦ L ε * (Q ε) ^ 2 + H ε * (U ε) ^ 2
  let q₂ : ℝ → ℝ := fun ε ↦
    Q ε - ε ^ 3 * delta ε * w₁ ε / (3 * beta ε)
  let v₂ : ℝ → ℝ := fun ε ↦ U ε - delta ε * w₂ ε / (3 * beta ε)
  let model : ℝ → ℝ := fun ε ↦
    1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6
  let radicand : ℝ → ℝ := fun ε ↦ (q₂ ε) ^ 2 + (ε ^ 2 * v₂ ε) ^ 2
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hp₀Continuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hp₀Continuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hh₀Continuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hh₀Continuous.tendsto using 1
    norm_num [h₀]
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFive).add hh₀Tendsto
  have hpZero : p 0 = 2 := by
    have hzeroRule := mem_of_mem_nhds hpDiff.eq_zero_imp
    have hzeroPower : (0 : ℝ) ^ 5 = 0 := by
      norm_num
    have hzeroValue := hzeroRule hzeroPower
    norm_num [p₀] at hzeroValue
    exact sub_eq_zero.mp hzeroValue
  have hhZero : h 0 = 1 := by
    have hzeroRule := mem_of_mem_nhds hhDiff.eq_zero_imp
    have hzeroPower : (0 : ℝ) ^ 5 = 0 := by
      norm_num
    have hzeroValue := hzeroRule hzeroPower
    norm_num [h₀] at hzeroValue
    exact sub_eq_zero.mp hzeroValue
  have hpContinuous : ContinuousAt p 0 := by
    simpa only [ContinuousAt, hpZero] using hpTendsto
  have hhContinuous : ContinuousAt h 0 := by
    simpa only [ContinuousAt, hhZero] using hhTendsto
  have hthreeFive : 3 < 5 := by
    norm_num
  have hfiveThree : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow hthreeFive).isBigO
  have hp₀Three : (fun ε ↦ p₀ ε - 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hcubic :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)).const_mul_left
        (198 / 5 : ℝ)
    have hthreeFour : 3 < 4 := by
      norm_num
    have hquartic :=
      (Asymptotics.isLittleO_pow_pow hthreeFour).isBigO.const_mul_left (-(9 / 5 : ℝ))
    have hsum := hcubic.add hquartic
    have hidentity (ε : ℝ) :
        (198 / 5) * ε ^ 3 + -(9 / 5) * ε ^ 4 = p₀ ε - 2 := by
      dsimp only [p₀]
      ring
    exact hsum.congr_left hidentity
  have hh₀Three : (fun ε ↦ h₀ ε - 1) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hcubic :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)).const_mul_left
        (8 : ℝ)
    have hidentity (ε : ℝ) : 8 * ε ^ 3 = h₀ ε - 1 := by
      dsimp only [h₀]
      ring
    exact hcubic.congr_left hidentity
  have hpThree : (fun ε ↦ p ε - 2) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hsum := (hpDiff.trans hfiveThree).add hp₀Three
    have hidentity (ε : ℝ) :
        (p ε - p₀ ε) + (p₀ ε - 2) = p ε - 2 := by
      ring
    exact hsum.congr_left hidentity
  have hhThree : (fun ε ↦ h ε - 1) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hsum := (hhDiff.trans hfiveThree).add hh₀Three
    have hidentity (ε : ℝ) :
        (h ε - h₀ ε) + (h₀ ε - 1) = h ε - 1 := by
      ring
    exact hsum.congr_left hidentity
  have hpOrder : p =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := hpContinuous.isBigO
  have hhOrder : h =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := hhContinuous.isBigO
  have hBContinuous : ContinuousAt B 0 := by
    dsimp only [B]
    fun_prop
  have hBZero : B 0 ≠ 0 := by
    norm_num [B]
  have hBInvContinuous : ContinuousAt (fun ε ↦ (B ε)⁻¹) 0 :=
    hBContinuous.inv₀ hBZero
  have hBInvOrder : (fun ε ↦ (B ε)⁻¹) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hBInvContinuous.isBigO
  have hCContinuous : ContinuousAt C 0 := by
    dsimp only [C]
    fun_prop
  have hCZero : C 0 ≠ 0 := by
    norm_num [C, hpZero]
  have hCInvContinuous : ContinuousAt (fun ε ↦ (C ε)⁻¹) 0 :=
    hCContinuous.inv₀ hCZero
  have hCInvOrder : (fun ε ↦ (C ε)⁻¹) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hCInvContinuous.isBigO
  let D : ℝ → ℝ := fun ε ↦ 3 * B ε
  let q₁₀ : ℝ → ℝ := fun ε ↦
    1 - 2 * (p₀ ε + 1) * ε ^ 3 * (1 + ε) / D ε
  let v₁₀ : ℝ → ℝ := fun ε ↦
    p₀ ε - 2 * (p₀ ε + 1) * (1 + ε ^ 3) / D ε
  let q₁P : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6
  let v₁P : ℝ → ℝ := fun ε ↦ (76 / 5) * ε ^ 3
  have hDContinuous : ContinuousAt D 0 := by
    dsimp only [D]
    fun_prop
  have hDZero : D 0 ≠ 0 := by
    norm_num [D, B]
  have hDInvOrder : (fun ε ↦ (D ε)⁻¹) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (hDContinuous.inv₀ hDZero).isBigO
  have honePlusOrder : (fun ε : ℝ ↦ 1 + ε) =O[𝓝 0]
      (fun _ : ℝ ↦ (1 : ℝ)) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ 1 + ε) 0 := by
      fun_prop
    exact hcontinuous.isBigO
  have hq₁DiffEighth : (fun ε ↦ q₁ ε - q₁₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
    have hscale := hpDiff.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0))
    have hscale' : (fun ε ↦ (p ε - p₀ ε) * ε ^ 3) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [← pow_add, Nat.reduceAdd] using hscale
    have hbounded := hscale'.mul honePlusOrder
    have hbounded' :
        (fun ε ↦ (p ε - p₀ ε) * ε ^ 3 * (1 + ε)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [mul_one] using hbounded
    have hquotient := hbounded'.mul hDInvOrder
    have hquotient' :
        (fun ε ↦ (p ε - p₀ ε) * ε ^ 3 * (1 + ε) * (D ε)⁻¹) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [mul_one] using hquotient
    have hscaled := hquotient'.const_mul_left (-2 : ℝ)
    have hidentity (ε : ℝ) :
        -2 * ((p ε - p₀ ε) * ε ^ 3 * (1 + ε) * (D ε)⁻¹) =
          q₁ ε - q₁₀ ε := by
      dsimp only [q₁, q₁₀, D]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    exact hscaled.congr_left hidentity
  let q₁Factor : ℝ → ℝ := fun ε ↦
    ((48 / 5 : ℝ) * (1 + ε) * (7 * ε ^ 2 + 7 * ε - 6)) / D ε
  have hq₁FactorContinuous : ContinuousAt q₁Factor 0 := by
    dsimp only [q₁Factor]
    fun_prop
  have hq₁FactorProduct : (fun ε ↦ q₁Factor ε * ε ^ 7) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    have hproduct := hq₁FactorContinuous.isBigO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 7) (𝓝 0))
    simpa only [one_mul] using hproduct
  have hq₁₀Eventually :
      (fun ε ↦ q₁Factor ε * ε ^ 7) =ᶠ[𝓝 0] (fun ε ↦ q₁₀ ε - q₁P ε) := by
    filter_upwards [hDContinuous.eventually_ne hDZero] with ε hDε
    dsimp only [q₁Factor, q₁₀, q₁P, p₀]
    field_simp [hDε]
    dsimp only [D, B]
    ring
  have hq₁₀ : (fun ε ↦ q₁₀ ε - q₁P ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    hq₁FactorProduct.congr' hq₁₀Eventually (Eventually.of_forall fun _ ↦ rfl)
  have hsevenEight : 7 < 8 := by
    norm_num
  have heightSeven : (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isLittleO_pow_pow hsevenEight).isBigO
  have hq₁ : EqModPow 7 q₁ q₁P := by
    have hsum := (hq₁DiffEighth.trans heightSeven).add hq₁₀
    have hidentity (ε : ℝ) :
        (q₁ ε - q₁₀ ε) + (q₁₀ ε - q₁P ε) = q₁ ε - q₁P ε := by
      ring
    exact EqModPow.of_isBigO (hsum.congr_left hidentity)
  let vDiffFactor : ℝ → ℝ := fun ε ↦
    1 - 2 * (1 + ε ^ 3) / D ε
  have hvDiffFactorContinuous : ContinuousAt vDiffFactor 0 := by
    dsimp only [vDiffFactor]
    fun_prop
  have hvDiff : (fun ε ↦ v₁ ε - v₁₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hproduct := hpDiff.mul hvDiffFactorContinuous.isBigO
    have hproduct' : (fun ε ↦ (p ε - p₀ ε) * vDiffFactor ε) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [mul_one] using hproduct
    have hidentity (ε : ℝ) :
        (p ε - p₀ ε) * vDiffFactor ε = v₁ ε - v₁₀ ε := by
      dsimp only [vDiffFactor, v₁, v₁₀, D]
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      ring
    exact hproduct'.congr_left hidentity
  let v₁Factor : ℝ → ℝ := fun ε ↦
    (-(3 / 5 : ℝ) * (1 + ε) * (9 * ε ^ 3 - 119 * ε ^ 2 + 7 * ε - 7)) / D ε
  have hv₁FactorContinuous : ContinuousAt v₁Factor 0 := by
    dsimp only [v₁Factor]
    fun_prop
  have hv₁FactorProduct : (fun ε ↦ v₁Factor ε * ε ^ 4) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    have hproduct := hv₁FactorContinuous.isBigO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 4) (𝓝 0))
    simpa only [one_mul] using hproduct
  have hv₁₀Eventually :
      (fun ε ↦ v₁Factor ε * ε ^ 4) =ᶠ[𝓝 0] (fun ε ↦ v₁₀ ε - v₁P ε) := by
    filter_upwards [hDContinuous.eventually_ne hDZero] with ε hDε
    dsimp only [v₁Factor, v₁₀, v₁P, p₀]
    field_simp [hDε]
    dsimp only [D, B]
    ring
  have hv₁₀ : (fun ε ↦ v₁₀ ε - v₁P ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) :=
    hv₁FactorProduct.congr' hv₁₀Eventually (Eventually.of_forall fun _ ↦ rfl)
  have hfourFive : 4 < 5 := by
    norm_num
  have hfiveFour : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hfourFive).isBigO
  have hv₁ : EqModPow 4 v₁ v₁P := by
    have hsum := (hvDiff.trans hfiveFour).add hv₁₀
    have hidentity (ε : ℝ) :
        (v₁ ε - v₁₀ ε) + (v₁₀ ε - v₁P ε) = v₁ ε - v₁P ε := by
      ring
    exact EqModPow.of_isBigO (hsum.congr_left hidentity)
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let onePlus : ℝ → ℝ := fun ε ↦ 1 + ε
  let onePlusCube : ℝ → ℝ := fun ε ↦ 1 + ε ^ 3
  have honeContinuous : ContinuousAt one 0 := by
    dsimp only [one]
    fun_prop
  have htwoContinuous : ContinuousAt two 0 := by
    dsimp only [two]
    fun_prop
  have honePlusContinuous : ContinuousAt onePlus 0 := by
    dsimp only [onePlus]
    fun_prop
  have honePlusCubeContinuous : ContinuousAt onePlusCube 0 := by
    dsimp only [onePlusCube]
    fun_prop
  have honePlusOrder' : onePlus =O[𝓝 0] one := honePlusContinuous.isBigO
  have honePlusCubeOrder : onePlusCube =O[𝓝 0] one :=
    honePlusCubeContinuous.isBigO
  have honePlusSquareOrder : (fun ε ↦ (onePlus ε) ^ 2) =O[𝓝 0] one := by
    have hproduct := honePlusOrder'.mul honePlusOrder'
    simpa only [pow_two, one_mul, one] using hproduct
  have hthreeOne : 1 < 3 := by
    norm_num
  have hpowThreeOne : (fun ε : ℝ ↦ ε ^ 3) =O[𝓝 0] (fun ε : ℝ ↦ ε) :=
    by
      simpa only [pow_one] using (Asymptotics.isLittleO_pow_pow hthreeOne).isBigO
  have hpOneOrder : (fun ε ↦ p ε - 2) =O[𝓝 0] (fun ε : ℝ ↦ ε) :=
    hpThree.trans hpowThreeOne
  have hhOneOrder : (fun ε ↦ h ε - 1) =O[𝓝 0] (fun ε : ℝ ↦ ε) :=
    hhThree.trans hpowThreeOne
  have hpOne : EqModPow 1 p two := by
    apply EqModPow.of_isBigO
    simpa only [two, pow_one] using hpOneOrder
  have hhOne : EqModPow 1 h one := by
    apply EqModPow.of_isBigO
    simpa only [one, pow_one] using hhOneOrder
  have honePlusOne : EqModPow 1 onePlus one := by
    apply EqModPow.of_factor (q := one)
    · exact honeContinuous
    · intro ε
      simp only [onePlus, one]
      ring
  have honePlusCubeOne : EqModPow 1 onePlusCube one := by
    apply EqModPow.of_factor (q := fun ε ↦ ε ^ 2)
    · fun_prop
    · intro ε
      simp only [onePlusCube, one]
      ring
  have hCOne : EqModPow 1 C one := by
    let CFactor : ℝ → ℝ := fun ε ↦
      ε ^ 2 * (2 + ε ^ 3) + p ε * ε ^ 5 * (1 + ε) ^ 2
    have hfactorContinuous : ContinuousAt CFactor 0 := by
      dsimp only [CFactor]
      fun_prop
    apply EqModPow.of_factor hfactorContinuous
    intro ε
    dsimp only [C, CFactor, one]
    ring
  let dCoeff : ℝ → ℝ := fun ε ↦
    h ε * p ε * (onePlus ε) ^ 2 / C ε
  have hhpOne : EqModPow 1 (fun ε ↦ h ε * p ε)
      (fun ε ↦ one ε * two ε) :=
    hhOne.mul hpOne honeContinuous hpContinuous
  have honePlusSquareOne : EqModPow 1 (fun ε ↦ (onePlus ε) ^ 2)
      (fun ε ↦ (one ε) ^ 2) := by
    have hsquare := honePlusOne.mul honePlusOne honeContinuous honePlusContinuous
    simpa only [pow_two] using hsquare
  have hdNumeratorOne : EqModPow 1
      (fun ε ↦ h ε * p ε * (onePlus ε) ^ 2)
      (fun ε ↦ (one ε * two ε) * (one ε) ^ 2) := by
    have hmodelContinuous : ContinuousAt (fun ε ↦ one ε * two ε) 0 := by
      fun_prop
    have hsquareContinuous : ContinuousAt (fun ε ↦ (onePlus ε) ^ 2) 0 := by
      fun_prop
    exact hhpOne.mul honePlusSquareOne hmodelContinuous hsquareContinuous
  have hCTwoOne : EqModPow 1 (fun ε ↦ C ε * two ε)
      (fun ε ↦ one ε * two ε) :=
    hCOne.mul (EqModPow.refl 1 two) honeContinuous htwoContinuous
  have hdNumeratorTarget : EqModPow 1
      (fun ε ↦ h ε * p ε * (onePlus ε) ^ 2)
      (fun ε ↦ C ε * two ε) := by
    have hmodelIdentity (ε : ℝ) :
        (one ε * two ε) * (one ε) ^ 2 = one ε * two ε := by
      simp only [one, two]
      norm_num
    exact (hdNumeratorOne.congr (fun _ ↦ rfl) (fun ε ↦ (hmodelIdentity ε).symm)).trans
      hCTwoOne.symm
  have hdCoeff : EqModPow 1 dCoeff two := by
    have hquotient := EqModPow.div_of_eq_mul hdNumeratorTarget hCContinuous hCZero
    simpa only [dCoeff] using hquotient
  let iBP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - ε ^ 4 + 4 * ε ^ 6
  have hiBMul : EqModPow 7 (fun ε ↦ B ε * iBP ε) one := by
    apply EqModPow.of_factor
      (q := fun ε ↦ 4 * ε ^ 3 + 8 * ε ^ 2 - ε - 4)
    · fun_prop
    · intro ε
      simp only [B, iBP, one]
      ring
  have hiB : EqModPow 7 (fun ε ↦ 1 / B ε) iBP := by
    simpa only [one_div] using EqModPow.inv_of_mul_eq_one hiBMul hBContinuous hBZero
  let dExtra : ℝ → ℝ := fun ε ↦ ε ^ 6 * dCoeff ε
  have hdExtra : EqModPow 7 dExtra (fun ε ↦ ε ^ 6 * two ε) := by
    simpa only [Nat.reduceAdd] using
      (eqModPow_mul_pow_left (n := 1) (k := 6) hdCoeff)
  let dP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - ε ^ 4 + 6 * ε ^ 6
  have hdIdentity : ∀ᶠ ε in 𝓝 0, d ε = 1 / B ε + dExtra ε := by
    filter_upwards [hCContinuous.eventually_ne hCZero] with ε hCε
    dsimp only [d, dExtra, dCoeff, onePlus]
    field_simp [hCε]
    dsimp only [C]
    ring
  have hdSum : EqModPow 7 (fun ε ↦ 1 / B ε + dExtra ε)
      (fun ε ↦ iBP ε + ε ^ 6 * two ε) :=
    hiB.add hdExtra
  have hd : EqModPow 7 d dP := by
    apply EqModPow.of_isBigO
    refine (EqModPow.to_isBigO hdSum).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hdIdentity] with ε hdε
    rw [hdε]
    dsimp only [iBP, two, dP]
    ring
  let pP : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3
  let hP : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpP₀Four : EqModPow 4 p p₀ := by
    apply EqModPow.of_isBigO
    exact hpDiff.trans hfiveFour
  have hp₀PFour : EqModPow 4 p₀ pP := by
    apply EqModPow.of_factor (q := fun _ ↦ (-(9 / 5 : ℝ)))
    · fun_prop
    · intro ε
      dsimp only [p₀, pP]
      ring
  have hpFour : EqModPow 4 p pP := hpP₀Four.trans hp₀PFour
  have hhFour : EqModPow 4 h hP := by
    have hdiff : EqModPow 4 h h₀ := by
      apply EqModPow.of_isBigO
      exact hhDiff.trans hfiveFour
    exact hdiff.congr (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hpPContinuous : ContinuousAt pP 0 := by
    dsimp only [pP]
    fun_prop
  have hhPContinuous : ContinuousAt hP 0 := by
    dsimp only [hP]
    fun_prop
  have hhpFour : EqModPow 4 (fun ε ↦ h ε * p ε)
      (fun ε ↦ hP ε * pP ε) :=
    hhFour.mul hpFour hhPContinuous hpContinuous
  let iB4 : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3
  have hfourSeven : 4 < 7 := by
    norm_num
  have hsevenFour : (fun ε : ℝ ↦ ε ^ 7) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hfourSeven).isBigO
  have hiBFourRaw : EqModPow 4 (fun ε ↦ 1 / B ε) iBP := by
    apply EqModPow.of_isBigO
    exact (EqModPow.to_isBigO hiB).trans hsevenFour
  have hiBP4 : EqModPow 4 iBP iB4 := by
    apply EqModPow.of_factor (q := fun ε ↦ -1 + 4 * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [iBP, iB4]
      ring
  have hiBFour : EqModPow 4 (fun ε ↦ 1 / B ε) iB4 :=
    hiBFourRaw.trans hiBP4
  let aSix : ℝ → ℝ := fun ε ↦
    h ε * (p ε) ^ 2 * ε ^ 6 * (onePlus ε) ^ 2 * (C ε)⁻¹
  have hpSquareOrder : (fun ε ↦ (p ε) ^ 2) =O[𝓝 0] one := by
    have hsquare := hpOrder.mul hpOrder
    simpa only [pow_two, mul_one, one] using hsquare
  have haCoeffOrder :
      (fun ε ↦ h ε * (p ε) ^ 2 * (onePlus ε) ^ 2 * (C ε)⁻¹) =O[𝓝 0] one := by
    have hhpSquare := hhOrder.mul hpSquareOrder
    have hhpSquare' : (fun ε ↦ h ε * (p ε) ^ 2) =O[𝓝 0] one := by
      simpa only [mul_one, one] using hhpSquare
    have honePlusProduct := hhpSquare'.mul honePlusSquareOrder
    have honePlusProduct' :
        (fun ε ↦ h ε * (p ε) ^ 2 * (onePlus ε) ^ 2) =O[𝓝 0] one := by
      simpa only [mul_one, one] using honePlusProduct
    have htotal := honePlusProduct'.mul hCInvOrder
    simpa only [mul_one, one] using htotal
  have haSixOrder : aSix =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) := by
    have hproduct :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 6) (𝓝 0)).mul haCoeffOrder
    have hidentity (ε : ℝ) :
        ε ^ 6 * (h ε * (p ε) ^ 2 * (onePlus ε) ^ 2 * (C ε)⁻¹) = aSix ε := by
      dsimp only [aSix]
      ring
    simpa only [mul_one, one] using hproduct.congr_left hidentity
  have hfourSix : 4 < 6 := by
    norm_num
  have hsixFour : (fun ε : ℝ ↦ ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) :=
    (Asymptotics.isLittleO_pow_pow hfourSix).isBigO
  have haSixFour : EqModPow 4 aSix (fun _ ↦ 0) := by
    apply EqModPow.of_isBigO
    simpa only [sub_zero] using haSixOrder.trans hsixFour
  let aP : ℝ → ℝ := fun ε ↦ 3 + (268 / 5) * ε ^ 3
  have haComponents : EqModPow 4
      (fun ε ↦ h ε * p ε - aSix ε + 1 / B ε)
      (fun ε ↦ hP ε * pP ε - 0 + iB4 ε) :=
    (hhpFour.sub haSixFour).add hiBFour
  have ha : EqModPow 4 a aP := by
    have haRaw : EqModPow 4 a
        (fun ε ↦ hP ε * pP ε - 0 + iB4 ε) := by
      apply haComponents.congr
      · intro ε
        dsimp only [a, aSix, onePlus]
        rw [div_eq_mul_inv]
      · intro _
        rfl
    have haPolynomial : EqModPow 4
        (fun ε ↦ hP ε * pP ε - 0 + iB4 ε) aP := by
      apply EqModPow.of_factor (q := fun ε ↦ (1584 / 5 : ℝ) * ε ^ 2)
      · fun_prop
      · intro ε
        dsimp only [hP, pP, iB4, aP]
        ring
    exact haRaw.trans haPolynomial
  let bCoeff : ℝ → ℝ := fun ε ↦
    h ε * p ε * onePlus ε * onePlusCube ε / C ε
  have hbNumeratorOne : EqModPow 1
      (fun ε ↦ h ε * p ε * onePlus ε * onePlusCube ε)
      (fun ε ↦ one ε * two ε) := by
    have hfirstModelContinuous : ContinuousAt
        (fun ε ↦ one ε * two ε) 0 := by
      fun_prop
    have hsecondModelContinuous : ContinuousAt
        (fun ε ↦ one ε * two ε * one ε) 0 := by
      fun_prop
    have hfirst := hhpOne.mul honePlusOne hfirstModelContinuous honePlusContinuous
    have hsecond := hfirst.mul honePlusCubeOne hsecondModelContinuous
      honePlusCubeContinuous
    apply hsecond.congr (fun _ ↦ rfl)
    intro ε
    simp only [one, two]
    norm_num
  have hbNumeratorTarget : EqModPow 1
      (fun ε ↦ h ε * p ε * onePlus ε * onePlusCube ε)
      (fun ε ↦ C ε * two ε) :=
    hbNumeratorOne.trans hCTwoOne.symm
  have hbCoeff : EqModPow 1 bCoeff two := by
    have hquotient := EqModPow.div_of_eq_mul hbNumeratorTarget hCContinuous hCZero
    simpa only [bCoeff] using hquotient
  let bTerm : ℝ → ℝ := fun ε ↦ ε ^ 3 * bCoeff ε
  have hbTerm : EqModPow 4 bTerm (fun ε ↦ ε ^ 3 * two ε) := by
    simpa only [Nat.reduceAdd] using
      (eqModPow_mul_pow_left (n := 1) (k := 3) hbCoeff)
  let bP : ℝ → ℝ := fun ε ↦ 1 - 4 * ε ^ 3
  have hbComponents : EqModPow 4 (fun ε ↦ 1 / B ε - bTerm ε)
      (fun ε ↦ iB4 ε - ε ^ 3 * two ε) :=
    hiBFour.sub hbTerm
  have hb : EqModPow 4 b bP := by
    apply hbComponents.congr
    · intro ε
      dsimp only [b, bTerm, bCoeff, onePlus, onePlusCube]
      rw [div_eq_mul_inv]
      ring
    · intro ε
      dsimp only [iB4, two, bP]
      ring
  have haContinuous : ContinuousAt a 0 := by
    dsimp only [a]
    fun_prop
  have hbContinuous : ContinuousAt b 0 := by
    dsimp only [b]
    fun_prop
  have hdContinuous : ContinuousAt d 0 := by
    dsimp only [d]
    fun_prop
  have haZero : a 0 = 3 := by
    norm_num [a, B, C, hpZero, hhZero]
  have hbZero : b 0 = 1 := by
    norm_num [b, B, C, hpZero, hhZero]
  have hdZero : d 0 = 1 := by
    norm_num [d, B, C, hpZero, hhZero]
  let AP : ℝ → ℝ := fun ε ↦ 3 * ε ^ 4
  have hALift : EqModPow 8 A (fun ε ↦ ε ^ 4 * aP ε) := by
    have hlift := eqModPow_mul_pow_left (n := 4) (k := 4) ha
    simpa only [Nat.reduceAdd, A] using hlift
  have heightSeven' : (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := heightSeven
  have hAApprox : EqModPow 7 A (fun ε ↦ ε ^ 4 * aP ε) := by
    apply EqModPow.of_isBigO
    exact (EqModPow.to_isBigO hALift).trans heightSeven'
  have hAPolynomial : EqModPow 7 (fun ε ↦ ε ^ 4 * aP ε) AP := by
    apply EqModPow.of_factor (q := fun _ ↦ (268 / 5 : ℝ))
    · fun_prop
    · intro ε
      dsimp only [aP, AP]
      ring
  have hA : EqModPow 7 A AP := hAApprox.trans hAPolynomial
  have hbPContinuous : ContinuousAt bP 0 := by
    dsimp only [bP]
    fun_prop
  have hbSquare : EqModPow 4 (fun ε ↦ (b ε) ^ 2)
      (fun ε ↦ (bP ε) ^ 2) := by
    have hsquare := hb.mul hb hbPContinuous hbContinuous
    simpa only [pow_two] using hsquare
  have hESquareLift : EqModPow 8 (fun ε ↦ ε ^ 4 * (b ε) ^ 2)
      (fun ε ↦ ε ^ 4 * (bP ε) ^ 2) := by
    have hlift := eqModPow_mul_pow_left (n := 4) (k := 4) hbSquare
    simpa only [Nat.reduceAdd] using hlift
  have hESquareApprox : EqModPow 7 (fun ε ↦ (E ε) ^ 2)
      (fun ε ↦ ε ^ 4 * (bP ε) ^ 2) := by
    have hraw : EqModPow 8 (fun ε ↦ (E ε) ^ 2)
        (fun ε ↦ ε ^ 4 * (bP ε) ^ 2) := by
      apply hESquareLift.congr
      · intro ε
        dsimp only [E]
        ring
      · intro _
        rfl
    apply EqModPow.of_isBigO
    exact (EqModPow.to_isBigO hraw).trans heightSeven'
  have hESquarePolynomial : EqModPow 7
      (fun ε ↦ ε ^ 4 * (bP ε) ^ 2) (fun ε ↦ ε ^ 4) := by
    apply EqModPow.of_factor (q := fun ε ↦ -8 + 16 * ε ^ 3)
    · fun_prop
    · intro ε
      dsimp only [bP]
      ring
  have hESquare : EqModPow 7 (fun ε ↦ (E ε) ^ 2)
      (fun ε ↦ ε ^ 4) := hESquareApprox.trans hESquarePolynomial
  let dMinusAP : ℝ → ℝ := fun ε ↦ dP ε - AP ε
  have hdMinusA : EqModPow 7 (fun ε ↦ d ε - A ε) dMinusAP := by
    have hsub := hd.sub hA
    simpa only [dMinusAP] using hsub
  have hdMinusAContinuous : ContinuousAt (fun ε ↦ d ε - A ε) 0 := by
    dsimp only [A]
    fun_prop
  have hdMinusAPContinuous : ContinuousAt dMinusAP 0 := by
    dsimp only [dMinusAP, dP, AP]
    fun_prop
  have hdMinusASquare : EqModPow 7 (fun ε ↦ (d ε - A ε) ^ 2)
      (fun ε ↦ (dMinusAP ε) ^ 2) := by
    have hsquare := hdMinusA.mul hdMinusA hdMinusAPContinuous hdMinusAContinuous
    simpa only [pow_two] using hsquare
  have hfourESquare : EqModPow 7 (fun ε ↦ 4 * (E ε) ^ 2)
      (fun ε ↦ 4 * ε ^ 4) :=
    eqModPow_const_mul_left 4 hESquare
  have hdiscRaw : EqModPow 7 disc
      (fun ε ↦ (dMinusAP ε) ^ 2 + 4 * ε ^ 4) := by
    have hsum := hdMinusASquare.add hfourESquare
    simpa only [disc] using hsum
  let gapP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - 2 * ε ^ 4 + 6 * ε ^ 6
  have hdiscPolynomial : EqModPow 7
      (fun ε ↦ (dMinusAP ε) ^ 2 + 4 * ε ^ 4)
      (fun ε ↦ (gapP ε) ^ 2) := by
    apply EqModPow.of_factor (q := fun ε ↦ 8 + 12 * ε - 24 * ε ^ 3)
    · fun_prop
    · intro ε
      dsimp only [dMinusAP, dP, AP, gapP]
      ring
  have hdisc : EqModPow 7 disc (fun ε ↦ (gapP ε) ^ 2) :=
    hdiscRaw.trans hdiscPolynomial
  have hAContinuous : ContinuousAt A 0 := by
    dsimp only [A]
    fun_prop
  have hEContinuous : ContinuousAt E 0 := by
    dsimp only [E]
    fun_prop
  have hdiscContinuous : ContinuousAt disc 0 := by
    dsimp only [disc]
    fun_prop
  have hgapPContinuous : ContinuousAt gapP 0 := by
    dsimp only [gapP]
    fun_prop
  have hdiscPos : 0 < disc 0 := by
    norm_num [disc, A, E, haZero, hbZero, hdZero]
  have hgapPPos : 0 < gapP 0 := by
    norm_num [gapP]
  have hgap : EqModPow 7 gap gapP := by
    have hsqrt := EqModPow.sqrt_of_sq hdisc hdiscContinuous hgapPContinuous
      hdiscPos hgapPPos
    simpa only [gap] using hsqrt
  let lowP : ℝ → ℝ := fun ε ↦ 2 * ε ^ 4
  have hlowNumerator : EqModPow 7 (fun ε ↦ A ε + d ε - gap ε)
      (fun ε ↦ AP ε + dP ε - gapP ε) :=
    hA.add hd |>.sub hgap
  have hlowScaled : EqModPow 7
      (fun ε ↦ (1 / 2 : ℝ) * (A ε + d ε - gap ε))
      (fun ε ↦ (1 / 2 : ℝ) * (AP ε + dP ε - gapP ε)) :=
    eqModPow_const_mul_left (1 / 2) hlowNumerator
  have hlow : EqModPow 7 low lowP := by
    apply hlowScaled.congr
    · intro ε
      dsimp only [low]
      ring
    · intro ε
      dsimp only [AP, dP, gapP, lowP]
      ring
  have hgapContinuous : ContinuousAt gap 0 := by
    dsimp only [gap]
    fun_prop
  have hlowContinuous : ContinuousAt low 0 := by
    dsimp only [low]
    fun_prop
  let denomP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 + 6 * ε ^ 6
  let dMinusLowP : ℝ → ℝ := fun ε ↦ dP ε - lowP ε
  have hdMinusLow : EqModPow 7 (fun ε ↦ d ε - low ε) dMinusLowP := by
    have hsub := hd.sub hlow
    simpa only [dMinusLowP] using hsub
  have hdMinusLowContinuous : ContinuousAt (fun ε ↦ d ε - low ε) 0 := by
    fun_prop
  have hdMinusLowPContinuous : ContinuousAt dMinusLowP 0 := by
    dsimp only [dMinusLowP, dP, lowP]
    fun_prop
  have hdMinusLowSquare : EqModPow 7
      (fun ε ↦ (d ε - low ε) ^ 2)
      (fun ε ↦ (dMinusLowP ε) ^ 2) := by
    have hsquare := hdMinusLow.mul hdMinusLow hdMinusLowPContinuous
      hdMinusLowContinuous
    simpa only [pow_two] using hsquare
  have hdenomRadRaw : EqModPow 7 denomRad
      (fun ε ↦ (dMinusLowP ε) ^ 2 + ε ^ 4) := by
    have hsum := hdMinusLowSquare.add hESquare
    simpa only [denomRad] using hsum
  have hdenomRadPolynomial : EqModPow 7
      (fun ε ↦ (dMinusLowP ε) ^ 2 + ε ^ 4)
      (fun ε ↦ (denomP ε) ^ 2) := by
    apply EqModPow.of_factor (q := fun ε ↦ 2 + (11 / 4) * ε - 6 * ε ^ 3)
    · fun_prop
    · intro ε
      dsimp only [dMinusLowP, dP, lowP, denomP]
      ring
  have hdenomRad : EqModPow 7 denomRad (fun ε ↦ (denomP ε) ^ 2) :=
    hdenomRadRaw.trans hdenomRadPolynomial
  have hdenomRadContinuous : ContinuousAt denomRad 0 := by
    dsimp only [denomRad]
    fun_prop
  have hdenomPContinuous : ContinuousAt denomP 0 := by
    dsimp only [denomP]
    fun_prop
  have hdenomRadPos : 0 < denomRad 0 := by
    norm_num [denomRad, E, low, A, gap, disc, haZero, hbZero, hdZero]
  have hdenomPPos : 0 < denomP 0 := by
    norm_num [denomP]
  have hdenom : EqModPow 7 denom denomP := by
    have hsqrt := EqModPow.sqrt_of_sq hdenomRad hdenomRadContinuous
      hdenomPContinuous hdenomRadPos hdenomPPos
    simpa only [denom] using hsqrt
  let highP : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3 + 6 * ε ^ 6
  have hhighNumerator : EqModPow 7 (fun ε ↦ A ε + d ε + gap ε)
      (fun ε ↦ AP ε + dP ε + gapP ε) := by
    have hsum := hA.add hd
    exact hsum.add hgap
  have hhighScaled : EqModPow 7
      (fun ε ↦ (1 / 2 : ℝ) * (A ε + d ε + gap ε))
      (fun ε ↦ (1 / 2 : ℝ) * (AP ε + dP ε + gapP ε)) :=
    eqModPow_const_mul_left (1 / 2) hhighNumerator
  have hhigh : EqModPow 7 high highP := by
    apply hhighScaled.congr
    · intro ε
      dsimp only [high]
      ring
    · intro ε
      dsimp only [AP, dP, gapP, highP]
      ring
  have hhighContinuous : ContinuousAt high 0 := by
    dsimp only [high]
    fun_prop
  have hzeroSeven : 0 < 7 := by
    norm_num
  have hhighZero : high 0 = 1 := by
    have hzero := eqModPow_apply_zero hzeroSeven hhigh
    norm_num [highP] at hzero ⊢
    exact hzero
  have hhighZeroNe : high 0 ≠ 0 := by
    rw [hhighZero]
    norm_num
  have haPContinuous : ContinuousAt aP 0 := by
    dsimp only [aP]
    fun_prop
  have hdPContinuous : ContinuousAt dP 0 := by
    dsimp only [dP]
    fun_prop
  have hhighPContinuous : ContinuousAt highP 0 := by
    dsimp only [highP]
    fun_prop
  have hdFour : EqModPow 4 d dP :=
    eqModPow_mono hd hfourSeven.le
  have hhighFour : EqModPow 4 high highP :=
    eqModPow_mono hhigh hfourSeven.le
  have had : EqModPow 4 (fun ε ↦ a ε * d ε)
      (fun ε ↦ aP ε * dP ε) :=
    ha.mul hdFour haPContinuous hdContinuous
  have hLNumerator : EqModPow 4 (fun ε ↦ a ε * d ε - b ε ^ 2)
      (fun ε ↦ aP ε * dP ε - bP ε ^ 2) :=
    had.sub hbSquare
  let LP : ℝ → ℝ := fun ε ↦ 2 + (298 / 5) * ε ^ 3
  have hLPolynomial : EqModPow 4
      (fun ε ↦ aP ε * dP ε - bP ε ^ 2)
      (fun ε ↦ highP ε * LP ε) := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -(180 * ε ^ 5 + 268 * ε ^ 3 - 10 * ε ^ 2 + 15) / 5)
    · fun_prop
    · intro ε
      dsimp only [aP, dP, bP, highP, LP]
      ring
  have hLPContinuous : ContinuousAt LP 0 := by
    dsimp only [LP]
    fun_prop
  have hhighTimesLP : EqModPow 4 (fun ε ↦ high ε * LP ε)
      (fun ε ↦ highP ε * LP ε) := by
    have hrefl := EqModPow.refl 4 LP
    exact hhighFour.mul hrefl hhighPContinuous hLPContinuous
  have hLProduct : EqModPow 4 (fun ε ↦ a ε * d ε - b ε ^ 2)
      (fun ε ↦ high ε * LP ε) :=
    (hLNumerator.trans hLPolynomial).trans hhighTimesLP.symm
  have hL : EqModPow 4 L LP := by
    have hquotient := EqModPow.div_of_eq_mul hLProduct hhighContinuous hhighZeroNe
    simpa only [L] using hquotient
  have hdenomContinuous : ContinuousAt denom 0 := by
    dsimp only [denom]
    exact hdenomRadContinuous.sqrt
  have hdenomZero : denom 0 = 1 := by
    have hzero := eqModPow_apply_zero hzeroSeven hdenom
    norm_num [denomP] at hzero ⊢
    exact hzero
  have hdenomZeroNe : denom 0 ≠ 0 := by
    rw [hdenomZero]
    norm_num
  have hq₁Continuous : ContinuousAt q₁ 0 := by
    dsimp only [q₁]
    fun_prop
  have hv₁Continuous : ContinuousAt v₁ 0 := by
    dsimp only [v₁]
    fun_prop
  have hq₁PContinuous : ContinuousAt q₁P 0 := by
    dsimp only [q₁P]
    fun_prop
  have hv₁PContinuous : ContinuousAt v₁P 0 := by
    dsimp only [v₁P]
    fun_prop
  have hQFirstTerm : EqModPow 7
      (fun ε ↦ (d ε - low ε) * q₁ ε)
      (fun ε ↦ dMinusLowP ε * q₁P ε) :=
    hdMinusLow.mul hq₁ hdMinusLowPContinuous hq₁Continuous
  have hbV₁ : EqModPow 4 (fun ε ↦ b ε * v₁ ε)
      (fun ε ↦ bP ε * v₁P ε) :=
    hb.mul hv₁ hbPContinuous hv₁Continuous
  have hQSecondLift : EqModPow 8
      (fun ε ↦ ε ^ 4 * (b ε * v₁ ε))
      (fun ε ↦ ε ^ 4 * (bP ε * v₁P ε)) := by
    have hlift := eqModPow_mul_pow_left (n := 4) (k := 4) hbV₁
    simpa only [Nat.reduceAdd] using hlift
  have hQSecondApprox : EqModPow 7
      (fun ε ↦ ε ^ 4 * b ε * v₁ ε)
      (fun ε ↦ ε ^ 4 * bP ε * v₁P ε) := by
    have hlower := eqModPow_mono hQSecondLift hsevenEight.le
    apply hlower.congr
    · intro ε
      ring
    · intro ε
      ring
  have hQSecondPolynomial : EqModPow 7
      (fun ε ↦ ε ^ 4 * bP ε * v₁P ε) (fun _ ↦ 0) := by
    apply EqModPow.of_factor (q := fun ε ↦ (76 / 5) * (1 - 4 * ε ^ 3))
    · fun_prop
    · intro ε
      dsimp only [bP, v₁P]
      ring
  have hQSecond : EqModPow 7 (fun ε ↦ ε ^ 4 * b ε * v₁ ε)
      (fun _ ↦ 0) := hQSecondApprox.trans hQSecondPolynomial
  have hQNumerator : EqModPow 7
      (fun ε ↦ (d ε - low ε) * q₁ ε - ε ^ 4 * b ε * v₁ ε)
      (fun ε ↦ dMinusLowP ε * q₁P ε - 0) :=
    hQFirstTerm.sub hQSecond
  let QP : ℝ → ℝ := fun ε ↦
    1 - 2 * ε ^ 3 - (5 / 2) * ε ^ 4 - (112 / 5) * ε ^ 6
  have hQPolynomial : EqModPow 7
      (fun ε ↦ dMinusLowP ε * q₁P ε - 0)
      (fun ε ↦ denomP ε * QP ε) := by
    apply EqModPow.of_factor
      (q := fun ε ↦ ε * (284 * ε ^ 2 - 5) / 20)
    · fun_prop
    · intro ε
      dsimp only [dMinusLowP, dP, lowP, q₁P, denomP, QP]
      ring
  have hQPContinuous : ContinuousAt QP 0 := by
    dsimp only [QP]
    fun_prop
  have hdenomTimesQP : EqModPow 7 (fun ε ↦ denom ε * QP ε)
      (fun ε ↦ denomP ε * QP ε) := by
    have hrefl := EqModPow.refl 7 QP
    exact hdenom.mul hrefl hdenomPContinuous hQPContinuous
  have hQProduct : EqModPow 7
      (fun ε ↦ (d ε - low ε) * q₁ ε - ε ^ 4 * b ε * v₁ ε)
      (fun ε ↦ denom ε * QP ε) :=
    (hQNumerator.trans hQPolynomial).trans hdenomTimesQP.symm
  have hQ : EqModPow 7 Q QP := by
    have hquotient := EqModPow.div_of_eq_mul hQProduct hdenomContinuous hdenomZeroNe
    simpa only [Q] using hquotient
  have hq₁Four : EqModPow 4 q₁ q₁P :=
    eqModPow_mono hq₁ hfourSeven.le
  have hdMinusLowFour : EqModPow 4 (fun ε ↦ d ε - low ε) dMinusLowP :=
    eqModPow_mono hdMinusLow hfourSeven.le
  have hUFirstTerm : EqModPow 4 (fun ε ↦ b ε * q₁ ε)
      (fun ε ↦ bP ε * q₁P ε) :=
    hb.mul hq₁Four hbPContinuous hq₁Continuous
  have hUSecondTerm : EqModPow 4 (fun ε ↦ (d ε - low ε) * v₁ ε)
      (fun ε ↦ dMinusLowP ε * v₁P ε) :=
    hdMinusLowFour.mul hv₁ hdMinusLowPContinuous hv₁Continuous
  have hUNumerator : EqModPow 4
      (fun ε ↦ b ε * q₁ ε + (d ε - low ε) * v₁ ε)
      (fun ε ↦ bP ε * q₁P ε + dMinusLowP ε * v₁P ε) :=
    hUFirstTerm.add hUSecondTerm
  let UP : ℝ → ℝ := fun ε ↦ 1 + (56 / 5) * ε ^ 3
  have hUPolynomial : EqModPow 4
      (fun ε ↦ bP ε * q₁P ε + dMinusLowP ε * v₁P ε)
      (fun ε ↦ denomP ε * UP ε) := by
    apply EqModPow.of_factor
      (q := fun ε ↦ (1136 * ε ^ 5 - 96 * ε ^ 3 - 284 * ε ^ 2 + 5) / 10)
    · fun_prop
    · intro ε
      dsimp only [bP, q₁P, dMinusLowP, dP, lowP, denomP, v₁P, UP]
      ring
  have hUPContinuous : ContinuousAt UP 0 := by
    dsimp only [UP]
    fun_prop
  have hdenomFour : EqModPow 4 denom denomP :=
    eqModPow_mono hdenom hfourSeven.le
  have hdenomTimesUP : EqModPow 4 (fun ε ↦ denom ε * UP ε)
      (fun ε ↦ denomP ε * UP ε) := by
    have hrefl := EqModPow.refl 4 UP
    exact hdenomFour.mul hrefl hdenomPContinuous hUPContinuous
  have hUProduct : EqModPow 4
      (fun ε ↦ b ε * q₁ ε + (d ε - low ε) * v₁ ε)
      (fun ε ↦ denom ε * UP ε) :=
    (hUNumerator.trans hUPolynomial).trans hdenomTimesUP.symm
  have hU : EqModPow 4 U UP := by
    have hquotient := EqModPow.div_of_eq_mul hUProduct hdenomContinuous hdenomZeroNe
    simpa only [U] using hquotient
  have hH : EqModPow 4 H highP := by
    apply hhighFour.congr
    · intro _
      rfl
    · intro _
      rfl
  let H4 : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3
  have hhighPToH4 : EqModPow 4 highP H4 := by
    apply EqModPow.of_factor (q := fun ε ↦ 6 * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [highP, H4]
      ring
  have hHCubic : EqModPow 4 H H4 := hH.trans hhighPToH4
  let Q4 : ℝ → ℝ := fun ε ↦ 1 - 2 * ε ^ 3
  have hQFourRaw : EqModPow 4 Q QP :=
    eqModPow_mono hQ hfourSeven.le
  have hQPToQ4 : EqModPow 4 QP Q4 := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -(5 / 2 : ℝ) - (112 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [QP, Q4]
      ring
  have hQFour : EqModPow 4 Q Q4 := hQFourRaw.trans hQPToQ4
  have hH4Continuous : ContinuousAt H4 0 := by
    dsimp only [H4]
    fun_prop
  have hQ4Continuous : ContinuousAt Q4 0 := by
    dsimp only [Q4]
    fun_prop
  have hLContinuous : ContinuousAt L 0 := by
    dsimp only [L]
    fun_prop
  have hHContinuous : ContinuousAt H 0 := by
    dsimp only [H]
    exact hhighContinuous
  have hQContinuous : ContinuousAt Q 0 := by
    dsimp only [Q]
    fun_prop
  have hUContinuous : ContinuousAt U 0 := by
    dsimp only [U]
    fun_prop
  have hIdContinuous : ContinuousAt (fun ε : ℝ ↦ ε) 0 := by
    fun_prop
  have hεCongruence : EqModPow 4 (fun ε : ℝ ↦ ε) (fun ε ↦ ε) :=
    EqModPow.refl 4 (fun ε : ℝ ↦ ε)
  have hεL : EqModPow 4 (fun ε ↦ ε * L ε)
      (fun ε ↦ ε * LP ε) :=
    hεCongruence.mul hL hIdContinuous hLContinuous
  have hεLPContinuous : ContinuousAt (fun ε ↦ ε * LP ε) 0 := by
    fun_prop
  have hεLQ : EqModPow 4 (fun ε ↦ ε * L ε * Q ε)
      (fun ε ↦ ε * LP ε * Q4 ε) :=
    hεL.mul hQFour hεLPContinuous hQContinuous
  have hHU : EqModPow 4 (fun ε ↦ H ε * U ε)
      (fun ε ↦ H4 ε * UP ε) :=
    hHCubic.mul hU hH4Continuous hUContinuous
  have htwoHU : EqModPow 4 (fun ε ↦ 2 * (H ε * U ε))
      (fun ε ↦ 2 * (H4 ε * UP ε)) :=
    eqModPow_const_mul_left 2 hHU
  have hw₁Raw : EqModPow 4
      (fun ε ↦ ε * L ε * Q ε - 2 * (H ε * U ε))
      (fun ε ↦ ε * LP ε * Q4 ε - 2 * (H4 ε * UP ε)) :=
    hεLQ.sub htwoHU
  let w₁P : ℝ → ℝ := fun ε ↦
    -2 + 2 * ε - (92 / 5) * ε ^ 3
  have hw₁Polynomial : EqModPow 4
      (fun ε ↦ ε * LP ε * Q4 ε - 2 * (H4 ε * UP ε)) w₁P := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -2 * (298 * ε ^ 3 - 112 * ε ^ 2 - 139) / 5)
    · fun_prop
    · intro ε
      dsimp only [LP, Q4, H4, UP, w₁P]
      ring
  have hw₁ : EqModPow 4 w₁ w₁P := by
    have hraw := hw₁Raw.trans hw₁Polynomial
    apply hraw.congr
    · intro ε
      dsimp only [w₁]
      ring
    · intro _
      rfl
  have hLQ : EqModPow 4 (fun ε ↦ L ε * Q ε)
      (fun ε ↦ LP ε * Q4 ε) :=
    hL.mul hQFour hLPContinuous hQContinuous
  have hpowThreeContinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 3) 0 := by
    fun_prop
  have hLQContinuous : ContinuousAt (fun ε ↦ L ε * Q ε) 0 := by
    fun_prop
  have hpowThreeCongruence : EqModPow 4 (fun ε : ℝ ↦ ε ^ 3)
      (fun ε ↦ ε ^ 3) := EqModPow.refl 4 (fun ε : ℝ ↦ ε ^ 3)
  have hpowThreeLQ : EqModPow 4 (fun ε ↦ ε ^ 3 * (L ε * Q ε))
      (fun ε ↦ ε ^ 3 * (LP ε * Q4 ε)) :=
    hpowThreeCongruence.mul hLQ hpowThreeContinuous hLQContinuous
  have htwoPowThreeLQ : EqModPow 4
      (fun ε ↦ 2 * (ε ^ 3 * (L ε * Q ε)))
      (fun ε ↦ 2 * (ε ^ 3 * (LP ε * Q4 ε))) :=
    eqModPow_const_mul_left 2 hpowThreeLQ
  have hw₂Raw : EqModPow 4
      (fun ε ↦ H ε * U ε - 2 * (ε ^ 3 * (L ε * Q ε)))
      (fun ε ↦ H4 ε * UP ε - 2 * (ε ^ 3 * (LP ε * Q4 ε))) :=
    hHU.sub htwoPowThreeLQ
  let w₂P : ℝ → ℝ := fun ε ↦ 1 + (26 / 5) * ε ^ 3
  have hw₂Polynomial : EqModPow 4
      (fun ε ↦ H4 ε * UP ε - 2 * (ε ^ 3 * (LP ε * Q4 ε))) w₂P := by
    apply EqModPow.of_factor
      (q := fun ε ↦ 4 * ε ^ 2 * (298 * ε ^ 3 - 167) / 5)
    · fun_prop
    · intro ε
      dsimp only [H4, UP, LP, Q4, w₂P]
      ring
  have hw₂ : EqModPow 4 w₂ w₂P := by
    have hraw := hw₂Raw.trans hw₂Polynomial
    apply hraw.congr
    · intro ε
      dsimp only [w₂]
      ring
    · intro _
      rfl
  have hw₁Continuous : ContinuousAt w₁ 0 := by
    dsimp only [w₁]
    fun_prop
  have hw₂Continuous : ContinuousAt w₂ 0 := by
    dsimp only [w₂]
    fun_prop
  have hzeroOne : 0 < 1 := by
    norm_num
  have honeFour : 1 ≤ 4 := by
    norm_num
  have hLOneRaw : EqModPow 1 L LP := eqModPow_mono hL honeFour
  have hLPOne : EqModPow 1 LP two := by
    apply EqModPow.of_factor (q := fun ε ↦ (298 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [LP, two]
      ring
  have hLOne : EqModPow 1 L two := hLOneRaw.trans hLPOne
  have hQOneRaw : EqModPow 1 Q Q4 := eqModPow_mono hQFour honeFour
  have hQ4One : EqModPow 1 Q4 one := by
    apply EqModPow.of_factor (q := fun ε ↦ -2 * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [Q4, one]
      ring
  have hQOne : EqModPow 1 Q one := hQOneRaw.trans hQ4One
  let negTwo : ℝ → ℝ := fun _ ↦ -2
  have hw₁OneRaw : EqModPow 1 w₁ w₁P := eqModPow_mono hw₁ honeFour
  have hw₁POne : EqModPow 1 w₁P negTwo := by
    apply EqModPow.of_factor (q := fun ε ↦ 2 - (92 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [w₁P, negTwo]
      ring
  have hw₁One : EqModPow 1 w₁ negTwo := hw₁OneRaw.trans hw₁POne
  have htwoContinuous : ContinuousAt two 0 := by
    dsimp only [two]
    fun_prop
  have honeContinuous' : ContinuousAt one 0 := by
    dsimp only [one]
    fun_prop
  have hnegTwoContinuous : ContinuousAt negTwo 0 := by
    dsimp only [negTwo]
    fun_prop
  have hLQOne : EqModPow 1 (fun ε ↦ L ε * Q ε)
      (fun ε ↦ two ε * one ε) :=
    hLOne.mul hQOne htwoContinuous hQContinuous
  have htwoOneContinuous : ContinuousAt (fun ε ↦ two ε * one ε) 0 := by
    fun_prop
  have hLQw₁One : EqModPow 1 (fun ε ↦ L ε * Q ε * w₁ ε)
      (fun ε ↦ two ε * one ε * negTwo ε) :=
    hLQOne.mul hw₁One htwoOneContinuous hw₁Continuous
  let negFour : ℝ → ℝ := fun _ ↦ -4
  have hcoreOne : EqModPow 1 (fun ε ↦ L ε * Q ε * w₁ ε) negFour := by
    apply hLQw₁One.congr
    · intro _
      rfl
    · intro ε
      dsimp only [two, one, negTwo, negFour]
      ring
  have hbetaFirstLift : EqModPow 4
      (fun ε ↦ ε ^ 3 * (L ε * Q ε * w₁ ε))
      (fun ε ↦ ε ^ 3 * negFour ε) := by
    have hlift := eqModPow_mul_pow_left (n := 1) (k := 3) hcoreOne
    simpa only [Nat.reduceAdd] using hlift
  have hbetaFirst : EqModPow 4
      (fun ε ↦ ε ^ 3 * L ε * Q ε * w₁ ε)
      (fun ε ↦ -4 * ε ^ 3) := by
    apply hbetaFirstLift.congr
    · intro ε
      simp only [mul_assoc]
    · intro ε
      dsimp only [negFour]
      ring
  have hHUPContinuous : ContinuousAt (fun ε ↦ H4 ε * UP ε) 0 := by
    fun_prop
  have hHUw₂ : EqModPow 4 (fun ε ↦ H ε * U ε * w₂ ε)
      (fun ε ↦ H4 ε * UP ε * w₂P ε) :=
    hHU.mul hw₂ hHUPContinuous hw₂Continuous
  let betaSecondP : ℝ → ℝ := fun ε ↦ 1 + (72 / 5) * ε ^ 3
  have hbetaSecondPolynomial : EqModPow 4
      (fun ε ↦ H4 ε * UP ε * w₂P ε) betaSecondP := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -4 * ε ^ 2 * (728 * ε ^ 3 - 159) / 25)
    · fun_prop
    · intro ε
      dsimp only [H4, UP, w₂P, betaSecondP]
      ring
  have hbetaSecond : EqModPow 4 (fun ε ↦ H ε * U ε * w₂ ε)
      betaSecondP := hHUw₂.trans hbetaSecondPolynomial
  let betaP : ℝ → ℝ := fun ε ↦ 1 + (52 / 5) * ε ^ 3
  have hbetaRaw : EqModPow 4
      (fun ε ↦ ε ^ 3 * L ε * Q ε * w₁ ε + H ε * U ε * w₂ ε)
      (fun ε ↦ -4 * ε ^ 3 + betaSecondP ε) :=
    hbetaFirst.add hbetaSecond
  have hbeta : EqModPow 4 beta betaP := by
    apply hbetaRaw.congr
    · intro ε
      dsimp only [beta]
    · intro ε
      dsimp only [betaSecondP, betaP]
      ring
  have hQSquare : EqModPow 4 (fun ε ↦ Q ε ^ 2)
      (fun ε ↦ Q4 ε ^ 2) := by
    have hsquare := hQFour.mul hQFour hQ4Continuous hQContinuous
    simpa only [pow_two] using hsquare
  have hUSquare : EqModPow 4 (fun ε ↦ U ε ^ 2)
      (fun ε ↦ UP ε ^ 2) := by
    have hsquare := hU.mul hU hUPContinuous hUContinuous
    simpa only [pow_two] using hsquare
  have hQSquareContinuous : ContinuousAt (fun ε ↦ Q ε ^ 2) 0 := by
    fun_prop
  have hUSquareContinuous : ContinuousAt (fun ε ↦ U ε ^ 2) 0 := by
    fun_prop
  have hLQSquare : EqModPow 4 (fun ε ↦ L ε * Q ε ^ 2)
      (fun ε ↦ LP ε * Q4 ε ^ 2) :=
    hL.mul hQSquare hLPContinuous hQSquareContinuous
  have hHUSquare : EqModPow 4 (fun ε ↦ H ε * U ε ^ 2)
      (fun ε ↦ H4 ε * UP ε ^ 2) :=
    hHCubic.mul hUSquare hH4Continuous hUSquareContinuous
  have hdeltaRaw : EqModPow 4
      (fun ε ↦ L ε * Q ε ^ 2 + H ε * U ε ^ 2)
      (fun ε ↦ LP ε * Q4 ε ^ 2 + H4 ε * UP ε ^ 2) :=
    hLQSquare.add hHUSquare
  let deltaP : ℝ → ℝ := fun ε ↦ 3 + 72 * ε ^ 3
  have hdeltaPolynomial : EqModPow 4
      (fun ε ↦ LP ε * Q4 ε ^ 2 + H4 ε * UP ε ^ 2) deltaP := by
    apply EqModPow.of_factor
      (q := fun ε ↦ -(312 / 25) * ε ^ 2 * (ε ^ 3 + 12))
    · fun_prop
    · intro ε
      dsimp only [LP, Q4, H4, UP, deltaP]
      ring
  have hdelta : EqModPow 4 delta deltaP := by
    have hraw := hdeltaRaw.trans hdeltaPolynomial
    apply hraw.congr
    · intro ε
      dsimp only [delta]
    · intro _
      rfl
  have hdeltaPContinuous : ContinuousAt deltaP 0 := by
    dsimp only [deltaP]
    fun_prop
  have hbetaPContinuous : ContinuousAt betaP 0 := by
    dsimp only [betaP]
    fun_prop
  have hw₁PContinuous : ContinuousAt w₁P 0 := by
    dsimp only [w₁P]
    fun_prop
  have hw₂PContinuous : ContinuousAt w₂P 0 := by
    dsimp only [w₂P]
    fun_prop
  have hdeltaContinuous : ContinuousAt delta 0 := by
    dsimp only [delta]
    fun_prop
  have hbetaContinuous : ContinuousAt beta 0 := by
    dsimp only [beta]
    fun_prop
  have hzeroFour : 0 < 4 := by
    norm_num
  have hbetaZero : beta 0 = 1 := by
    have hzero := eqModPow_apply_zero hzeroFour hbeta
    norm_num [betaP] at hzero ⊢
    exact hzero
  let threeBeta : ℝ → ℝ := fun ε ↦ 3 * beta ε
  let threeBetaP : ℝ → ℝ := fun ε ↦ 3 * betaP ε
  have hthreeBeta : EqModPow 4 threeBeta threeBetaP := by
    have hscaled := eqModPow_const_mul_left 3 hbeta
    simpa only [threeBeta, threeBetaP] using hscaled
  have hthreeBetaContinuous : ContinuousAt threeBeta 0 := by
    dsimp only [threeBeta]
    fun_prop
  have hthreeBetaZeroNe : threeBeta 0 ≠ 0 := by
    norm_num [threeBeta, hbetaZero]
  have hdeltaW₁ : EqModPow 4 (fun ε ↦ delta ε * w₁ ε)
      (fun ε ↦ deltaP ε * w₁P ε) :=
    hdelta.mul hw₁ hdeltaPContinuous hw₁Continuous
  let ratio₁P : ℝ → ℝ := fun ε ↦
    -2 + 2 * ε - (228 / 5) * ε ^ 3
  have hratio₁Polynomial : EqModPow 4
      (fun ε ↦ deltaP ε * w₁P ε)
      (fun ε ↦ threeBetaP ε * ratio₁P ε) := by
    apply EqModPow.of_factor
      (q := fun ε ↦ (408 / 25) * (6 * ε ^ 2 + 5))
    · fun_prop
    · intro ε
      dsimp only [deltaP, w₁P, threeBetaP, betaP, ratio₁P]
      ring
  have hratio₁PContinuous : ContinuousAt ratio₁P 0 := by
    dsimp only [ratio₁P]
    fun_prop
  have hthreeBetaPContinuous : ContinuousAt threeBetaP 0 := by
    dsimp only [threeBetaP]
    fun_prop
  have hthreeBetaTimesRatio₁P : EqModPow 4
      (fun ε ↦ threeBeta ε * ratio₁P ε)
      (fun ε ↦ threeBetaP ε * ratio₁P ε) := by
    have hrefl := EqModPow.refl 4 ratio₁P
    exact hthreeBeta.mul hrefl hthreeBetaPContinuous hratio₁PContinuous
  have hratio₁Product : EqModPow 4 (fun ε ↦ delta ε * w₁ ε)
      (fun ε ↦ threeBeta ε * ratio₁P ε) :=
    (hdeltaW₁.trans hratio₁Polynomial).trans hthreeBetaTimesRatio₁P.symm
  let ratio₁ : ℝ → ℝ := fun ε ↦ delta ε * w₁ ε / threeBeta ε
  have hratio₁ : EqModPow 4 ratio₁ ratio₁P := by
    have hquotient := EqModPow.div_of_eq_mul hratio₁Product
      hthreeBetaContinuous hthreeBetaZeroNe
    simpa only [ratio₁] using hquotient
  have hq₂CorrectionLift : EqModPow 7
      (fun ε ↦ ε ^ 3 * ratio₁ ε)
      (fun ε ↦ ε ^ 3 * ratio₁P ε) := by
    have hlift := eqModPow_mul_pow_left (n := 4) (k := 3) hratio₁
    simpa only [Nat.reduceAdd] using hlift
  have hq₂Raw : EqModPow 7
      (fun ε ↦ Q ε - ε ^ 3 * ratio₁ ε)
      (fun ε ↦ QP ε - ε ^ 3 * ratio₁P ε) :=
    hQ.sub hq₂CorrectionLift
  have hq₂ : EqModPow 7 q₂ model := by
    apply hq₂Raw.congr
    · intro ε
      dsimp only [q₂, ratio₁, threeBeta]
      simp only [mul_div_assoc, mul_assoc]
    · intro ε
      dsimp only [QP, ratio₁P, model]
      ring
  have hthreeFourLe : 3 ≤ 4 := by
    norm_num
  let three : ℝ → ℝ := fun _ ↦ 3
  have hdeltaThreeRaw : EqModPow 3 delta deltaP :=
    eqModPow_mono hdelta hthreeFourLe
  have hdeltaPThree : EqModPow 3 deltaP three := by
    apply EqModPow.of_factor (q := fun _ ↦ 72)
    · fun_prop
    · intro ε
      dsimp only [deltaP, three]
      ring
  have hdeltaThree : EqModPow 3 delta three :=
    hdeltaThreeRaw.trans hdeltaPThree
  have hw₂ThreeRaw : EqModPow 3 w₂ w₂P :=
    eqModPow_mono hw₂ hthreeFourLe
  have hw₂PThree : EqModPow 3 w₂P one := by
    apply EqModPow.of_factor (q := fun _ ↦ (26 / 5 : ℝ))
    · fun_prop
    · intro ε
      dsimp only [w₂P, one]
      ring
  have hw₂Three : EqModPow 3 w₂ one := hw₂ThreeRaw.trans hw₂PThree
  have hbetaThreeRaw : EqModPow 3 beta betaP :=
    eqModPow_mono hbeta hthreeFourLe
  have hbetaPThree : EqModPow 3 betaP one := by
    apply EqModPow.of_factor (q := fun _ ↦ (52 / 5 : ℝ))
    · fun_prop
    · intro ε
      dsimp only [betaP, one]
      ring
  have hbetaThree : EqModPow 3 beta one := hbetaThreeRaw.trans hbetaPThree
  have hUThreeRaw : EqModPow 3 U UP := eqModPow_mono hU hthreeFourLe
  have hUPThree : EqModPow 3 UP one := by
    apply EqModPow.of_factor (q := fun _ ↦ (56 / 5 : ℝ))
    · fun_prop
    · intro ε
      dsimp only [UP, one]
      ring
  have hUThree : EqModPow 3 U one := hUThreeRaw.trans hUPThree
  have hthreeContinuous : ContinuousAt three 0 := by
    dsimp only [three]
    fun_prop
  have hdeltaW₂ThreeRaw : EqModPow 3 (fun ε ↦ delta ε * w₂ ε)
      (fun ε ↦ three ε * one ε) :=
    hdeltaThree.mul hw₂Three hthreeContinuous hw₂Continuous
  have hdeltaW₂Three : EqModPow 3 (fun ε ↦ delta ε * w₂ ε) three := by
    apply hdeltaW₂ThreeRaw.congr
    · intro _
      rfl
    · intro ε
      dsimp only [three, one]
      ring
  have hthreeBetaThreeRaw : EqModPow 3 beta one := hbetaThree
  have hthreeBetaThree : EqModPow 3 threeBeta three := by
    have hscaled := eqModPow_const_mul_left 3 hthreeBetaThreeRaw
    apply hscaled.congr
    · intro ε
      dsimp only [threeBeta]
    · intro ε
      dsimp only [one, three]
      ring
  have hthreeBetaTimesOne : EqModPow 3
      (fun ε ↦ threeBeta ε * one ε) three := by
    apply hthreeBetaThree.congr
    · intro ε
      simp only [one, mul_one]
    · intro _
      rfl
  have hratio₂Product : EqModPow 3 (fun ε ↦ delta ε * w₂ ε)
      (fun ε ↦ threeBeta ε * one ε) :=
    hdeltaW₂Three.trans hthreeBetaTimesOne.symm
  let ratio₂ : ℝ → ℝ := fun ε ↦ delta ε * w₂ ε / threeBeta ε
  have hratio₂ : EqModPow 3 ratio₂ one := by
    have hquotient := EqModPow.div_of_eq_mul hratio₂Product
      hthreeBetaContinuous hthreeBetaZeroNe
    simpa only [ratio₂] using hquotient
  have hv₂Raw : EqModPow 3 (fun ε ↦ U ε - ratio₂ ε)
      (fun ε ↦ one ε - one ε) := hUThree.sub hratio₂
  have hv₂ : EqModPow 3 v₂ (fun _ ↦ 0) := by
    apply hv₂Raw.congr
    · intro ε
      dsimp only [v₂, ratio₂, threeBeta]
    · intro ε
      dsimp only [one]
      ring
  have hv₂Order : v₂ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have horder := EqModPow.to_isBigO hv₂
    simpa only [sub_zero] using horder
  have hweightedV₂Order : (fun ε ↦ ε ^ 2 * v₂ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hproduct :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0)).mul hv₂Order
    simpa only [← pow_add, Nat.reduceAdd] using hproduct
  have hweightedV₂Square : (fun ε ↦ (ε ^ 2 * v₂ ε) ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 10) := by
    simpa only [← pow_mul, Nat.reduceMul] using hweightedV₂Order.pow 2
  have hsevenTen : 7 < 10 := by
    norm_num
  have htenSeven : (fun ε : ℝ ↦ ε ^ 10) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isLittleO_pow_pow hsevenTen).isBigO
  have hratio₁Continuous : ContinuousAt ratio₁ 0 := by
    dsimp only [ratio₁]
    fun_prop
  have hratio₂Continuous : ContinuousAt ratio₂ 0 := by
    dsimp only [ratio₂]
    fun_prop
  have hq₂Continuous : ContinuousAt q₂ 0 := by
    dsimp only [q₂]
    fun_prop
  have hv₂Continuous : ContinuousAt v₂ 0 := by
    dsimp only [v₂]
    fun_prop
  have hmodelContinuous : ContinuousAt model 0 := by
    dsimp only [model]
    fun_prop
  have hq₂Square : EqModPow 7 (fun ε ↦ q₂ ε ^ 2)
      (fun ε ↦ model ε ^ 2) := by
    have hsquare := hq₂.mul hq₂ hmodelContinuous hq₂Continuous
    simpa only [pow_two] using hsquare
  have hradicandSquare : EqModPow 7 radicand
      (fun ε ↦ model ε ^ 2) := by
    have hsum := (EqModPow.to_isBigO hq₂Square).add
      (hweightedV₂Square.trans htenSeven)
    have hidentity (ε : ℝ) :
        (q₂ ε ^ 2 - model ε ^ 2) + (ε ^ 2 * v₂ ε) ^ 2 =
          radicand ε - model ε ^ 2 := by
      dsimp only [radicand]
      abel
    exact EqModPow.of_isBigO (hsum.congr_left hidentity)
  have hq₂Zero : q₂ 0 = 1 := by
    have hzero := eqModPow_apply_zero hzeroSeven hq₂
    norm_num [model] at hzero ⊢
    exact hzero
  have hv₂Zero : v₂ 0 = 0 := by
    have hzeroThree : 0 < 3 := by
      norm_num
    have hzero := eqModPow_apply_zero hzeroThree hv₂
    simpa only using hzero
  have hradicandContinuous : ContinuousAt radicand 0 := by
    dsimp only [radicand]
    fun_prop
  have hradicandPos : 0 < radicand 0 := by
    norm_num [radicand, hq₂Zero, hv₂Zero]
  have hmodelPos : 0 < model 0 := by
    norm_num [model]
  have hsqrt : EqModPow 7 (fun ε ↦ Real.sqrt (radicand ε)) model :=
    EqModPow.sqrt_of_sq hradicandSquare hradicandContinuous
      hmodelContinuous hradicandPos hmodelPos
  have hAZero : A 0 = 0 := by
    norm_num [A, haZero]
  have hfirstLowChart : ∀ᶠ ε in 𝓝 (0 : ℝ), A ε < d ε := by
    apply hAContinuous.eventually_lt hdContinuous
    rw [hAZero, hdZero]
    norm_num
  have hremainder := EqModPow.to_isBigO hsqrt
  have hleft : ∀ᶠ ε in 𝓝 (0 : ℝ),
      Real.sqrt (radicand ε) - model ε =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
          (1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6) := by
    filter_upwards [hfirstLowChart] with ε hchart
    have hmetricChart :
        let M := DFP.FirstLeg.outputMetric ε (p ε) (h ε)
        M 0 0 < M 1 1 := by
      simpa [DFP.FirstLeg.outputMetric, A, d, a, b, B, C] using hchart
    rw [finalGradientNorm_eq_sqrt_of_lowChart ε (p ε) (h ε) hmetricChart]
    dsimp only [model]
    congr 2
  exact hremainder.congr' hleft (Eventually.of_forall fun _ ↦ rfl)

/-- Along a path whose shape and high-eigenvalue coordinates agree with the
polynomial slow graph through order four, the first normalized step norm equals
`2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6` up to `O(ε ^ 7)`. -/
theorem slowCurveFirstStepRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm -
        (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  let factorMap : ℝ × ℝ × ℝ → Fin 2 → ℝ := fun z ↦
    let B := 1 + 2 * z.1 ^ 3 + z.1 ^ 4
    let c := 2 * (z.2.1 + 1) / (3 * B)
    ![-c * z.1 ^ 2, -c]
  let factorNorm : ℝ × ℝ × ℝ → ℝ := fun z ↦
    ‖WithLp.toLp 2 (factorMap z)‖
  let model : ℝ → ℝ := fun ε ↦
    2 + (112 / 5) * ε ^ 3 - (11 / 5) * ε ^ 4
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFive).add hh₀Tendsto
  have hxTendsto : Tendsto x (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Tendsto : Tendsto x₀ (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x₀, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hp₀Tendsto.prodMk hh₀Tendsto)
  have hpathDiff : (fun ε ↦ x ε - x₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
    simpa [x, x₀] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have hfactorMap : ContDiffAt ℝ 1 factorMap (0, 2, 1) := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i
    · dsimp only [factorMap]
      fun_prop (disch := norm_num)
    · dsimp only [factorMap]
      fun_prop (disch := norm_num)
  have hfactorBaseNe : WithLp.toLp 2 (factorMap (0, 2, 1)) ≠
      (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro hzero
    have hcoord := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hzero
    norm_num [factorMap] at hcoord
  have hfactorLp : ContDiffAt ℝ 1
      (fun z ↦ WithLp.toLp 2 (factorMap z)) (0, 2, 1) := by
    fun_prop
  have hfactorNorm : ContDiffAt ℝ 1 factorNorm (0, 2, 1) := by
    dsimp only [factorNorm]
    exact hfactorLp.norm ℝ hfactorBaseNe
  have hfactorNormStrict := hfactorNorm.hasStrictFDerivAt one_ne_zero
  have hfactorDiff : (fun ε ↦ factorNorm (x ε) - factorNorm (x₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have houter := hfactorNormStrict.isBigO_sub
    have hpairs : Tendsto (fun ε ↦ (x ε, x₀ ε)) (𝓝 0)
        (𝓝 (((0, 2, 1), (0, 2, 1)) :
          (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
      simpa only [nhds_prod_eq] using hxTendsto.prodMk hx₀Tendsto
    have hcomposed := houter.comp_tendsto hpairs
    have hcomposed' :
        (fun ε ↦ factorNorm (x ε) - factorNorm (x₀ ε)) =O[𝓝 0]
          (fun ε ↦ x ε - x₀ ε) := by
      simpa only [Function.comp_def] using hcomposed
    exact hcomposed'.trans hpathDiff
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  let coefficient : ℝ → ℝ := fun ε ↦
    2 * (p₀ ε + 1) / (3 * B ε)
  let coefficientP : ℝ → ℝ := fun ε ↦
    2 + (112 / 5) * ε ^ 3 - (16 / 5) * ε ^ 4
  let radicand : ℝ → ℝ := fun ε ↦
    coefficient ε ^ 2 * (ε ^ 4 + 1)
  have hdenContinuous : ContinuousAt (fun ε ↦ 3 * B ε) 0 := by
    dsimp only [B]
    fun_prop
  have hdenZero : 3 * B 0 ≠ 0 := by
    norm_num [B]
  have hcoefficientProduct : EqModPow 5
      (fun ε ↦ 2 * (p₀ ε + 1))
      (fun ε ↦ (3 * B ε) * coefficientP ε) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        -(672 / 5) * ε - 48 * ε ^ 2 + (48 / 5) * ε ^ 3)
    · fun_prop
    · intro ε
      dsimp only [p₀, B, coefficientP]
      ring
  have hcoefficient : EqModPow 5 coefficient coefficientP := by
    have hquotient := EqModPow.div_of_eq_mul hcoefficientProduct
      hdenContinuous hdenZero
    simpa only [coefficient] using hquotient
  have hcoefficientContinuous : ContinuousAt coefficient 0 := by
    dsimp only [coefficient, p₀, B]
    fun_prop (disch := norm_num)
  have hcoefficientPContinuous : ContinuousAt coefficientP 0 := by
    dsimp only [coefficientP]
    fun_prop
  have hcoefficientSquare : EqModPow 5
      (fun ε ↦ coefficient ε ^ 2)
      (fun ε ↦ coefficientP ε ^ 2) := by
    have hsquare := hcoefficient.mul hcoefficient
      hcoefficientPContinuous hcoefficientContinuous
    simpa only [pow_two] using hsquare
  have hweight : EqModPow 5 (fun ε : ℝ ↦ ε ^ 4 + 1)
      (fun ε : ℝ ↦ ε ^ 4 + 1) := EqModPow.refl 5 _
  have hweightContinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 4 + 1) 0 := by
    fun_prop
  have hcoefficientPSquareContinuous :
      ContinuousAt (fun ε ↦ coefficientP ε ^ 2) 0 := by
    fun_prop
  have hradicandRaw : EqModPow 5 radicand
      (fun ε ↦ coefficientP ε ^ 2 * (ε ^ 4 + 1)) := by
    have hproduct := hcoefficientSquare.mul hweight
      hcoefficientPSquareContinuous hweightContinuous
    simpa only [radicand] using hproduct
  have hradicandPolynomial : EqModPow 5
      (fun ε ↦ coefficientP ε ^ 2 * (ε ^ 4 + 1))
      (fun ε ↦ model ε ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦
        (256 / 25) * ε ^ 7 - (3584 / 25) * ε ^ 6 +
          (12544 / 25) * ε ^ 5 - (37 / 5) * ε ^ 3 +
          (224 / 5) * ε ^ 2)
    · fun_prop
    · intro ε
      dsimp only [coefficientP, model]
      ring
  have hradicand : EqModPow 5 radicand (fun ε ↦ model ε ^ 2) :=
    hradicandRaw.trans hradicandPolynomial
  have hradicandContinuous : ContinuousAt radicand 0 := by
    dsimp only [radicand]
    fun_prop
  have hmodelContinuous : ContinuousAt model 0 := by
    dsimp only [model]
    fun_prop
  have hradicandPos : 0 < radicand 0 := by
    norm_num [radicand, coefficient, p₀, B]
  have hmodelPos : 0 < model 0 := by
    norm_num [model]
  have hsqrt : EqModPow 5 (fun ε ↦ Real.sqrt (radicand ε)) model :=
    EqModPow.sqrt_of_sq hradicand hradicandContinuous
      hmodelContinuous hradicandPos hmodelPos
  have hslowNorm : EqModPow 5 (fun ε ↦ factorNorm (x₀ ε)) model := by
    apply hsqrt.congr
    · intro ε
      dsimp only [factorNorm, factorMap, x₀, radicand, coefficient, p₀, h₀, B]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      ring_nf
    · intro _
      rfl
  have hfactorModel : EqModPow 5 (fun ε ↦ factorNorm (x ε)) model := by
    have hsum := hfactorDiff.add (EqModPow.to_isBigO hslowNorm)
    have hidentity (ε : ℝ) :
        (factorNorm (x ε) - factorNorm (x₀ ε)) +
            (factorNorm (x₀ ε) - model ε) =
          factorNorm (x ε) - model ε := by
      ring
    exact EqModPow.of_isBigO (hsum.congr_left hidentity)
  have hscaled : EqModPow 7
      (fun ε ↦ ε ^ 2 * factorNorm (x ε))
      (fun ε ↦ ε ^ 2 * model ε) := by
    have hlift := eqModPow_mul_pow_left (n := 5) (k := 2) hfactorModel
    simpa only [Nat.reduceAdd] using hlift
  have hfirstStepScale (ε pValue hValue : ℝ)
      (hpValue : pValue ≠ 0) (hhValue : hValue ≠ 0)
      (hBValue : 1 + 2 * ε ^ 3 + ε ^ 4 ≠ 0) :
      (DFP.TwoLeg.observableMap (ε, pValue, hValue)).firstStepNorm =
        ε ^ 2 * ‖WithLp.toLp 2 (factorMap (ε, pValue, hValue))‖ := by
    let g : Fin 2 → ℝ := ![(1 : ℝ), pValue * ε ^ 2]
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![hValue * pValue * ε ^ 4, hValue]
    let Hg := H.mulVec g
    let A := (TwoPhaseControls.first ε).matrix
    let alpha := (TwoPhaseControls.first ε).tau * dotProduct g Hg /
      dotProduct Hg (A.mulVec Hg)
    let raw : Fin 2 → ℝ := -(alpha • Hg)
    have hnorms := congrArg Prod.fst
      (DFP.TwoLeg.observableMap_stepNorms ε pValue hValue)
    have hnorms' :
        (DFP.TwoLeg.observableMap (ε, pValue, hValue)).firstStepNorm =
          ‖WithLp.toLp 2 raw‖ := by
      simpa only [g, H, Hg, A, alpha, raw] using hnorms
    have hBAlt : 1 + ε ^ 3 * 2 + ε ^ 4 ≠ 0 := by
      simpa only [mul_comm] using hBValue
    have hraw : raw = ε ^ 2 • factorMap (ε, pValue, hValue) := by
      ext i
      fin_cases i <;>
        simp [raw, alpha, Hg, A, H, g, factorMap,
          TwoPhaseControls.first_tau, TwoPhaseControls.first_matrix,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      all_goals
        by_cases hε : ε = 0
        · simp [hε]
        · field_simp [hpValue, hhValue, hBValue, hBAlt, hε]
          have hunit : (1 + ε ^ 3 * 2 + ε ^ 4) *
              (1 + ε ^ 3 * 2 + ε ^ 4)⁻¹ = 1 :=
            mul_inv_cancel₀ hBAlt
          calc
            _ = (1 + pValue) * ((1 + ε ^ 3 * 2 + ε ^ 4)⁻¹ *
                (1 + ε ^ 3 * 2 + ε ^ 4)) := by ring
            _ = _ := by
              rw [inv_mul_cancel₀ hBAlt, mul_one]
              ring
    rw [hnorms', hraw]
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg ε)]
  have htwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  have honeNe : (1 : ℝ) ≠ 0 := by
    norm_num
  have hpNe : ∀ᶠ ε in 𝓝 (0 : ℝ), p ε ≠ 0 :=
    hpTendsto.eventually_ne htwoNe
  have hhNe : ∀ᶠ ε in 𝓝 (0 : ℝ), h ε ≠ 0 :=
    hhTendsto.eventually_ne honeNe
  have hBContinuous : ContinuousAt B 0 := by
    dsimp only [B]
    fun_prop
  have hBZero : B 0 ≠ 0 := by
    norm_num [B]
  have hBNe : ∀ᶠ ε in 𝓝 (0 : ℝ), B ε ≠ 0 :=
    hBContinuous.eventually_ne hBZero
  have hstepScale : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm =
        ε ^ 2 * factorNorm (x ε) := by
    filter_upwards [hpNe, hhNe, hBNe] with ε hpε hhε hBε
    have hstep := hfirstStepScale ε (p ε) (h ε) hpε hhε hBε
    simpa only [factorNorm, factorMap, x] using hstep
  have hremainder := EqModPow.to_isBigO hscaled
  have hleft : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ε ^ 2 * factorNorm (x ε) - ε ^ 2 * model ε =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm -
          (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6) := by
    filter_upwards [hstepScale] with ε hstep
    rw [hstep]
    dsimp only [model]
    ring
  exact hremainder.congr' hleft (Eventually.of_forall fun _ ↦ rfl)

/-- Along a path whose shape and high-eigenvalue coordinates agree with the
polynomial slow graph through order four, the second normalized step norm equals
`ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6` up to `O(ε ^ 7)`. -/
theorem slowCurveSecondStepRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm -
        (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  let factorMap : ℝ × ℝ × ℝ → Fin 2 → ℝ := fun z ↦
    secondStepDisplacementFactor z.1 z.2.1 z.2.2
  let factorNorm : ℝ × ℝ × ℝ → ℝ := fun z ↦
    ‖WithLp.toLp 2 (factorMap z)‖
  let model : ℝ → ℝ := fun ε ↦
    1 + (114 / 5) * ε ^ 3 - (49 / 10) * ε ^ 4
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFive).add hh₀Tendsto
  have hxTendsto : Tendsto x (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Tendsto : Tendsto x₀ (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x₀, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hp₀Tendsto.prodMk hh₀Tendsto)
  have hpathDiff : (fun ε ↦ x ε - x₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
    simpa [x, x₀] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have hfirstFactors : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.factors z.1 z.2.1 z.2.2) (0, 2, 1) :=
    DFP.FirstLeg.factorsAnalytic.contDiffAt
  have hspectral : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.spectralFactors z.1 z.2.1 z.2.2) (0, 2, 1) := by
    simpa only [DFP.FirstLeg.factors] using hfirstFactors.fst
  have hgradient : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.gradientFactors z.1 z.2.1 z.2.2) (0, 2, 1) := by
    simpa only [DFP.FirstLeg.factors] using hfirstFactors.snd.fst
  have hL := contDiffAt_fst.comp (0, 2, 1) hspectral
  have hH := contDiffAt_snd.comp (0, 2, 1) hspectral
  have hQ := contDiffAt_fst.comp (0, 2, 1) hgradient
  have hU := contDiffAt_snd.comp (0, 2, 1) hgradient
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hfactorMap : ContDiffAt ℝ 1 factorMap (0, 2, 1) := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i
    · dsimp only [factorMap, secondStepDisplacementFactor]
      fun_prop (disch := norm_num [hspectralBase, hgradientBase])
    · dsimp only [factorMap, secondStepDisplacementFactor]
      fun_prop (disch := norm_num [hspectralBase, hgradientBase])
  have hfactorBaseNe : WithLp.toLp 2 (factorMap (0, 2, 1)) ≠
      (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro hzero
    have hcoord := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hzero
    norm_num [factorMap, secondStepDisplacementFactor, hspectralBase,
      hgradientBase] at hcoord
  have hfactorLp : ContDiffAt ℝ 1
      (fun z ↦ WithLp.toLp 2 (factorMap z)) (0, 2, 1) := by
    fun_prop
  have hfactorNorm : ContDiffAt ℝ 1 factorNorm (0, 2, 1) := by
    dsimp only [factorNorm]
    exact hfactorLp.norm ℝ hfactorBaseNe
  have hfactorNormStrict := hfactorNorm.hasStrictFDerivAt one_ne_zero
  have hfactorDiff : (fun ε ↦ factorNorm (x ε) - factorNorm (x₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have houter := hfactorNormStrict.isBigO_sub
    have hpairs : Tendsto (fun ε ↦ (x ε, x₀ ε)) (𝓝 0)
        (𝓝 (((0, 2, 1), (0, 2, 1)) :
          (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
      simpa only [nhds_prod_eq] using hxTendsto.prodMk hx₀Tendsto
    have hcomposed := houter.comp_tendsto hpairs
    have hcomposed' :
        (fun ε ↦ factorNorm (x ε) - factorNorm (x₀ ε)) =O[𝓝 0]
          (fun ε ↦ x ε - x₀ ε) := by
      simpa only [Function.comp_def] using hcomposed
    exact hcomposed'.trans hpathDiff
  have hslowSqrt := slowGraphSecondStepFactorNormGerm
  have hslowNorm : EqModPow 5 (fun ε ↦ factorNorm (x₀ ε)) model := by
    apply hslowSqrt.congr
    · intro ε
      dsimp only [factorNorm, factorMap, x₀, p₀, h₀]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    · intro _
      rfl
  have hfactorModel : EqModPow 5 (fun ε ↦ factorNorm (x ε)) model := by
    have hsum := hfactorDiff.add (EqModPow.to_isBigO hslowNorm)
    have hidentity (ε : ℝ) :
        (factorNorm (x ε) - factorNorm (x₀ ε)) +
            (factorNorm (x₀ ε) - model ε) =
          factorNorm (x ε) - model ε := by
      ring
    exact EqModPow.of_isBigO (hsum.congr_left hidentity)
  have hscaled : EqModPow 7
      (fun ε ↦ ε ^ 2 * factorNorm (x ε))
      (fun ε ↦ ε ^ 2 * model ε) := by
    have hlift := eqModPow_mul_pow_left (n := 5) (k := 2) hfactorModel
    simpa only [Nat.reduceAdd] using hlift
  have hmetric00 : ContinuousAt
      (fun z : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.outputMetric z.1 z.2.1 z.2.2 0 0) (0, 2, 1) := by
    simp only [DFP.FirstLeg.outputMetric]
    fun_prop (disch := norm_num)
  have hmetric11 : ContinuousAt
      (fun z : ℝ × ℝ × ℝ ↦
        DFP.FirstLeg.outputMetric z.1 z.2.1 z.2.2 1 1) (0, 2, 1) := by
    simp only [DFP.FirstLeg.outputMetric]
    fun_prop (disch := norm_num)
  have hbaseChart : DFP.FirstLeg.outputMetric 0 2 1 0 0 <
      DFP.FirstLeg.outputMetric 0 2 1 1 1 := by
    norm_num [DFP.FirstLeg.outputMetric]
  have hchartState : ∀ᶠ z in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DFP.FirstLeg.outputMetric z.1 z.2.1 z.2.2 0 0 <
        DFP.FirstLeg.outputMetric z.1 z.2.1 z.2.2 1 1 :=
    hmetric00.eventually_lt hmetric11 hbaseChart
  have hchartPath : ∀ᶠ ε in 𝓝 (0 : ℝ),
      DFP.FirstLeg.outputMetric ε (p ε) (h ε) 0 0 <
        DFP.FirstLeg.outputMetric ε (p ε) (h ε) 1 1 := by
    have hpullback := hxTendsto.eventually hchartState
    simpa only [x] using hpullback
  have hfactorNormSqrt (ε : ℝ) : factorNorm (x ε) =
      Real.sqrt
        ((secondStepDisplacementFactor ε (p ε) (h ε) 0) ^ 2 +
          (secondStepDisplacementFactor ε (p ε) (h ε) 1) ^ 2) := by
    dsimp only [factorNorm, factorMap, x]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hremainder := EqModPow.to_isBigO hscaled
  have hleft : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ε ^ 2 * factorNorm (x ε) - ε ^ 2 * model ε =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm -
          (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6) := by
    filter_upwards [hchartPath] with ε hchart
    have hmetricChart :
        let M := DFP.FirstLeg.outputMetric ε (p ε) (h ε)
        M 0 0 < M 1 1 := hchart
    rw [secondStepNorm_eq_scale_sqrt_of_lowChart ε (p ε) (h ε) hmetricChart]
    rw [hfactorNormSqrt]
    dsimp only [model]
    ring
  exact hremainder.congr' hleft (Eventually.of_forall fun _ ↦ rfl)

/-- Along the polynomial slow-graph path, the first normalized step norm has the displayed
order-six finite Taylor jet. -/
theorem slowFirstStep :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).firstStepNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6) 0 := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hp : (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [p] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [h] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hrem := slowCurveFirstStepRemainder p h hp hh
  have hrem' : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).firstStepNorm -
        (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    simpa [p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hrem
  have hpath : ContDiffAt ℝ 6 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    simpa only [show DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) by
          funext ε; exact DFP.TwoLeg.slowGraphJetPath_apply ε] using hp'
  have houter := DFP.TwoLeg.CenterCancellation.firstStepNorm_contDiffAt 6
  have hbase : DFP.TwoLeg.slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  rw [← hbase] at houter
  have hactual : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)).firstStepNorm) 0 := by
    simpa only [Function.comp_def] using houter.comp 0 hpath
  have hmodel : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ 2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hmodel
  simpa only [zero_add] using hrem'

/-- Along the polynomial slow-graph path, the second normalized step norm has the displayed
order-six finite Taylor jet. -/
theorem slowSecondStep :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).secondStepNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦ ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6) 0 := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hp : (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [p] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [h] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hrem := slowCurveSecondStepRemainder p h hp hh
  have hrem' : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).secondStepNorm -
        (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    simpa [p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hrem
  have hpath : ContDiffAt ℝ 6 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    simpa only [show DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) by
          funext ε; exact DFP.TwoLeg.slowGraphJetPath_apply ε] using hp'
  have houter := DFP.TwoLeg.CenterCancellation.secondStepNorm_contDiffAt 6
  have hbase : DFP.TwoLeg.slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  rw [← hbase] at houter
  have hactual : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)).secondStepNorm) 0 := by
    simpa only [Function.comp_def] using houter.comp 0 hpath
  have hmodel : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hmodel
  simpa only [zero_add] using hrem'

/-- Along the polynomial slow-graph path, the initial normalized gradient norm has the
displayed order-five finite Taylor jet. -/
theorem slowInitialGradient :
    FiniteTaylorJet.ofFunction ℝ 5
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).initialGradientNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 5 (fun ε : ℝ ↦ 1 + 2 * ε ^ 4) 0 := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  have hp : (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [p] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hrem := slowInitialGradientRemainder p h hp
  have hrem' : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).initialGradientNorm -
        (1 + 2 * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) := by
    simpa [p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hrem
  have hpath : ContDiffAt ℝ 5 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 5
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    simpa only [show DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) by
          funext ε; exact DFP.TwoLeg.slowGraphJetPath_apply ε] using hp'
  have houter := DFP.TwoLeg.initialGradientNorm_contDiffAt 5
  have hbase : DFP.TwoLeg.slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  rw [← hbase] at houter
  have hactual : ContDiffAt ℝ 5
      (fun ε : ℝ ↦ (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)).initialGradientNorm) 0 := by
    simpa only [Function.comp_def] using houter.comp 0 hpath
  have hmodel : ContDiffAt ℝ 5 (fun ε : ℝ ↦ 1 + 2 * ε ^ 4) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hmodel
  simpa only [zero_add] using hrem'

/-- Along the polynomial slow-graph path, the intermediate normalized gradient norm has the
displayed order-six finite Taylor jet. -/
theorem slowIntermediateGradient :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).intermediateGradientNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦ 1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6) 0 := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  have hp : (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [p] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hrem := slowIntermediateGradientRemainder p h hp
  have hrem' : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).intermediateGradientNorm -
        (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    simpa [p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hrem
  have hpath : ContDiffAt ℝ 6 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    simpa only [show DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) by
          funext ε; exact DFP.TwoLeg.slowGraphJetPath_apply ε] using hp'
  have houter := DFP.TwoLeg.intermediateGradientNorm_contDiffAt 6
  have hbase : DFP.TwoLeg.slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  rw [← hbase] at houter
  have hactual : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)).intermediateGradientNorm) 0 := by
    simpa only [Function.comp_def] using houter.comp 0 hpath
  have hmodel : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ 1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hmodel
  simpa only [zero_add] using hrem'

/-- Along the polynomial slow-graph path, the final normalized gradient norm has the displayed
order-six finite Taylor jet. -/
theorem slowFinalGradient :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).finalGradientNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦ 1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6) 0 := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hp : (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [p] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa [h] using Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hrem := slowFinalGradientRemainder p h hp hh
  have hrem' : (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)).finalGradientNorm -
        (1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    simpa [p, h, DFP.TwoLeg.slowGraphJetPath_apply] using hrem
  have hpath : ContDiffAt ℝ 6 DFP.TwoLeg.slowGraphJetPath 0 := by
    have hp' : ContDiffAt ℝ 6
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    simpa only [show DFP.TwoLeg.slowGraphJetPath =
        (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) by
          funext ε; exact DFP.TwoLeg.slowGraphJetPath_apply ε] using hp'
  have houter := DFP.TwoLeg.finalGradientNorm_contDiffAt 6
  have hbase : DFP.TwoLeg.slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [DFP.TwoLeg.slowGraphJetPath_apply]
    norm_num
  rw [← hbase] at houter
  have hactual : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)).finalGradientNorm) 0 := by
    simpa only [Function.comp_def] using houter.comp 0 hpath
  have hmodel : ContDiffAt ℝ 6
      (fun ε : ℝ ↦ 1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hmodel
  simpa only [zero_add] using hrem'

end DFP.TwoLeg.NormJet
