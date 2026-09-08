module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.SecondLeg

/-- The second DFP metric in the first output's oriented eigenframe, with every
common power of `ε` canceled from the entrywise update formulas. -/
def outputMetric (ε p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
  let a := L - ε ^ 6 * L ^ 2 * w₁ ^ 2 / gamma + L ^ 2 * Q ^ 2 / beta
  let b := -(ε ^ 3 * L * H * w₁ * w₂ / gamma) + L * Q * H * U / beta
  let d := H - H ^ 2 * w₂ ^ 2 / gamma + H ^ 2 * U ^ 2 / beta
  !![ε ^ 4 * a, ε ^ 2 * b; ε ^ 2 * b, d]

/-- The normalized second updated gradient in the first output's oriented frame,
with its removable factor `ε ^ 2` retained in the second coordinate. -/
def outputGradient (ε p h : ℝ) : Fin 2 → ℝ :=
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
  let q := Q - ε ^ 3 * delta * w₁ / (3 * beta)
  let v := U - delta * w₂ / (3 * beta)
  ![q, ε ^ 2 * v]

/-- The fixed analytic eigenframe of the second updated metric. -/
def frame (ε p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let H := outputMetric ε p h
  EuclideanPlane.frame (RealSymmetric2.lowVector (H 0 0) (H 0 1) (H 1 1))

/-- The low and high eigenvalues of the second updated metric in the fixed branch. -/
def eigenvalues (ε p h : ℝ) : ℝ × ℝ :=
  let H := outputMetric ε p h
  (RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1),
    RealSymmetric2.high (H 0 0) (H 0 1) (H 1 1))

/-- The fixed-frame coordinates of the normalized second updated gradient. -/
def coordinates (ε p h : ℝ) : ℝ × ℝ :=
  let g := (frame ε p h).transpose *ᵥ outputGradient ε p h
  (g 0, g 1)

/-- The removable low-eigenvalue factor `L₂` and high eigenvalue `ℋ₂`. -/
def spectralFactors (ε p h : ℝ) : ℝ × ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
  let a := L - ε ^ 6 * L ^ 2 * w₁ ^ 2 / gamma + L ^ 2 * Q ^ 2 / beta
  let b := -(ε ^ 3 * L * H * w₁ * w₂ / gamma) + L * Q * H * U / beta
  let d := H - H ^ 2 * w₂ ^ 2 / gamma + H ^ 2 * U ^ 2 / beta
  let high := RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d
  ((a * d - b ^ 2) / high, high)

/-- The removable oriented-gradient factors `𝒢₂` and `U₂`, with the factor
`ε ^ 2` canceled from the high-frame coordinate. -/
def gradientFactors (ε p h : ℝ) : ℝ × ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
  let delta := L * Q ^ 2 + H * U ^ 2
  let a := L - ε ^ 6 * L ^ 2 * w₁ ^ 2 / gamma + L ^ 2 * Q ^ 2 / beta
  let b := -(ε ^ 3 * L * H * w₁ * w₂ / gamma) + L * Q * H * U / beta
  let d := H - H ^ 2 * w₂ ^ 2 / gamma + H ^ 2 * U ^ 2 / beta
  let q := Q - ε ^ 3 * delta * w₁ / (3 * beta)
  let v := U - delta * w₂ / (3 * beta)
  let low := RealSymmetric2.low (ε ^ 4 * a) (ε ^ 2 * b) d
  let denom := RealSymmetric2.lowDenom (ε ^ 4 * a) (ε ^ 2 * b) d
  (((d - low) * q - ε ^ 4 * b * v) / denom,
    (b * q + (d - low) * v) / denom)

/-- The canonical radius factor `ℛ₂` and recovered shape `p₂` formed from the
second-leg removable spectral and gradient factors. -/
def canonicalFactors (ε p h : ℝ) : ℝ × ℝ :=
  let spectral := spectralFactors ε p h
  let gradient := gradientFactors ε p h
  (spectral.1 * gradient.1 / (spectral.2 * gradient.2),
    spectral.2 * gradient.2 ^ 2 / (spectral.1 * gradient.1 ^ 2))

/-- The radius and shape recovered from the actual second-leg spectral and
oriented-gradient coordinates. -/
def recovered (ε p h : ℝ) : ℝ × ℝ :=
  let eigen := eigenvalues ε p h
  let gradient := coordinates ε p h
  (CycleBoundaryState.recoveryRadius eigen.1 eigen.2 gradient.1 gradient.2,
    CycleBoundaryState.recoveryShape eigen.1 eigen.2 gradient.1 gradient.2)

/-- The three pairs of removable second-leg factors: spectral, gradient, and canonical. -/
def factors (ε p h : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  (spectralFactors ε p h, gradientFactors ε p h, canonicalFactors ε p h)

/-- The second-control preconditioned-gradient energy has the displayed removable factor. -/
private lemma preconditionedEnergySecondControl
    (z : DFP.AbstractSecantStep (Fin 2)) (ε L H Q U G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![ε ^ 4 * L, H])
    (hg : z.gradient = G • ![Q, ε ^ 2 * U])
    (hA : z.secantMatrix = (TwoPhaseControls.second ε).matrix) :
    z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient) =
      G ^ 2 * ε ^ 4 *
        (ε ^ 3 * L * Q * (ε * L * Q - 2 * H * U) +
          H * U * (H * U - 2 * ε ^ 3 * L * Q)) := by
  -- Evaluate both coordinate actions in the incoming diagonal frame.
  rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.second_matrix]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- Polynomial normalization exposes the common fourth power.
  ring

/-- The inverse-Hessian energy of the second-control secant image has the displayed
removable factor. -/
private lemma secantImageEnergySecondControl
    (z : DFP.AbstractSecantStep (Fin 2)) (ε L H Q U G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![ε ^ 4 * L, H])
    (hg : z.gradient = G • ![Q, ε ^ 2 * U])
    (hA : z.secantMatrix = (TwoPhaseControls.second ε).matrix) :
    (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
        (z.inverseHessian *ᵥ
          (z.secantMatrix *ᵥ z.preconditionedGradient)) =
      G ^ 2 * ε ^ 4 *
        (ε ^ 6 * L * (ε * L * Q - 2 * H * U) ^ 2 +
          H * (H * U - 2 * ε ^ 3 * L * Q) ^ 2) := by
  -- Expand the secant image and final diagonal action coordinatewise.
  rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.second_matrix]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- Polynomial normalization exposes the same common fourth power.
  ring

/-- The canceled outputs agree with the abstract DFP step from the first-leg factored
state under the second control with the same `ε` and incoming amplitude `G`. -/
theorem outputEqStep (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal
      ![ε ^ 4 * (DFP.FirstLeg.spectralFactors ε p h).1,
        (DFP.FirstLeg.spectralFactors ε p h).2])
    (hg : z.gradient = G • ![(DFP.FirstLeg.gradientFactors ε p h).1,
      ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2])
    (hA : z.secantMatrix = (TwoPhaseControls.second ε).matrix)
    (hτ : z.tau = (TwoPhaseControls.second ε).tau) :
    (z.nextInverseHessian, z.nextGradient) =
      (outputMetric ε p h, G • outputGradient ε p h) := by
  let L := (DFP.FirstLeg.spectralFactors ε p h).1
  let H := (DFP.FirstLeg.spectralFactors ε p h).2
  let Q := (DFP.FirstLeg.gradientFactors ε p h).1
  let U := (DFP.FirstLeg.gradientFactors ε p h).2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
  -- Put the scaled input and second control into the explicit eigenframe spelling.
  have hg' : z.gradient = ![G * Q, G * (ε ^ 2 * U)] := by
    rw [hg]
    ext i
    fin_cases i
    · simp [Q]
    · simp [U]
  have hA' : z.secantMatrix = !![1, -2 * ε; -2 * ε, 1] := by
    simpa only [TwoPhaseControls.second_matrix] using hA
  have hτ' : z.tau = 1 / 3 := by
    simpa only [TwoPhaseControls.second_tau] using hτ
  have hβne : G ^ 2 * ε ^ 4 * beta ≠ 0 := by
    rw [← preconditionedEnergySecondControl z ε L H Q U G]
    · exact z.stepLengthDenominator_ne_zero
    · exact hH
    · exact hg
    · exact hA
  have hγne : G ^ 2 * ε ^ 4 * gamma ≠ 0 := by
    rw [← secantImageEnergySecondControl z ε L H Q U G]
    · exact ne_of_gt z.secantImageEnergy_pos
    · exact hH
    · exact hg
    · exact hA
  have hG : G ≠ 0 := by
    intro hG
    apply hβne
    simp [hG]
  have hε : ε ≠ 0 := by
    intro hε
    apply hβne
    simp [hε]
  have hbeta : beta ≠ 0 := right_ne_zero_of_mul hβne
  have hgamma : gamma ≠ 0 := right_ne_zero_of_mul hγne
  -- Normalize the two full energies once before applying the rank-two formulas.
  have hβ :
      (ε ^ 4 * L * (G * Q)) *
          (1 * (ε ^ 4 * L * (G * Q)) + (-2 * ε) * (H * (G * (ε ^ 2 * U)))) +
        (H * (G * (ε ^ 2 * U))) *
          ((-2 * ε) * (ε ^ 4 * L * (G * Q)) + 1 * (H * (G * (ε ^ 2 * U)))) =
        G ^ 2 * ε ^ 4 * beta := by
    dsimp [beta, w₁, w₂]
    ring
  have hγ :
      (ε ^ 4 * L) *
          (1 * (ε ^ 4 * L * (G * Q)) + (-2 * ε) * (H * (G * (ε ^ 2 * U)))) ^ 2 +
        H * ((-2 * ε) * (ε ^ 4 * L * (G * Q)) +
          1 * (H * (G * (ε ^ 2 * U)))) ^ 2 =
        G ^ 2 * ε ^ 4 * gamma := by
    dsimp [gamma, w₁, w₂]
    ring
  apply Prod.ext
  · -- The four metric entries now reduce to the canceled residual formulas.
    rw [z.nextInverseHessian_eigenframe (ε ^ 4 * L) H (G * Q)
      (G * (ε ^ 2 * U)) 1 (-2 * ε) 1 hH hg' hA']
    rw [hβ, hγ]
    unfold outputMetric
    dsimp [L, H, Q, U, w₁, w₂, beta, gamma] at hβne hγne hbeta hgamma ⊢
    ext i j
    fin_cases i
    · fin_cases j
      · simp
        field_simp [hG, hε, hβne, hγne, hbeta, hgamma]
        ring
      · simp
        field_simp [hG, hε, hβne, hγne, hbeta, hgamma]
        ring
    · fin_cases j
      · simp
        field_simp [hG, hε, hβne, hγne, hbeta, hgamma]
        ring
      · simp
        field_simp [hG, hε, hβne, hγne, hbeta, hgamma]
        ring
  · -- The two gradient coordinates use the same normalized step-length energy.
    rw [z.nextGradient_eigenframe (ε ^ 4 * L) H (G * Q)
      (G * (ε ^ 2 * U)) 1 (-2 * ε) 1 hH hg' hA', hτ', hβ]
    unfold outputGradient
    dsimp [L, H, Q, U, w₁, w₂, beta] at hβne hbeta ⊢
    ext i
    fin_cases i
    · simp
      field_simp [hG, hε, hβne, hbeta]
      ring
    · simp
      field_simp [hG, hε, hβne, hbeta]
      ring

/-- The unscaled metric and gradient residuals of the second DFP update. -/
private def residualData (x : ℝ × ℝ × ℝ) : (ℝ × ℝ × ℝ) × (ℝ × ℝ) :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
  let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
  let delta := L * Q ^ 2 + H * U ^ 2
  let a := L - ε ^ 6 * L ^ 2 * w₁ ^ 2 / gamma + L ^ 2 * Q ^ 2 / beta
  let b := -(ε ^ 3 * L * H * w₁ * w₂ / gamma) + L * Q * H * U / beta
  let d := H - H ^ 2 * w₂ ^ 2 / gamma + H ^ 2 * U ^ 2 / beta
  let q := Q - ε ^ 3 * delta * w₁ / (3 * beta)
  let v := U - delta * w₂ / (3 * beta)
  ((a, b, d), (q, v))

/-- At the base parameters, the second-update residuals have their reference values. -/
private lemma residualData_base :
    residualData (0, 2, 1) = (((6, 2, 1), (1, 0)) : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) := by
  -- The first-leg factors specialize before the residual arithmetic is normalized.
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  norm_num [residualData, hspectral, hgradient]

/-- The second-update residual data are analytic at the base parameters. -/
private lemma analyticAt_residualData : AnalyticAt ℝ residualData (0, 2, 1) := by
  have hall := DFP.FirstLeg.factorsAnalytic
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hspectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
    apply (analyticAt_fst.comp hall).congr
    filter_upwards [] with x
    rfl
  have hgradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
    apply (analyticAt_fst.comp (analyticAt_snd.comp hall)).congr
    filter_upwards [] with x
    rfl
  have hL : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1)
      (0, 2, 1) := by
    apply (analyticAt_fst.comp hspectral).congr
    filter_upwards [] with x
    rfl
  have hH : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2)
      (0, 2, 1) := by
    apply (analyticAt_snd.comp hspectral).congr
    filter_upwards [] with x
    rfl
  have hQ : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1)
      (0, 2, 1) := by
    apply (analyticAt_fst.comp hgradient).congr
    filter_upwards [] with x
    rfl
  have hU : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2)
      (0, 2, 1) := by
    apply (analyticAt_snd.comp hgradient).congr
    filter_upwards [] with x
    rfl
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  let εf : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.1
  let Lf : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1
  let Hf : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2
  let Qf : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1
  let Uf : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2
  let w₁ : ℝ × ℝ × ℝ → ℝ := fun x ↦ εf x * Lf x * Qf x - 2 * Hf x * Uf x
  let w₂ : ℝ × ℝ × ℝ → ℝ := fun x ↦ Hf x * Uf x - 2 * εf x ^ 3 * Lf x * Qf x
  let beta : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ εf x ^ 3 * Lf x * Qf x * w₁ x + Hf x * Uf x * w₂ x
  let gamma : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ εf x ^ 6 * Lf x * w₁ x ^ 2 + Hf x * w₂ x ^ 2
  let delta : ℝ × ℝ × ℝ → ℝ := fun x ↦ Lf x * Qf x ^ 2 + Hf x * Uf x ^ 2
  have hεf : AnalyticAt ℝ εf (0, 2, 1) := hε
  have hLf : AnalyticAt ℝ Lf (0, 2, 1) := hL
  have hHf : AnalyticAt ℝ Hf (0, 2, 1) := hH
  have hQf : AnalyticAt ℝ Qf (0, 2, 1) := hQ
  have hUf : AnalyticAt ℝ Uf (0, 2, 1) := hU
  have hw₁ : AnalyticAt ℝ w₁ (0, 2, 1) := by
    dsimp [w₁]
    fun_prop
  have hw₂ : AnalyticAt ℝ w₂ (0, 2, 1) := by
    dsimp [w₂]
    fun_prop
  have hbeta : AnalyticAt ℝ beta (0, 2, 1) := by
    dsimp [beta]
    fun_prop
  have hgamma : AnalyticAt ℝ gamma (0, 2, 1) := by
    dsimp [gamma]
    fun_prop
  have hdelta : AnalyticAt ℝ delta (0, 2, 1) := by
    dsimp [delta]
    fun_prop
  have hbeta_ne : beta (0, 2, 1) ≠ 0 := by
    norm_num [beta, w₁, w₂, εf, Lf, Hf, Qf, Uf, hspectralBase, hgradientBase]
  have hgamma_ne : gamma (0, 2, 1) ≠ 0 := by
    norm_num [gamma, w₁, w₂, εf, Lf, Hf, Qf, Uf, hspectralBase, hgradientBase]
  have hthreeBeta_ne : 3 * beta (0, 2, 1) ≠ 0 := mul_ne_zero (by norm_num) hbeta_ne
  let a : ℝ × ℝ × ℝ → ℝ := fun x ↦
    Lf x - εf x ^ 6 * Lf x ^ 2 * w₁ x ^ 2 / gamma x + Lf x ^ 2 * Qf x ^ 2 / beta x
  let b : ℝ × ℝ × ℝ → ℝ := fun x ↦
    -(εf x ^ 3 * Lf x * Hf x * w₁ x * w₂ x / gamma x) +
      Lf x * Qf x * Hf x * Uf x / beta x
  let d : ℝ × ℝ × ℝ → ℝ := fun x ↦
    Hf x - Hf x ^ 2 * w₂ x ^ 2 / gamma x + Hf x ^ 2 * Uf x ^ 2 / beta x
  let q : ℝ × ℝ × ℝ → ℝ := fun x ↦
    Qf x - εf x ^ 3 * delta x * w₁ x / (3 * beta x)
  let v : ℝ × ℝ × ℝ → ℝ := fun x ↦
    Uf x - delta x * w₂ x / (3 * beta x)
  -- Each residual component now follows from one rational analytic expression.
  have ha : AnalyticAt ℝ a (0, 2, 1) := by
    dsimp [a]
    fun_prop
  have hb : AnalyticAt ℝ b (0, 2, 1) := by
    dsimp [b]
    fun_prop
  have hd : AnalyticAt ℝ d (0, 2, 1) := by
    dsimp [d]
    fun_prop
  have hq : AnalyticAt ℝ q (0, 2, 1) := by
    dsimp [q]
    fun_prop (disch := exact hthreeBeta_ne)
  have hv : AnalyticAt ℝ v (0, 2, 1) := by
    dsimp [v]
    fun_prop (disch := exact hthreeBeta_ne)
  have hdata := (ha.prod (hb.prod hd)).prod (hq.prod hv)
  apply hdata.congr
  filter_upwards [] with x
  -- Unfolding only at this interface identifies the named residual components.
  rfl

/-- The second updated metric is obtained by restoring its row and column powers to the
unscaled metric residuals. -/
private lemma outputMetric_eq_residualData (x : ℝ × ℝ × ℝ) :
    outputMetric x.1 x.2.1 x.2.2 =
      !![x.1 ^ 4 * (residualData x).1.1,
          x.1 ^ 2 * (residualData x).1.2.1;
        x.1 ^ 2 * (residualData x).1.2.1, (residualData x).1.2.2] := by
  -- Both sides expose the same three residual entries.
  rfl

/-- The normalized second updated gradient restores only the second-coordinate square. -/
private lemma outputGradient_eq_residualData (x : ℝ × ℝ × ℝ) :
    outputGradient x.1 x.2.1 x.2.2 =
      ![(residualData x).2.1, x.1 ^ 2 * (residualData x).2.2] := by
  -- Both sides expose the same two residual coordinates.
  rfl

/-- The three independent entries of the canceled second updated metric. -/
private def metricEntryTriple (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (outputMetric x.1 x.2.1 x.2.2 0 0,
    outputMetric x.1 x.2.1 x.2.2 0 1,
    outputMetric x.1 x.2.1 x.2.2 1 1)

/-- The metric-entry triple is analytic at the base parameters. -/
private lemma analyticAt_metricEntryTriple : AnalyticAt ℝ metricEntryTriple (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have ha := (analyticAt_fst.comp analyticAt_fst).comp analyticAt_residualData
  have hb := ((analyticAt_fst.comp analyticAt_snd).comp analyticAt_fst).comp
    analyticAt_residualData
  have hd := ((analyticAt_snd.comp analyticAt_snd).comp analyticAt_fst).comp
    analyticAt_residualData
  have hentries := ((hε.pow 4).mul ha).prod (((hε.pow 2).mul hb).prod hd)
  apply hentries.congr
  filter_upwards [] with x
  -- The residual interface keeps this projection comparison definitional.
  rw [metricEntryTriple, outputMetric_eq_residualData]
  simp

/-- At the base parameters, the metric-entry triple is the reference diagonal triple. -/
private lemma metricEntryTriple_base :
    metricEntryTriple (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
  -- Restore the vanishing powers after evaluating the residual data.
  rw [metricEntryTriple, outputMetric_eq_residualData, residualData_base]
  norm_num

/-- The fixed frame depends on the metric only through its three independent entries. -/
private lemma frame_eq_frameOfMetricEntries (x : ℝ × ℝ × ℝ) :
    frame x.1 x.2.1 x.2.2 = EuclideanPlane.frame
      (RealSymmetric2.lowVector (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
  -- This is the projection interface for the frame construction.
  rfl

/-- Each entry of the fixed second-leg eigenframe is analytic at the base parameters. -/
private lemma analyticAt_frameEntry (i j : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ frame x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_frame i j
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntryTriple_base] at houter
  have hframe := houter.comp analyticAt_metricEntryTriple
  apply hframe.congr
  filter_upwards [] with x
  -- Rewrite through the frame interface without unfolding its normalization.
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M i j)
    (frame_eq_frameOfMetricEntries x).symm

/-- Each coordinate of the normalized second updated gradient is analytic at the base. -/
private lemma analyticAt_outputGradientEntry (i : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ outputGradient x.1 x.2.1 x.2.2 i) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hq : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (residualData x).2.1)
      (0, 2, 1) := by
    apply ((analyticAt_fst.comp analyticAt_snd).comp analyticAt_residualData).congr
    filter_upwards [] with x
    rfl
  have hv : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (residualData x).2.2)
      (0, 2, 1) := by
    apply ((analyticAt_snd.comp analyticAt_snd).comp analyticAt_residualData).congr
    filter_upwards [] with x
    rfl
  fin_cases i
  · -- The low coordinate is already unscaled.
    apply hq.congr
    filter_upwards [] with x
    rw [outputGradient_eq_residualData]
    rfl
  · -- The high coordinate restores the explicit square.
    apply ((hε.pow 2).mul hv).congr
    filter_upwards [] with x
    rw [outputGradient_eq_residualData]
    rfl

/-- Near the base point, the fixed analytic low eigenvector is oriented toward
the normalized second updated gradient. -/
theorem frameOriented :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < (coordinates x.1 x.2.1 x.2.2).1 := by
  -- Continuity preserves the positive low-frame coordinate at the diagonal base point.
  have hcoordinate : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ (coordinates x.1 x.2.1 x.2.2).1) (0, 2, 1) := by
    have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
      with_reducible_and_instances rfl
    rw [htop]
    have hsum := ((analyticAt_frameEntry 0 0).continuousAt.mul
        (analyticAt_outputGradientEntry 0).continuousAt).add
        ((analyticAt_frameEntry 1 0).continuousAt.mul
          (analyticAt_outputGradientEntry 1).continuousAt)
    have hsum' : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
        frame x.1 x.2.1 x.2.2 0 0 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 0 * outputGradient x.1 x.2.1 x.2.2 1)
        (0, 2, 1) := by
      apply hsum.congr
      filter_upwards [] with x
      rfl
    simpa [coordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hsum'
  apply hcoordinate.eventually
  apply Ioi_mem_nhds
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  simp [coordinates, frame, outputMetric, outputGradient, hspectral, hgradient,
    RealSymmetric2.frame_diag, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The high eigenvalue of the second updated metric is analytic at the base parameters. -/
private lemma analyticAt_highEigenvalue : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ RealSymmetric2.high (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_high
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntryTriple_base] at houter
  -- Analyticity is transported through the metric-entry interface.
  exact houter.comp analyticAt_metricEntryTriple

/-- The high eigenvalue of the second updated metric stays nonzero near the base. -/
private lemma eventually_highEigenvalue_ne_zero :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      RealSymmetric2.high (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2 ≠ 0 := by
  have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  rw [htop]
  apply analyticAt_highEigenvalue.continuousAt.eventually_ne
  rw [metricEntryTriple_base]
  -- The trace, determinant, and ordering characterize the high root as one.
  have hsum := RealSymmetric2.low_add_high 0 0 1
  have hprod := RealSymmetric2.low_mul_high 0 0 1
  have hle := RealSymmetric2.low_le_high 0 0 1
  nlinarith

/-- Scaling a symmetric matrix's first row and column extracts the fourth power from
its low eigenvalue. -/
private lemma low_scaledFactorization (ε a b d : ℝ)
    (hhigh : RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d ≠ 0) :
    RealSymmetric2.low (ε ^ 4 * a) (ε ^ 2 * b) d =
      ε ^ 4 * ((a * d - b ^ 2) /
        RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d) := by
  -- Divide the low-high determinant identity by the nonzero high eigenvalue.
  rw [← mul_div_assoc]
  apply (eq_div_iff hhigh).2
  rw [RealSymmetric2.low_mul_high]
  ring

/-- Locally at `(0, 2, 1)`, the second updated low and high eigenvalues factor as
`ε ^ 4 * L₂` and `ℋ₂`. -/
theorem spectrumFactorization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      eigenvalues x.1 x.2.1 x.2.2 =
        (x.1 ^ 4 * (spectralFactors x.1 x.2.1 x.2.2).1,
          (spectralFactors x.1 x.2.1 x.2.2).2) := by
  filter_upwards [eventually_highEigenvalue_ne_zero] with x hx
  -- The determinant identity cancels the displayed fourth power from the low root.
  unfold metricEntryTriple at hx
  unfold eigenvalues spectralFactors
  dsimp at hx ⊢
  apply Prod.ext
  · exact low_scaledFactorization _ _ _ _ hx
  · rfl

/-- Locally at `(0, 2, 1)`, the second-leg eigenframe diagonalizes the updated metric
with diagonal entries `ε ^ 4 * L₂` and `ℋ₂`. -/
theorem frameDiagonalization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (frame x.1 x.2.1 x.2.2).transpose * outputMetric x.1 x.2.1 x.2.2 *
          frame x.1 x.2.1 x.2.2 =
        Matrix.diagonal
          ![x.1 ^ 4 * (spectralFactors x.1 x.2.1 x.2.2).1,
            (spectralFactors x.1 x.2.1 x.2.2).2] := by
  -- First restrict to the chart where the fixed low-eigenvector branch is valid.
  have ha : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_metricEntryTriple
  have hd : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2) (0, 2, 1) :=
    (analyticAt_snd.comp analyticAt_snd).comp analyticAt_metricEntryTriple
  have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  rw [htop]
  have hdiffRaw := (hd.sub ha).continuousAt
  have hdiff : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2 - (metricEntryTriple x).1)
      (0, 2, 1) := by
    apply hdiffRaw.congr
    filter_upwards [] with x
    rfl
  have hchart : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (metricEntryTriple x).1 < (metricEntryTriple x).2.2 := by
    have hpos : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
        0 < (metricEntryTriple x).2.2 - (metricEntryTriple x).1 := by
      apply hdiff.eventually
      have hbaseDiff :
          ((fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2 - (metricEntryTriple x).1)
            (0, 2, 1)) = 1 := by
        dsimp
        rw [metricEntryTriple_base]
        norm_num
      rw [hbaseDiff]
      have hone_pos : 0 < (1 : ℝ) := by
        norm_num
      exact Ioi_mem_nhds hone_pos
    simpa only [sub_pos] using hpos
  -- On the common neighborhood, factor the spectrum and apply exact diagonalization.
  filter_upwards [hchart, spectrumFactorization] with x hx hspectrum
  -- Record the two projection interfaces before invoking the spectral theorem.
  have hmetric : outputMetric x.1 x.2.1 x.2.2 =
      RealSymmetric2.matrix (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2 := by
    unfold metricEntryTriple RealSymmetric2.matrix
    rw [outputMetric_eq_residualData]
    simp
  have heigen : eigenvalues x.1 x.2.1 x.2.2 =
      (RealSymmetric2.low (metricEntryTriple x).1
          (metricEntryTriple x).2.1 (metricEntryTriple x).2.2,
        RealSymmetric2.high (metricEntryTriple x).1
          (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
    rfl
  have hlow := congrArg Prod.fst hspectrum
  have hhigh := congrArg Prod.snd hspectrum
  rw [heigen] at hlow hhigh
  simp only at hlow hhigh
  rw [frame_eq_frameOfMetricEntries, hmetric, ← hlow, ← hhigh]
  exact RealSymmetric2.frame_diagonalizes (metricEntryTriple x).1
    (metricEntryTriple x).2.1 (metricEntryTriple x).2.2 hx

/-- Locally at `(0, 2, 1)`, the oriented second updated gradient coordinates factor as
`G • ![𝒢₂, ε ^ 2 * U₂]` for every amplitude `G`. -/
theorem gradientFactorization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), ∀ G : ℝ,
      (frame x.1 x.2.1 x.2.2).transpose *ᵥ
          (G • outputGradient x.1 x.2.1 x.2.2) =
        G • ![(gradientFactors x.1 x.2.1 x.2.2).1,
          x.1 ^ 2 * (gradientFactors x.1 x.2.1 x.2.2).2] := by
  filter_upwards [] with x
  intro G
  -- The two frame columns expose exactly the residual coordinate numerators.
  unfold gradientFactors frame outputMetric outputGradient
  ext i
  fin_cases i
  · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- Canonical recovery cancels fourth- and second-power coordinate factors. -/
private lemma recovered_scaledFactorization (ε L H Q U : ℝ) (hε : ε ≠ 0) :
    (CycleBoundaryState.recoveryRadius (ε ^ 4 * L) H Q (ε ^ 2 * U),
      CycleBoundaryState.recoveryShape (ε ^ 4 * L) H Q (ε ^ 2 * U)) =
        (ε ^ 2 * (L * Q / (H * U)), H * U ^ 2 / (L * Q ^ 2)) := by
  unfold CycleBoundaryState.recoveryRadius CycleBoundaryState.recoveryShape
  apply Prod.ext
  · -- Zero high factors are trivial; otherwise cancel the common powers and factors.
    dsimp
    by_cases hH : H = 0
    · simp [hH]
    by_cases hU : U = 0
    · simp [hU]
    field_simp [hε, hH, hU]
  · -- Zero low factors are trivial; otherwise the same cancellation gives the shape.
    dsimp
    by_cases hL : L = 0
    · simp [hL]
    by_cases hQ : Q = 0
    · simp [hQ]
    field_simp [hε, hL, hQ]

/-- Locally at `(0, 2, 1)` away from `ε = 0`, canonical recovery yields radius
`ε ^ 2 * ℛ₂` and shape `p₂`. -/
theorem canonicalFactorization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.1 ≠ 0 →
      recovered x.1 x.2.1 x.2.2 =
        (x.1 ^ 2 * (canonicalFactors x.1 x.2.1 x.2.2).1,
          (canonicalFactors x.1 x.2.1 x.2.2).2) := by
  filter_upwards [spectrumFactorization, gradientFactorization] with x hspectrum hgradient
  intro hε
  have hvector := hgradient 1
  simp only [one_smul] at hvector
  have hcoordinates : coordinates x.1 x.2.1 x.2.2 =
      ((gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (gradientFactors x.1 x.2.1 x.2.2).2) := by
    unfold coordinates
    apply Prod.ext
    · exact congrArg (fun v : Fin 2 → ℝ ↦ v 0) hvector
    · exact congrArg (fun v : Fin 2 → ℝ ↦ v 1) hvector
  -- Substitute both factorizations before applying the generic power cancellation.
  unfold recovered
  dsimp
  rw [hspectrum, hcoordinates]
  unfold canonicalFactors
  dsimp
  exact recovered_scaledFactorization _ _ _ _ _ hε

/-- The low eigenvalue of the second updated metric is analytic at the base parameters. -/
private lemma analyticAt_lowEigenvalue : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ RealSymmetric2.low (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntryTriple_base] at houter
  -- Compose the branch-local eigenvalue with the analytic metric entries.
  exact houter.comp analyticAt_metricEntryTriple

/-- The low eigenvalue of the base metric is zero. -/
private lemma lowEigenvalue_base : RealSymmetric2.low (metricEntryTriple (0, 2, 1)).1
    (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 = 0 := by
  rw [metricEntryTriple_base]
  -- Trace, determinant, and ordering determine the two base eigenvalues.
  have hsum := RealSymmetric2.low_add_high 0 0 1
  have hprod := RealSymmetric2.low_mul_high 0 0 1
  have hle := RealSymmetric2.low_le_high 0 0 1
  nlinarith

/-- The high eigenvalue of the base metric is one. -/
private lemma highEigenvalue_base : RealSymmetric2.high (metricEntryTriple (0, 2, 1)).1
    (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 = 1 := by
  rw [metricEntryTriple_base]
  -- Trace, determinant, and ordering determine the two base eigenvalues.
  have hsum := RealSymmetric2.low_add_high 0 0 1
  have hprod := RealSymmetric2.low_mul_high 0 0 1
  have hle := RealSymmetric2.low_le_high 0 0 1
  nlinarith

/-- The squared norm used to normalize the fixed low eigenvector. -/
private def lowDenomRadicand (x : ℝ × ℝ × ℝ) : ℝ :=
  ((metricEntryTriple x).2.2 -
      RealSymmetric2.low (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) ^ 2 +
    (metricEntryTriple x).2.1 ^ 2

/-- The low-eigenvector normalization radicand is analytic at the base. -/
private lemma analyticAt_lowDenomRadicand : AnalyticAt ℝ lowDenomRadicand (0, 2, 1) := by
  have hb : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.1)
      (0, 2, 1) := by
    apply ((analyticAt_fst.comp analyticAt_snd).comp analyticAt_metricEntryTriple).congr
    filter_upwards [] with x
    rfl
  have hd : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2)
      (0, 2, 1) := by
    apply ((analyticAt_snd.comp analyticAt_snd).comp analyticAt_metricEntryTriple).congr
    filter_upwards [] with x
    rfl
  have hradicand := ((hd.sub analyticAt_lowEigenvalue).pow 2).add (hb.pow 2)
  apply hradicand.congr
  filter_upwards [] with x
  -- The named radicand is exactly the squared norm expression.
  rfl

/-- The low-eigenvector normalization denominator is analytic at the base. -/
private lemma analyticAt_lowDenom : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ RealSymmetric2.lowDenom (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) (0, 2, 1) := by
  have hradicand_pos : 0 < lowDenomRadicand (0, 2, 1) := by
    unfold lowDenomRadicand
    rw [metricEntryTriple_base]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap]
  have hsqrtAt : AnalyticAt ℝ Real.sqrt (lowDenomRadicand (0, 2, 1)) := by
    have hformula : AnalyticAt ℝ
        (fun y : ℝ ↦ NormedSpace.exp (Real.log y * (1 / 2 : ℝ)))
        (lowDenomRadicand (0, 2, 1)) :=
      (NormedSpace.exp_analytic _).comp
        ((analyticAt_log hradicand_pos).mul analyticAt_const)
    apply hformula.congr
    filter_upwards [eventually_gt_nhds hradicand_pos] with y hy
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, Real.exp_eq_exp_ℝ]
  have hsqrt := hsqrtAt.comp (f := lowDenomRadicand) analyticAt_lowDenomRadicand
  apply hsqrt.congr
  filter_upwards [] with x
  -- `lowDenom` is the square root of the named radicand.
  rfl

/-- The removable spectral factors are the determinant residual divided by the high root. -/
private lemma spectralFactors_eq_residualFormula (x : ℝ × ℝ × ℝ) :
    spectralFactors x.1 x.2.1 x.2.2 =
      (((residualData x).1.1 * (residualData x).1.2.2 -
          (residualData x).1.2.1 ^ 2) /
          RealSymmetric2.high (metricEntryTriple x).1
            (metricEntryTriple x).2.1 (metricEntryTriple x).2.2,
        RealSymmetric2.high (metricEntryTriple x).1
          (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
  -- This projection lemma hides the full residual construction from later proofs.
  rfl

/-- The removable spectral factors are analytic at the base parameters. -/
private lemma analyticAt_spectralFactors : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ spectralFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have ha := (analyticAt_fst.comp analyticAt_fst).comp analyticAt_residualData
  have hb := ((analyticAt_fst.comp analyticAt_snd).comp analyticAt_fst).comp
    analyticAt_residualData
  have hd := ((analyticAt_snd.comp analyticAt_snd).comp analyticAt_fst).comp
    analyticAt_residualData
  have hhigh_ne : RealSymmetric2.high (metricEntryTriple (0, 2, 1)).1
      (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 ≠ 0 := by
    rw [highEigenvalue_base]
    norm_num
  have hlowFactor := ((ha.mul hd).sub (hb.pow 2)).div analyticAt_highEigenvalue hhigh_ne
  have hpairs := hlowFactor.prod analyticAt_highEigenvalue
  apply hpairs.congr
  filter_upwards [] with x
  -- Rewrite the public factor pair through its residual formula.
  exact (spectralFactors_eq_residualFormula x).symm

/-- The removable gradient factors are the normalized fixed-frame residual coordinates. -/
private lemma gradientFactors_eq_residualFormula (x : ℝ × ℝ × ℝ) :
    gradientFactors x.1 x.2.1 x.2.2 =
      ((((residualData x).1.2.2 -
            RealSymmetric2.low (metricEntryTriple x).1
              (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) *
          (residualData x).2.1 - x.1 ^ 4 * (residualData x).1.2.1 *
            (residualData x).2.2) /
          RealSymmetric2.lowDenom (metricEntryTriple x).1
            (metricEntryTriple x).2.1 (metricEntryTriple x).2.2,
        ((residualData x).1.2.1 * (residualData x).2.1 +
            ((residualData x).1.2.2 -
              RealSymmetric2.low (metricEntryTriple x).1
                (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) *
              (residualData x).2.2) /
          RealSymmetric2.lowDenom (metricEntryTriple x).1
            (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
  -- This projection lemma hides the full fixed-frame coordinate construction.
  rfl

/-- The removable gradient factors are analytic at the base parameters. -/
private lemma analyticAt_gradientFactors : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hb := ((analyticAt_fst.comp analyticAt_snd).comp analyticAt_fst).comp
    analyticAt_residualData
  have hd := ((analyticAt_snd.comp analyticAt_snd).comp analyticAt_fst).comp
    analyticAt_residualData
  have hq := (analyticAt_fst.comp analyticAt_snd).comp analyticAt_residualData
  have hv := (analyticAt_snd.comp analyticAt_snd).comp analyticAt_residualData
  have hdenom_ne : RealSymmetric2.lowDenom (metricEntryTriple (0, 2, 1)).1
      (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 ≠ 0 := by
    rw [RealSymmetric2.lowDenom, metricEntryTriple_base]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap]
  have hlowFactor := (((hd.sub analyticAt_lowEigenvalue).mul hq).sub
    (((hε.pow 4).mul hb).mul hv)).div analyticAt_lowDenom hdenom_ne
  have hhighFactor := ((hb.mul hq).add
    ((hd.sub analyticAt_lowEigenvalue).mul hv)).div analyticAt_lowDenom hdenom_ne
  have hpairs := hlowFactor.prod hhighFactor
  apply hpairs.congr
  filter_upwards [] with x
  -- Rewrite the public factor pair through its residual formula.
  exact (gradientFactors_eq_residualFormula x).symm

/-- The spectral and gradient removable factors have their reference base values. -/
private lemma factorData_base :
    (spectralFactors 0 2 1, gradientFactors 0 2 1) = ((2, 1), (1, 2)) := by
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  -- Evaluate the residual formulas at the diagonal base metric.
  norm_num [spectralFactors, gradientFactors, hspectral, hgradient,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
    RealSymmetric2.lowDenom]

/-- The removable canonical factors are analytic at the base parameters. -/
private lemma analyticAt_canonicalFactors : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ canonicalFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hL := analyticAt_fst.comp analyticAt_spectralFactors
  have hH := analyticAt_snd.comp analyticAt_spectralFactors
  have hQ := analyticAt_fst.comp analyticAt_gradientFactors
  have hU := analyticAt_snd.comp analyticAt_gradientFactors
  have hhighDenom_ne :
      (spectralFactors 0 2 1).2 * (gradientFactors 0 2 1).2 ≠ 0 := by
    have hspectral : spectralFactors 0 2 1 = (2, 1) := congrArg Prod.fst factorData_base
    have hgradient : gradientFactors 0 2 1 = (1, 2) := congrArg Prod.snd factorData_base
    rw [hspectral, hgradient]
    norm_num
  have hlowDenom_ne :
      (spectralFactors 0 2 1).1 * (gradientFactors 0 2 1).1 ^ 2 ≠ 0 := by
    have hspectral : spectralFactors 0 2 1 = (2, 1) := congrArg Prod.fst factorData_base
    have hgradient : gradientFactors 0 2 1 = (1, 2) := congrArg Prod.snd factorData_base
    rw [hspectral, hgradient]
    norm_num
  have hradius := (hL.mul hQ).div (hH.mul hU) hhighDenom_ne
  have hshape := (hH.mul (hU.pow 2)).div (hL.mul (hQ.pow 2)) hlowDenom_ne
  have hpairs := hradius.prod hshape
  apply hpairs.congr
  filter_upwards [] with x
  -- The canonical pair is definitionally the two factor quotients.
  rfl

/-- All six removable second-leg factors are jointly real analytic at `(0, 2, 1)`. -/
theorem factorsAnalytic :
    AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ factors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
  -- Assemble the spectral, gradient, and canonical analytic pairs.
  exact analyticAt_spectralFactors.prod
    (analyticAt_gradientFactors.prod analyticAt_canonicalFactors)

/-- The second-leg spectral, gradient, radius, and shape factors have base values
`(2, 1, 1, 2, 1, 2)`. -/
theorem factorsBase :
    factors 0 2 1 = ((2, 1), (1, 2), (1, 2)) := by
  have hspectral : spectralFactors 0 2 1 = (2, 1) := congrArg Prod.fst factorData_base
  have hgradient : gradientFactors 0 2 1 = (1, 2) := congrArg Prod.snd factorData_base
  -- Substitute the two factor pairs before normalizing the canonical quotients.
  norm_num [factors, canonicalFactors, hspectral, hgradient]

/-- The low second-leg gradient factor is constant on the positive zero-scale slice;
this cancellation supports Lemma 4.15 (Near-return winding number is nonzero). -/
theorem gradientFactors_low_zeroScale (p h : ℝ) (hp : 0 < p) :
    (gradientFactors 0 p h).1 = 1 := by
  have hp_one_ne : p + 1 ≠ 0 := by
    linarith
  have hspectral : DFP.FirstLeg.spectralFactors 0 p h = (h * p, 1) := by
    norm_num [DFP.FirstLeg.spectralFactors, DFP.FirstLeg.outputMetric,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap]
  have hgradient : DFP.FirstLeg.gradientFactors 0 p h = (1, (p + 1) / 3) := by
    norm_num [DFP.FirstLeg.gradientFactors, RealSymmetric2.low,
      RealSymmetric2.gap, RealSymmetric2.lowDenom]
    ring
  norm_num [gradientFactors, hspectral, hgradient,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
    RealSymmetric2.lowDenom]
  field_simp [hp_one_ne]
  all_goals norm_num

/- Claim 2 of Lemma 4.15 — `DFP.SecondLeg.lowGradientFactorTransverseFDeriv_norm_bound`
(the uniform cubic bound on the transverse derivative of the low gradient factor) — is now proven
unconditionally in the leaf module
`ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseNormBoundFinal`.
Its declaration site had to move out of this file: `SecondLeg.lean` is imported *by* the second-scale
certificate chain, so the proof term (which depends on that chain) cannot live here without an import
cycle.  Consumers should `import all ...SecondLeg.TransverseNormBoundFinal`. -/

end DFP.SecondLeg
