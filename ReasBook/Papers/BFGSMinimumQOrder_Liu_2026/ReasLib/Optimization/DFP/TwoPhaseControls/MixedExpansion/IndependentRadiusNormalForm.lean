module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap
public import ReasLib.Analysis.Calculus.Analytic.RecoveryFactors
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap
import all ReasLib.Analysis.Calculus.Analytic.RecoveryFactors

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/- The local raw-step mirror keeps the private evaluator boundary opaque to later
   normalization lemmas while preserving its exact computational body. -/
def independentRawStep (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) :=
  let v := H *ᵥ g
  let α := control.tau * (g ⬝ᵥ v) / (v ⬝ᵥ (control.matrix *ᵥ v))
  let s := -(α • v)
  let y := control.matrix *ᵥ s
  (Matrix.inverseDFPUpdate H s y, g + y)

def independentMapRaw (b r p h : ℝ) : ℝ × ℝ × ℝ :=
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let firstStep := independentRawStep H₀ g₀ (TwoPhaseControls.first b)
  let firstFrame := OrientedEigenframe.frame
    (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
    (WithLp.toLp 2 firstStep.2)
  let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
  let g₁ := firstFrame.transpose *ᵥ firstStep.2
  let secondStep := independentRawStep H₁ g₁ (TwoPhaseControls.second b)
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  let g₂ := secondFrame.transpose *ᵥ secondStep.2
  let lambdaMinus := RealSymmetric2.low
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
  let lambdaPlus := RealSymmetric2.high
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
  (CycleBoundaryState.recoveryRadius lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
    CycleBoundaryState.recoveryShape lambdaMinus lambdaPlus (g₂ 0) (g₂ 1),
    lambdaPlus)

lemma independentMapRaw_eq_map (b r p h : ℝ) (hr : r ≠ 0) :
    independentMapRaw b r p h = map b (r, p, h) := by
  unfold independentMapRaw map
  dsimp
  rw [if_neg hr]
  rfl

/-- The three normalized residual entries produced by the first independent-radius step. -/
def independentFirstResiduals (b r p h : ℝ) : ℝ × ℝ × ℝ :=
  let B := 1 + 2 * b * r + r ^ 2
  let C := (1 + b * r) ^ 2 + p * r ^ 2 * (b + r) ^ 2
  let a := h * p - h * p ^ 2 * r ^ 2 * (b + r) ^ 2 / C + 1 / B
  let c := 1 / B - h * p * r * (b + r) * (1 + b * r) / C
  let d := h - h * (1 + b * r) ^ 2 / C + 1 / B
  (a, c, d)

/-- The first independent-radius DFP metric after removing its common radius factors. -/
def independentFirstMetric (b r p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let t := independentFirstResiduals b r p h
  !![r ^ 2 * t.1, r * t.2.1; r * t.2.1, t.2.2]

/-- The two normalized gradient residuals produced by the first independent-radius step. -/
def independentFirstGradientResiduals (b r p : ℝ) : ℝ × ℝ :=
  let B := 1 + 2 * b * r + r ^ 2
  let q := 1 - 2 * (p + 1) * r * (b + r) / (3 * B)
  let u := p - 2 * (p + 1) * (1 + b * r) / (3 * B)
  (q, u)

/-- The first independent-radius DFP gradient after removing its common radius factor. -/
def independentFirstGradient (b r p : ℝ) : Fin 2 → ℝ :=
  let t := independentFirstGradientResiduals b r p
  ![t.1, r * t.2]

/-- The first independent-radius DFP step has the displayed normalized matrix and gradient. -/
theorem independentFirstStep_spec (z : DFP.AbstractSecantStep (Fin 2))
    (b r p h G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = (TwoPhaseControls.first b).matrix)
    (hτ : z.tau = (TwoPhaseControls.first b).tau)
    (hr : r ≠ 0) :
    (z.nextInverseHessian, z.nextGradient) =
      (independentFirstMetric b r p h, G • independentFirstGradient b r p) := by
  -- The two abstract energy denominators factor into the independent-radius residuals.
  have hβne : h ^ 2 * p ^ 2 * G ^ 2 * r ^ 2 *
      (1 + 2 * b * r + r ^ 2) ≠ 0 := by
    rw [← show z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient) =
        h ^ 2 * p ^ 2 * G ^ 2 * r ^ 2 * (1 + 2 * b * r + r ^ 2) by
      rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.first_matrix]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring]
    exact z.stepLengthDenominator_ne_zero
  have hγne : h ^ 3 * p ^ 2 * G ^ 2 * r ^ 2 *
      ((1 + b * r) ^ 2 + p * r ^ 2 * (b + r) ^ 2) ≠ 0 := by
    rw [← show (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
        (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient)) =
        h ^ 3 * p ^ 2 * G ^ 2 * r ^ 2 *
          ((1 + b * r) ^ 2 + p * r ^ 2 * (b + r) ^ 2) by
      rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.first_matrix]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring]
    exact ne_of_gt z.secantImageEnergy_pos
  have hh : h ≠ 0 := by
    intro hh
    apply hβne
    simp [hh]
  have hp : p ≠ 0 := by
    intro hp
    apply hβne
    simp [hp]
  have hG : G ≠ 0 := by
    intro hG
    apply hβne
    simp [hG]
  have hB : 1 + 2 * b * r + r ^ 2 ≠ 0 := right_ne_zero_of_mul hβne
  have hC : (1 + b * r) ^ 2 + p * r ^ 2 * (b + r) ^ 2 ≠ 0 :=
    right_ne_zero_of_mul hγne
  have hg' : z.gradient = ![G, G * (p * r)] := by
    rw [hg]
    ext i
    fin_cases i <;> simp
  have hA' : z.secantMatrix = !![1, b; b, 1] := by
    simpa only [TwoPhaseControls.first_matrix] using hA
  have hτ' : z.tau = 2 / 3 := by
    simpa only [TwoPhaseControls.first_tau] using hτ
  have hβ :
      (h * p * r ^ 2 * G) *
          (1 * (h * p * r ^ 2 * G) + b * (h * (G * (p * r)))) +
        (h * (G * (p * r))) *
          (b * (h * p * r ^ 2 * G) + 1 * (h * (G * (p * r)))) =
        h ^ 2 * p ^ 2 * G ^ 2 * r ^ 2 * (1 + 2 * b * r + r ^ 2) := by
    ring
  have hγ :
      (h * p * r ^ 2) *
          (1 * (h * p * r ^ 2 * G) + b * (h * (G * (p * r)))) ^ 2 +
        h * (b * (h * p * r ^ 2 * G) + 1 * (h * (G * (p * r)))) ^ 2 =
        h ^ 3 * p ^ 2 * G ^ 2 * r ^ 2 *
          ((1 + b * r) ^ 2 + p * r ^ 2 * (b + r) ^ 2) := by
    ring
  apply Prod.ext
  · rw [z.nextInverseHessian_eigenframe (h * p * r ^ 2) h G (G * (p * r)) 1 b 1
      hH hg' hA', hβ, hγ]
    unfold independentFirstMetric
    unfold independentFirstResiduals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      <;> field_simp [hh, hp, hG, hr, hB, hC, hβne, hγne]
      <;> ring
  · rw [z.nextGradient_eigenframe (h * p * r ^ 2) h G (G * (p * r)) 1 b 1
      hH hg' hA', hτ', hβ]
    unfold independentFirstGradient
    unfold independentFirstGradientResiduals
    ext i
    fin_cases i <;>
      simp [dotProduct, Fin.sum_univ_two]
      <;> field_simp [hh, hp, hG, hr, hB, hC, hβne]
      <;> ring

/-- The three normalized residual entries produced by the second independent-radius step. -/
def independentSecondResiduals (b r L H Q U : ℝ) : ℝ × ℝ × ℝ :=
  let w₁ := r * L * Q - 2 * b * H * U
  let w₂ := H * U - 2 * b * r * L * Q
  let β := r * L * Q * w₁ + H * U * w₂
  let γ := r ^ 2 * L * w₁ ^ 2 + H * w₂ ^ 2
  let a := L - r ^ 2 * L ^ 2 * w₁ ^ 2 / γ + L ^ 2 * Q ^ 2 / β
  let c := -r * L * H * w₁ * w₂ / γ + L * Q * H * U / β
  let d := H - H ^ 2 * w₂ ^ 2 / γ + H ^ 2 * U ^ 2 / β
  (a, c, d)

/-- The second independent-radius DFP metric after removing its common radius factors. -/
def independentSecondMetric (b r L H Q U : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let t := independentSecondResiduals b r L H Q U
  !![r ^ 2 * t.1, r * t.2.1; r * t.2.1, t.2.2]

/-- The two normalized gradient residuals produced by the second independent-radius step. -/
def independentSecondGradientResiduals (b r L H Q U : ℝ) : ℝ × ℝ :=
  let w₁ := r * L * Q - 2 * b * H * U
  let w₂ := H * U - 2 * b * r * L * Q
  let β := r * L * Q * w₁ + H * U * w₂
  let δ := L * Q ^ 2 + H * U ^ 2
  let q := Q - r * δ * w₁ / (3 * β)
  let u := U - δ * w₂ / (3 * β)
  (q, u)

/-- The second independent-radius DFP gradient after removing its common radius factor. -/
def independentSecondGradient (b r L H Q U : ℝ) : Fin 2 → ℝ :=
  let t := independentSecondGradientResiduals b r L H Q U
  ![t.1, r * t.2]

/-- The second independent-radius DFP step has the displayed normalized matrix and gradient. -/
theorem independentSecondStep_spec (z : DFP.AbstractSecantStep (Fin 2))
    (b r L H Q U G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![r ^ 2 * L, H])
    (hg : z.gradient = G • ![Q, r * U])
    (hA : z.secantMatrix = (TwoPhaseControls.second b).matrix)
    (hτ : z.tau = (TwoPhaseControls.second b).tau)
    (hr : r ≠ 0) :
    (z.nextInverseHessian, z.nextGradient) =
      (independentSecondMetric b r L H Q U,
        G • independentSecondGradient b r L H Q U) := by
  -- The two abstract energy denominators factor through the second-leg residuals.
  have hβne : G ^ 2 * r ^ 2 *
      (r * L * Q * (r * L * Q - 2 * b * H * U) +
        H * U * (H * U - 2 * b * r * L * Q)) ≠ 0 := by
    rw [← show z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient) =
        G ^ 2 * r ^ 2 *
          (r * L * Q * (r * L * Q - 2 * b * H * U) +
            H * U * (H * U - 2 * b * r * L * Q)) by
      rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.second_matrix]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring]
    exact z.stepLengthDenominator_ne_zero
  have hγne : G ^ 2 * r ^ 2 *
      (r ^ 2 * L * (r * L * Q - 2 * b * H * U) ^ 2 +
        H * (H * U - 2 * b * r * L * Q) ^ 2) ≠ 0 := by
    rw [← show (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
        (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient)) =
        G ^ 2 * r ^ 2 *
          (r ^ 2 * L * (r * L * Q - 2 * b * H * U) ^ 2 +
            H * (H * U - 2 * b * r * L * Q) ^ 2) by
      rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.second_matrix]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring]
    exact ne_of_gt z.secantImageEnergy_pos
  have hG : G ≠ 0 := by
    intro hG
    apply hβne
    simp [hG]
  have hβ :
      (r ^ 2 * L * (G * Q)) *
          (1 * (r ^ 2 * L * (G * Q)) + (-2 * b) * (H * (G * (r * U)))) +
        (H * (G * (r * U))) *
          ((-2 * b) * (r ^ 2 * L * (G * Q)) + 1 * (H * (G * (r * U)))) =
        G ^ 2 * r ^ 2 *
          (r * L * Q * (r * L * Q - 2 * b * H * U) +
            H * U * (H * U - 2 * b * r * L * Q) ) := by
    ring
  have hγ :
      (r ^ 2 * L) *
          (1 * (r ^ 2 * L * (G * Q)) + (-2 * b) * (H * (G * (r * U)))) ^ 2 +
        H * ((-2 * b) * (r ^ 2 * L * (G * Q)) + 1 * (H * (G * (r * U)))) ^ 2 =
        G ^ 2 * r ^ 2 *
          (r ^ 2 * L * (r * L * Q - 2 * b * H * U) ^ 2 +
            H * (H * U - 2 * b * r * L * Q) ^ 2) := by
    ring
  have hg' : z.gradient = ![G * Q, G * (r * U)] := by
    rw [hg]
    ext i
    fin_cases i <;> simp
  have hA' : z.secantMatrix = !![1, -2 * b; -2 * b, 1] := by
    simpa only [TwoPhaseControls.second_matrix] using hA
  have hτ' : z.tau = 1 / 3 := by
    simpa only [TwoPhaseControls.second_tau] using hτ
  apply Prod.ext
  · rw [z.nextInverseHessian_eigenframe (r ^ 2 * L) H (G * Q) (G * (r * U)) 1 (-2 * b) 1
      hH hg' hA', hβ, hγ]
    unfold independentSecondMetric
    unfold independentSecondResiduals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      <;> field_simp [hG, hr, hβne, hγne]
      <;> ring
  · rw [z.nextGradient_eigenframe (r ^ 2 * L) H (G * Q) (G * (r * U)) 1 (-2 * b) 1
      hH hg' hA', hτ', hβ]
    unfold independentSecondGradient
    unfold independentSecondGradientResiduals
    ext i
    fin_cases i <;>
      simp [dotProduct, Fin.sum_univ_two]
      <;> field_simp [hG, hr, hβne]
      <;> ring

/-- The normalized spectral factors of the first independent-radius step. -/
def independentFirstSpectralFactors (b r p h : ℝ) : ℝ × ℝ :=
  let t := independentFirstResiduals b r p h
  let high := RealSymmetric2.high (r ^ 2 * t.1) (r * t.2.1) t.2.2
  ((t.1 * t.2.2 - t.2.1 ^ 2) / high, high)

/-- The normalized oriented-gradient factors of the first independent-radius step. -/
def independentFirstGradientFactors (b r p h : ℝ) : ℝ × ℝ :=
  let t := independentFirstResiduals b r p h
  let q := (independentFirstGradientResiduals b r p).1
  let u := (independentFirstGradientResiduals b r p).2
  let low := RealSymmetric2.low (r ^ 2 * t.1) (r * t.2.1) t.2.2
  let denom := RealSymmetric2.lowDenom (r ^ 2 * t.1) (r * t.2.1) t.2.2
  (((t.2.2 - low) * q - r ^ 2 * t.2.1 * u) / denom,
    (t.2.1 * q + (t.2.2 - low) * u) / denom)

/-- The normalized spectral factors of the second independent-radius step. -/
def independentSecondSpectralFactors (b r L H Q U : ℝ) : ℝ × ℝ :=
  let t := independentSecondResiduals b r L H Q U
  let high := RealSymmetric2.high (r ^ 2 * t.1) (r * t.2.1) t.2.2
  ((t.1 * t.2.2 - t.2.1 ^ 2) / high, high)

/-- The normalized oriented-gradient factors of the second independent-radius step. -/
def independentSecondGradientFactors (b r L H Q U : ℝ) : ℝ × ℝ :=
  let t := independentSecondResiduals b r L H Q U
  let q := (independentSecondGradientResiduals b r L H Q U).1
  let u := (independentSecondGradientResiduals b r L H Q U).2
  let low := RealSymmetric2.low (r ^ 2 * t.1) (r * t.2.1) t.2.2
  let denom := RealSymmetric2.lowDenom (r ^ 2 * t.1) (r * t.2.1) t.2.2
  (((t.2.2 - low) * q - r ^ 2 * t.2.1 * u) / denom,
    (t.2.1 * q + (t.2.2 - low) * u) / denom)

/-- The first normalized residual entries along the canonical mixed path. -/
def independentRadiusFirstResiduals
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ × ℝ :=
  independentFirstResiduals z.1.1 z.2
    (2 + z.1.2.1 * z.1.1 * z.2) (1 + z.1.2.2 * z.1.1 * z.2)

/-- The first normalized gradient residuals along the canonical mixed path. -/
def independentRadiusFirstGradientResiduals
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  independentFirstGradientResiduals z.1.1 z.2
    (2 + z.1.2.1 * z.1.1 * z.2)

/-- The first normalized metric entries along the canonical mixed path. -/
def independentRadiusFirstMetricTriple
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ × ℝ :=
  let t := independentRadiusFirstResiduals z
  (z.2 ^ 2 * t.1, z.2 * t.2.1, t.2.2)

/-- The first normalized gradient coordinates along the canonical mixed path. -/
def independentRadiusFirstGradientVector
    (z : (ℝ × ℝ × ℝ) × ℝ) : Fin 2 → ℝ :=
  let t := independentRadiusFirstGradientResiduals z
  ![t.1, z.2 * t.2]

/-- The first independent-radius spectral factors along the canonical mixed path. -/
def independentRadiusFirstSpectral
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  let t := independentRadiusFirstResiduals z
  let m := independentRadiusFirstMetricTriple z
  let high := RealSymmetric2.high m.1 m.2.1 m.2.2
  ((t.1 * t.2.2 - t.2.1 ^ 2) / high, high)

/-- The first independent-radius gradient factors along the canonical mixed path. -/
def independentRadiusFirstGradient
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  let t := independentRadiusFirstResiduals z
  let g := independentRadiusFirstGradientResiduals z
  let m := independentRadiusFirstMetricTriple z
  let low := RealSymmetric2.low m.1 m.2.1 m.2.2
  let denom := RealSymmetric2.lowDenom m.1 m.2.1 m.2.2
  (((t.2.2 - low) * g.1 - z.2 ^ 2 * t.2.1 * g.2) / denom,
    (t.2.1 * g.1 + (t.2.2 - low) * g.2) / denom)

/-- The second independent-radius spectral factors along the canonical mixed path. -/
def independentRadiusSecondSpectral
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  let s := independentRadiusFirstSpectral z
  let g := independentRadiusFirstGradient z
  independentSecondSpectralFactors z.1.1 z.2 s.1 s.2 g.1 g.2

/-- The second independent-radius gradient factors along the canonical mixed path. -/
def independentRadiusSecondGradient
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  let s := independentRadiusFirstSpectral z
  let g := independentRadiusFirstGradient z
  independentSecondGradientFactors z.1.1 z.2 s.1 s.2 g.1 g.2

/-- The independent-radius normal form is the analytic recovered state in normalized
    low/high and gradient coordinates. -/
def independentRadiusNormalForm (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ × ℝ × ℝ :=
  let z := (θ, r)
  let secondS := independentRadiusSecondSpectral z
  let secondG := independentRadiusSecondGradient z
  let ρ := secondS.1 * secondG.1 / (secondS.2 * secondG.2)
  let p₂ := secondS.2 * secondG.2 ^ 2 / (secondS.1 * secondG.1 ^ 2)
  (r * ρ, p₂, secondS.2)

/- The factor triple is the stable interface between the normalized two-leg
   calculation and the final recovered state. -/

/-- The recovered normalized factors `(ρ, p₂, H₂)` of the independent-radius normal form. -/
def independentRadiusRecoveryFactors
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ × ℝ :=
  let secondS := independentRadiusSecondSpectral z
  let secondG := independentRadiusSecondGradient z
  (secondS.1 * secondG.1 / (secondS.2 * secondG.2),
    secondS.2 * secondG.2 ^ 2 / (secondS.1 * secondG.1 ^ 2), secondS.2)

/-- The normal form is the radius times the recovered radius factor, followed by
the recovered shape and high-scale factors. -/
lemma independentRadiusNormalForm_eq_recoveryFactors (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    independentRadiusNormalForm θ r =
      (r * (independentRadiusRecoveryFactors (θ, r)).1,
        (independentRadiusRecoveryFactors (θ, r)).2.1,
        (independentRadiusRecoveryFactors (θ, r)).2.2) := by
  rfl

/-- The first normalized metric triple has the diagonal base value at zero radius. -/
lemma independentRadiusFirstMetricTriple_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusFirstMetricTriple (θ, 0) = (0, 0, 1) := by
  norm_num [independentRadiusFirstMetricTriple, independentRadiusFirstResiduals,
    independentFirstResiduals, RealSymmetric2.low, RealSymmetric2.high,
    RealSymmetric2.gap]

/-- The first normalized gradient factors have base value `(1,1)`. -/
lemma independentRadiusFirstGradient_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusFirstGradient (θ, 0) = (1, 1) := by
  norm_num [independentRadiusFirstGradient, independentRadiusFirstResiduals,
    independentRadiusFirstGradientResiduals, independentFirstResiduals,
    independentFirstGradientResiduals, independentRadiusFirstMetricTriple,
    RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom]

/-- The first normalized spectral factors have base value `(2,1)`. -/
lemma independentRadiusFirstSpectral_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusFirstSpectral (θ, 0) = (2, 1) := by
  norm_num [independentRadiusFirstSpectral, independentRadiusFirstResiduals,
    independentFirstResiduals, independentRadiusFirstMetricTriple,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap]

/-- The second normalized spectral factors have base value `(2,1)`. -/
lemma independentRadiusSecondSpectral_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusSecondSpectral (θ, 0) = (2, 1) := by
  rw [independentRadiusSecondSpectral, independentRadiusFirstSpectral_zero,
    independentRadiusFirstGradient_zero]
  norm_num [independentSecondSpectralFactors, independentSecondResiduals,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap]

/-- The second normalized gradient factors have base value `(1,2)`. -/
lemma independentRadiusSecondGradient_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusSecondGradient (θ, 0) = (1, 2) := by
  rw [independentRadiusSecondGradient, independentRadiusFirstSpectral_zero,
    independentRadiusFirstGradient_zero]
  norm_num [independentSecondGradientFactors, independentSecondResiduals,
    independentSecondGradientResiduals, RealSymmetric2.low, RealSymmetric2.high,
    RealSymmetric2.gap, RealSymmetric2.lowDenom]

/-- The recovered factor triple has its canonical base value at zero radius. -/
lemma independentRadiusRecoveryFactors_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusRecoveryFactors (θ, 0) = (1, 2, 1) := by
  -- Substitute the canonical spectral and gradient factor values at zero radius.
  unfold independentRadiusRecoveryFactors
  rw [independentRadiusSecondSpectral_zero, independentRadiusSecondGradient_zero]
  norm_num

/-- The low-eigenvector denominator is analytic after an analytic metric triple
has the reference diagonal value `(0,0,1)`. -/
lemma analyticAt_lowDenom_of_analyticAt_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {m : E → ℝ × ℝ × ℝ}
    (hm : AnalyticAt ℝ m x) (hm0 : m x = (0, 0, 1)) :
    AnalyticAt ℝ (fun y ↦ RealSymmetric2.lowDenom (m y).1 (m y).2.1 (m y).2.2) x := by
  have hlowOuter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  have hlowAt : AnalyticAt ℝ
      (fun p ↦ RealSymmetric2.low p.1 p.2.1 p.2.2) (m x) := by
    rw [hm0]
    exact hlowOuter
  have hlow := hlowAt.comp (f := m) hm
  have hlow' : AnalyticAt ℝ (fun y ↦ RealSymmetric2.low (m y).1
      (m y).2.1 (m y).2.2) x := by
    simpa only [Function.comp_def] using hlow
  have hd : AnalyticAt ℝ (fun y ↦ (m y).2.2) x :=
    analyticAt_snd.comp (analyticAt_snd.comp hm)
  have hfirst : AnalyticAt ℝ (fun y ↦ (m y).2.2 -
      RealSymmetric2.low (m y).1 (m y).2.1 (m y).2.2) x := hd.sub hlow'
  have hb : AnalyticAt ℝ (fun y ↦ (m y).2.1) x :=
    analyticAt_fst.comp (analyticAt_snd.comp hm)
  let rad : E → ℝ := fun y ↦
    ((m y).2.2 - RealSymmetric2.low (m y).1 (m y).2.1 (m y).2.2) ^ 2 +
      (m y).2.1 ^ 2
  have hrad : AnalyticAt ℝ rad x := by
    exact (hfirst.pow 2).add (hb.pow 2)
  have hrad0 : 0 < rad x := by
    dsimp [rad]
    rw [hm0]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap]
  have hsqrtAt : AnalyticAt ℝ Real.sqrt (rad x) := by
    have hformula : AnalyticAt ℝ
        (fun t : ℝ ↦ NormedSpace.exp (Real.log t * (1 / 2 : ℝ))) (rad x) :=
      (NormedSpace.exp_analytic _).comp ((analyticAt_log hrad0).mul analyticAt_const)
    apply hformula.congr
    filter_upwards [eventually_gt_nhds hrad0] with t ht
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, Real.exp_eq_exp_ℝ]
  have hsqrt := hsqrtAt.comp (f := rad) hrad
  have hden : AnalyticAt ℝ (fun y ↦ RealSymmetric2.lowDenom
      (m y).1 (m y).2.1 (m y).2.2) x := by
    simpa only [rad, RealSymmetric2.lowDenom, Function.comp_def] using hsqrt
  exact hden

/-- The low eigenvalue is analytic after an analytic metric triple has the
reference diagonal value `(0,0,1)`. -/
lemma analyticAt_low_of_analyticAt_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {m : E → ℝ × ℝ × ℝ}
    (hm : AnalyticAt ℝ m x) (hm0 : m x = (0, 0, 1)) :
    AnalyticAt ℝ (fun y ↦ RealSymmetric2.low (m y).1 (m y).2.1 (m y).2.2) x := by
  have houter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  have hat : AnalyticAt ℝ (fun p ↦ RealSymmetric2.low p.1 p.2.1 p.2.2) (m x) := by
    rw [hm0]
    exact houter
  simpa only [Function.comp_def] using hat.comp (f := m) hm

/-- The high eigenvalue is analytic after an analytic metric triple has the
reference diagonal value `(0,0,1)`. -/
lemma analyticAt_high_of_analyticAt_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {m : E → ℝ × ℝ × ℝ}
    (hm : AnalyticAt ℝ m x) (hm0 : m x = (0, 0, 1)) :
    AnalyticAt ℝ (fun y ↦ RealSymmetric2.high (m y).1 (m y).2.1 (m y).2.2) x := by
  have houter := RealSymmetric2.analyticOnNhd_high
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  have hat : AnalyticAt ℝ (fun p ↦ RealSymmetric2.high p.1 p.2.1 p.2.2) (m x) := by
    rw [hm0]
    exact houter
  simpa only [Function.comp_def] using hat.comp (f := m) hm

/-- The independent-radius normal form has the canonical value at zero radius. -/
lemma independentRadiusNormalForm_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusNormalForm θ 0 = (0, 2, 1) := by
  norm_num [independentRadiusNormalForm, independentFirstSpectralFactors,
    independentRadiusFirstSpectral, independentRadiusFirstGradient,
    independentRadiusFirstResiduals, independentRadiusFirstGradientResiduals,
    independentRadiusFirstMetricTriple, independentFirstResiduals,
    independentFirstGradientResiduals, independentSecondSpectralFactors,
    independentRadiusSecondSpectral, independentRadiusSecondGradient,
    independentSecondGradientFactors, independentSecondResiduals,
    independentSecondGradientResiduals, independentSecondMetric,
    independentSecondGradient, independentFirstMetric, independentFirstGradient,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
    RealSymmetric2.lowDenom]


/-- The first independent-radius metric residuals are analytic at zero radius. -/
lemma independentRadiusFirstResiduals_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusFirstResiduals (θ, 0) := by
  have hz : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1) (θ, 0) := analyticAt_fst
  have hb : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp hz
  have hθ₂ : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2) (θ, 0) :=
    analyticAt_snd.comp hz
  have hp : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hh : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  unfold independentRadiusFirstResiduals independentFirstResiduals
  dsimp
  fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- The first independent-radius gradient residuals are analytic at zero radius. -/
lemma independentRadiusFirstGradientResiduals_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusFirstGradientResiduals (θ, 0) := by
  have hz : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1) (θ, 0) := analyticAt_fst
  have hb : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp hz
  have hθ₂ : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2) (θ, 0) :=
    analyticAt_snd.comp hz
  have hp : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  unfold independentRadiusFirstGradientResiduals independentFirstGradientResiduals
  dsimp
  fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- The first normalized metric triple is analytic at each zero-radius base point. -/
lemma independentRadiusFirstMetricTriple_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusFirstMetricTriple (θ, 0) := by
  have ht := independentRadiusFirstResiduals_analyticAt θ
  have ha : AnalyticAt ℝ (fun z ↦ z.2 ^ 2 * (independentRadiusFirstResiduals z).1) (θ, 0) := by
    exact (analyticAt_snd.pow 2).mul (analyticAt_fst.comp ht)
  have hb : AnalyticAt ℝ (fun z ↦ z.2 * (independentRadiusFirstResiduals z).2.1) (θ, 0) := by
    exact analyticAt_snd.mul (analyticAt_fst.comp (analyticAt_snd.comp ht))
  have hd : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstResiduals z).2.2) (θ, 0) := by
    exact analyticAt_snd.comp (analyticAt_snd.comp ht)
  have h := ha.prod (hb.prod hd)
  apply h.congr
  filter_upwards [] with z
  rfl

/-- The first normalized gradient factors are analytic at each zero-radius base point. -/
lemma independentRadiusFirstGradient_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusFirstGradient (θ, 0) := by
  have ht := independentRadiusFirstResiduals_analyticAt θ
  have hg := independentRadiusFirstGradientResiduals_analyticAt θ
  have hm := independentRadiusFirstMetricTriple_analyticAt θ
  have hm0 := independentRadiusFirstMetricTriple_zero θ
  have hlow := analyticAt_low_of_analyticAt_metric hm hm0
  have hden := analyticAt_lowDenom_of_analyticAt_metric hm hm0
  have hden0 : RealSymmetric2.lowDenom
      (independentRadiusFirstMetricTriple (θ, 0)).1
      (independentRadiusFirstMetricTriple (θ, 0)).2.1
      (independentRadiusFirstMetricTriple (θ, 0)).2.2 ≠ 0 := by
    rw [hm0]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom]
  have hd : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstResiduals z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp ht)
  have hb : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstResiduals z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp ht)
  have hq : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstGradientResiduals z).1) (θ, 0) :=
    analyticAt_fst.comp hg
  have hu : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstGradientResiduals z).2) (θ, 0) :=
    analyticAt_snd.comp hg
  have hlow' : AnalyticAt ℝ (fun z ↦ RealSymmetric2.low
      (independentRadiusFirstMetricTriple z).1
      (independentRadiusFirstMetricTriple z).2.1
      (independentRadiusFirstMetricTriple z).2.2) (θ, 0) := hlow
  have hden' : AnalyticAt ℝ (fun z ↦ RealSymmetric2.lowDenom
      (independentRadiusFirstMetricTriple z).1
      (independentRadiusFirstMetricTriple z).2.1
      (independentRadiusFirstMetricTriple z).2.2) (θ, 0) := hden
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  have hfirst : AnalyticAt ℝ (fun z ↦
      ((independentRadiusFirstResiduals z).2.2 -
        RealSymmetric2.low (independentRadiusFirstMetricTriple z).1
          (independentRadiusFirstMetricTriple z).2.1
          (independentRadiusFirstMetricTriple z).2.2) *
        (independentRadiusFirstGradientResiduals z).1 -
        z.2 ^ 2 * (independentRadiusFirstResiduals z).2.1 *
          (independentRadiusFirstGradientResiduals z).2) (θ, 0) := by
    exact ((hd.sub hlow').mul hq).sub (((hr.pow 2).mul hb).mul hu)
  have hsecond : AnalyticAt ℝ (fun z ↦
      (independentRadiusFirstResiduals z).2.1 *
          (independentRadiusFirstGradientResiduals z).1 +
        ((independentRadiusFirstResiduals z).2.2 -
          RealSymmetric2.low (independentRadiusFirstMetricTriple z).1
            (independentRadiusFirstMetricTriple z).2.1
            (independentRadiusFirstMetricTriple z).2.2) *
          (independentRadiusFirstGradientResiduals z).2) (θ, 0) := by
    exact (hb.mul hq).add ((hd.sub hlow').mul hu)
  have hpair := (hfirst.div hden' hden0).prod (hsecond.div hden' hden0)
  unfold independentRadiusFirstGradient
  dsimp
  apply hpair.congr
  filter_upwards [] with z
  rfl

/-- The first normalized spectral factors are analytic at each zero-radius base point. -/
lemma independentRadiusFirstSpectral_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusFirstSpectral (θ, 0) := by
  have ht := independentRadiusFirstResiduals_analyticAt θ
  have hm := independentRadiusFirstMetricTriple_analyticAt θ
  have hm0 := independentRadiusFirstMetricTriple_zero θ
  have hhigh := analyticAt_high_of_analyticAt_metric hm hm0
  have hhigh0 : RealSymmetric2.high
      (independentRadiusFirstMetricTriple (θ, 0)).1
      (independentRadiusFirstMetricTriple (θ, 0)).2.1
      (independentRadiusFirstMetricTriple (θ, 0)).2.2 ≠ 0 := by
    rw [hm0]
    norm_num [RealSymmetric2.high, RealSymmetric2.gap]
  have ha : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstResiduals z).1) (θ, 0) :=
    analyticAt_fst.comp ht
  have hb : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstResiduals z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp ht)
  have hd : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstResiduals z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp ht)
  have hdet := ((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh0
  have hpair := hdet.prod hhigh
  unfold independentRadiusFirstSpectral
  dsimp
  apply hpair.congr
  filter_upwards [] with z
  rfl

/-- The second-leg residual triple is analytic at each zero-radius base point. -/
lemma independentRadiusSecondResiduals_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (fun z ↦ independentSecondResiduals z.1.1 z.2
      (independentRadiusFirstSpectral z).1
      (independentRadiusFirstSpectral z).2
      (independentRadiusFirstGradient z).1
      (independentRadiusFirstGradient z).2) (θ, 0) := by
  have hb : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp analyticAt_fst
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  have hs := independentRadiusFirstSpectral_analyticAt θ
  have hg := independentRadiusFirstGradient_analyticAt θ
  have hL : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hs
  have hH : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstSpectral z).2) (θ, 0) :=
    analyticAt_snd.comp hs
  have hQ : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstGradient z).1) (θ, 0) :=
    analyticAt_fst.comp hg
  have hU : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstGradient z).2) (θ, 0) :=
    analyticAt_snd.comp hg
  let w₁ : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 -
      2 * z.1.1 * (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2
  let w₂ : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 -
      2 * z.1.1 * z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1
  have hw₁ : AnalyticAt ℝ w₁ (θ, 0) := by
    dsimp [w₁]
    exact (hr.mul hL).mul hQ |>.sub (((analyticAt_const.mul hb).mul hH).mul hU)
  have hw₂ : AnalyticAt ℝ w₂ (θ, 0) := by
    dsimp [w₂]
    exact (hH.mul hU).sub ((((analyticAt_const.mul hb).mul hr).mul hL).mul hQ)
  let β : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 * w₁ z +
      (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 * w₂ z
  let γ : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    z.2 ^ 2 * (independentRadiusFirstSpectral z).1 * (w₁ z) ^ 2 +
      (independentRadiusFirstSpectral z).2 * (w₂ z) ^ 2
  have hβ : AnalyticAt ℝ β (θ, 0) := by
    dsimp [β]
    exact (((hr.mul hL).mul hQ).mul hw₁).add (((hH.mul hU).mul hw₂))
  have hγ : AnalyticAt ℝ γ (θ, 0) := by
    dsimp [γ]
    exact (((hr.pow 2).mul hL).mul (hw₁.pow 2)).add (hH.mul (hw₂.pow 2))
  have hβ0 : β (θ, 0) ≠ 0 := by
    dsimp [β, w₁, w₂]
    simp only [independentRadiusFirstSpectral_zero θ, independentRadiusFirstGradient_zero θ]
    norm_num
  have hγ0 : γ (θ, 0) ≠ 0 := by
    dsimp [γ, w₁, w₂]
    simp only [independentRadiusFirstSpectral_zero θ, independentRadiusFirstGradient_zero θ]
    norm_num
  let a : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstSpectral z).1 -
        z.2 ^ 2 * (independentRadiusFirstSpectral z).1 ^ 2 * (w₁ z) ^ 2 / γ z +
      (independentRadiusFirstSpectral z).1 ^ 2 *
        (independentRadiusFirstGradient z).1 ^ 2 / β z
  let c : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    -z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstSpectral z).2 * w₁ z * w₂ z / γ z +
      (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 *
        (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 / β z
  let d : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstSpectral z).2 -
        (independentRadiusFirstSpectral z).2 ^ 2 * (w₂ z) ^ 2 / γ z +
      (independentRadiusFirstSpectral z).2 ^ 2 *
        (independentRadiusFirstGradient z).2 ^ 2 / β z
  have ha : AnalyticAt ℝ a (θ, 0) := by
    dsimp [a]
    exact (hL.sub ((((hr.pow 2).mul (hL.pow 2)).mul (hw₁.pow 2)).div hγ hγ0)).add
      (((hL.pow 2).mul (hQ.pow 2)).div hβ hβ0)
  have hc : AnalyticAt ℝ c (θ, 0) := by
    dsimp [c]
    have hneg : AnalyticAt ℝ (fun z ↦ -z.2 *
        (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstSpectral z).2 * w₁ z * w₂ z) (θ, 0) := by
      apply ((((hr.mul hL).mul hH).mul hw₁).neg.mul hw₂).congr
      filter_upwards [] with z
      simp only [Pi.mul_apply, Pi.neg_apply]
      ring
    exact (hneg.div hγ hγ0).add
      (((hL.mul hQ).mul hH).mul hU |>.div hβ hβ0)
  have hd : AnalyticAt ℝ d (θ, 0) := by
    dsimp [d]
    exact (hH.sub ((hH.pow 2).mul (hw₂.pow 2) |>.div hγ hγ0)).add
      ((hH.pow 2).mul (hU.pow 2) |>.div hβ hβ0)
  have htriple := ha.prod (hc.prod hd)
  unfold independentSecondResiduals
  dsimp
  apply htriple.congr
  filter_upwards [] with z
  simp [a, c, d, β, γ, w₁, w₂]

/-- The second-leg gradient residual pair is analytic at each zero-radius base point. -/
lemma independentRadiusSecondGradientResiduals_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (fun z ↦ independentSecondGradientResiduals z.1.1 z.2
      (independentRadiusFirstSpectral z).1
      (independentRadiusFirstSpectral z).2
      (independentRadiusFirstGradient z).1
      (independentRadiusFirstGradient z).2) (θ, 0) := by
  have hb : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp analyticAt_fst
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  have hs := independentRadiusFirstSpectral_analyticAt θ
  have hg := independentRadiusFirstGradient_analyticAt θ
  have hL : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hs
  have hH : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstSpectral z).2) (θ, 0) :=
    analyticAt_snd.comp hs
  have hQ : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstGradient z).1) (θ, 0) :=
    analyticAt_fst.comp hg
  have hU : AnalyticAt ℝ (fun z ↦ (independentRadiusFirstGradient z).2) (θ, 0) :=
    analyticAt_snd.comp hg
  let w₁ : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 -
      2 * z.1.1 * (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2
  let w₂ : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 -
      2 * z.1.1 * z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1
  have hw₁ : AnalyticAt ℝ w₁ (θ, 0) := by
    dsimp [w₁]
    exact (hr.mul hL).mul hQ |>.sub (((analyticAt_const.mul hb).mul hH).mul hU)
  have hw₂ : AnalyticAt ℝ w₂ (θ, 0) := by
    dsimp [w₂]
    exact (hH.mul hU).sub ((((analyticAt_const.mul hb).mul hr).mul hL).mul hQ)
  let β : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 * w₁ z +
      (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 * w₂ z
  have hβ : AnalyticAt ℝ β (θ, 0) := by
    dsimp [β]
    exact (((hr.mul hL).mul hQ).mul hw₁).add ((hH.mul hU).mul hw₂)
  have hβ0 : β (θ, 0) ≠ 0 := by
    dsimp [β, w₁, w₂]
    rw [independentRadiusFirstSpectral_zero, independentRadiusFirstGradient_zero]
    norm_num
  let δ : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 ^ 2 +
      (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 ^ 2
  have hδ : AnalyticAt ℝ δ (θ, 0) := by
    dsimp [δ]
    exact (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
  let q : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstGradient z).1 - z.2 * δ z * w₁ z / (3 * β z)
  let u : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (independentRadiusFirstGradient z).2 - δ z * w₂ z / (3 * β z)
  have hthree : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (3 : ℝ) * β z) (θ, 0) :=
    analyticAt_const.mul hβ
  have hthree0 : (3 : ℝ) * β (θ, 0) ≠ 0 := by
    have hthree : (3 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero hthree hβ0
  have hq : AnalyticAt ℝ q (θ, 0) := by
    dsimp [q]
    exact hQ.sub (((hr.mul hδ).mul hw₁).div hthree hthree0)
  have hu : AnalyticAt ℝ u (θ, 0) := by
    dsimp [u]
    exact hU.sub ((hδ.mul hw₂).div hthree hthree0)
  have hpair := hq.prod hu
  unfold independentSecondGradientResiduals
  dsimp
  apply hpair.congr
  filter_upwards [] with z
  simp [q, u, δ, β, w₁, w₂]

/-- The second-leg residual triple has its reference value at zero radius. -/
lemma independentRadiusSecondResiduals_zero (θ : ℝ × ℝ × ℝ) :
    independentSecondResiduals  θ.1 0 2 1 1 1 = (6, 2, 1) := by
  unfold independentSecondResiduals
  dsimp
  norm_num

/-- The second-leg gradient residual pair has its reference value at zero radius. -/
lemma independentRadiusSecondGradientResiduals_zero (θ : ℝ × ℝ × ℝ) :
    independentSecondGradientResiduals θ.1 0 2 1 1 1 = (1, 0) := by
  norm_num [independentSecondGradientResiduals, independentSecondResiduals]

/-- The normalized second-leg metric triple is analytic at each zero-radius base point. -/
lemma independentRadiusSecondMetric_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (fun z ↦
      (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1,
       z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1,
       (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2)) (θ, 0) := by
  have ht := independentRadiusSecondResiduals_analyticAt θ
  have ha := analyticAt_fst.comp ht
  have hb := analyticAt_fst.comp (analyticAt_snd.comp ht)
  have hd := analyticAt_snd.comp (analyticAt_snd.comp ht)
  have h := ((analyticAt_snd.pow 2).mul ha).prod
    ((analyticAt_snd.mul hb).prod hd)
  apply h.congr
  filter_upwards [] with z
  rfl

/-- The normalized second-leg metric triple has the diagonal base value at zero radius. -/
lemma independentRadiusSecondMetric_zero (θ : ℝ × ℝ × ℝ) :
    (0 ^ 2 * (independentSecondResiduals θ.1 0 2 1 1 1).1,
      0 * (independentSecondResiduals θ.1 0 2 1 1 1).2.1,
      (independentSecondResiduals θ.1 0 2 1 1 1).2.2) = (0, 0, 1) := by
  rw [independentRadiusSecondResiduals_zero]
  norm_num

/-- The second normalized spectral factors are analytic at each zero-radius base point. -/
lemma independentRadiusSecondSpectral_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusSecondSpectral (θ, 0) := by
  have ht := independentRadiusSecondResiduals_analyticAt θ
  have hm := independentRadiusSecondMetric_analyticAt θ
  have hm0 : (fun z ↦
      (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1,
       z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1,
       (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2)) (θ, 0) = (0, 0, 1) := by
    simp only [independentRadiusFirstSpectral_zero θ, independentRadiusFirstGradient_zero θ]
    simp [independentRadiusSecondResiduals_zero]
  have hhigh := analyticAt_high_of_analyticAt_metric hm hm0
  have hhigh0 : RealSymmetric2.high
      ((fun z ↦ z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1) (θ, 0))
      ((fun z ↦ z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1) (θ, 0))
      ((fun z ↦ (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2) (θ, 0)) ≠ 0 := by
    norm_num [independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ, independentSecondResiduals,
      RealSymmetric2.high, RealSymmetric2.gap]
  have ha := analyticAt_fst.comp ht
  have hb := analyticAt_fst.comp (analyticAt_snd.comp ht)
  have hd := analyticAt_snd.comp (analyticAt_snd.comp ht)
  have hdet := ((ha.mul hd).sub (hb.pow 2)).div hhigh hhigh0
  have hpair := hdet.prod hhigh
  unfold independentRadiusSecondSpectral
  dsimp
  apply hpair.congr
  filter_upwards [] with z
  rfl

/-- The second normalized gradient factors are analytic at each zero-radius base point. -/
lemma independentRadiusSecondGradient_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusSecondGradient (θ, 0) := by
  have ht := independentRadiusSecondResiduals_analyticAt θ
  have hg := independentRadiusSecondGradientResiduals_analyticAt θ
  have hm := independentRadiusSecondMetric_analyticAt θ
  have hm0 : (fun z ↦
      (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1,
       z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1,
       (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2)) (θ, 0) = (0, 0, 1) := by
    simp only [independentRadiusFirstSpectral_zero θ, independentRadiusFirstGradient_zero θ]
    simp [independentRadiusSecondResiduals_zero]
  have hlow := analyticAt_low_of_analyticAt_metric hm hm0
  have hden := analyticAt_lowDenom_of_analyticAt_metric hm hm0
  have hden0 : RealSymmetric2.lowDenom 0 0 1 ≠ 0 := by
    norm_num [RealSymmetric2.low, RealSymmetric2.gap, RealSymmetric2.lowDenom]
  have hL : AnalyticAt ℝ (fun z ↦
      (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp ht)
  have hD : AnalyticAt ℝ (fun z ↦
      (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp ht)
  have hQ : AnalyticAt ℝ (fun z ↦
      (independentSecondGradientResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1) (θ, 0) :=
    analyticAt_fst.comp hg
  have hU : AnalyticAt ℝ (fun z ↦
      (independentSecondGradientResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2) (θ, 0) :=
    analyticAt_snd.comp hg
  have hlow' : AnalyticAt ℝ (fun z ↦ RealSymmetric2.low
      ((fun z ↦ z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1) z)
      ((fun z ↦ z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1) z)
      ((fun z ↦ (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2) z)) (θ, 0) := hlow
  have hden' : AnalyticAt ℝ (fun z ↦ RealSymmetric2.lowDenom
      ((fun z ↦ z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1) z)
      ((fun z ↦ z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1) z)
      ((fun z ↦ (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2) z)) (θ, 0) := hden
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  have hfirst : AnalyticAt ℝ (fun z ↦
      ((independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2 -
        RealSymmetric2.low
          (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
            (independentRadiusFirstSpectral z).1
            (independentRadiusFirstSpectral z).2
            (independentRadiusFirstGradient z).1
            (independentRadiusFirstGradient z).2).1)
          (z.2 * (independentSecondResiduals z.1.1 z.2
            (independentRadiusFirstSpectral z).1
            (independentRadiusFirstSpectral z).2
            (independentRadiusFirstGradient z).1
            (independentRadiusFirstGradient z).2).2.1)
          ((independentSecondResiduals z.1.1 z.2
            (independentRadiusFirstSpectral z).1
            (independentRadiusFirstSpectral z).2
            (independentRadiusFirstGradient z).1
            (independentRadiusFirstGradient z).2).2.2)) *
        (independentSecondGradientResiduals z.1.1 z.2
          (independentRadiusFirstSpectral z).1
          (independentRadiusFirstSpectral z).2
          (independentRadiusFirstGradient z).1
          (independentRadiusFirstGradient z).2).1 -
      z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1 *
        (independentSecondGradientResiduals z.1.1 z.2
          (independentRadiusFirstSpectral z).1
          (independentRadiusFirstSpectral z).2
          (independentRadiusFirstGradient z).1
          (independentRadiusFirstGradient z).2).2) (θ, 0) := by
    exact ((hD.sub hlow').mul hQ).sub (((hr.pow 2).mul hL).mul hU)
  have hsecond : AnalyticAt ℝ (fun z ↦
      (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1 *
        (independentSecondGradientResiduals z.1.1 z.2
          (independentRadiusFirstSpectral z).1
          (independentRadiusFirstSpectral z).2
          (independentRadiusFirstGradient z).1
          (independentRadiusFirstGradient z).2).1 +
      ((independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2 -
        RealSymmetric2.low
          (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
            (independentRadiusFirstSpectral z).1
            (independentRadiusFirstSpectral z).2
            (independentRadiusFirstGradient z).1
            (independentRadiusFirstGradient z).2).1)
          (z.2 * (independentSecondResiduals z.1.1 z.2
            (independentRadiusFirstSpectral z).1
            (independentRadiusFirstSpectral z).2
            (independentRadiusFirstGradient z).1
            (independentRadiusFirstGradient z).2).2.1)
          ((independentSecondResiduals z.1.1 z.2
            (independentRadiusFirstSpectral z).1
            (independentRadiusFirstSpectral z).2
            (independentRadiusFirstGradient z).1
            (independentRadiusFirstGradient z).2).2.2)) *
        (independentSecondGradientResiduals z.1.1 z.2
          (independentRadiusFirstSpectral z).1
          (independentRadiusFirstSpectral z).2
          (independentRadiusFirstGradient z).1
          (independentRadiusFirstGradient z).2).2) (θ, 0) := by
    exact hL.mul hQ |>.add ((hD.sub hlow').mul hU)
  have hden0' : RealSymmetric2.lowDenom
      ((fun z ↦ z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1) (θ, 0))
      ((fun z ↦ z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1) (θ, 0))
      ((fun z ↦ (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2) (θ, 0)) ≠ 0 := by
    simp only [independentRadiusFirstSpectral_zero θ, independentRadiusFirstGradient_zero θ]
    simp [independentRadiusSecondResiduals_zero, RealSymmetric2.lowDenom,
      RealSymmetric2.low, RealSymmetric2.gap]
  have hpair := (hfirst.div hden' hden0').prod (hsecond.div hden' hden0')
  unfold independentRadiusSecondGradient
  dsimp
  apply hpair.congr
  filter_upwards [] with z
  rfl

/-- The independent-radius normal form is smooth to every finite order at each base radius. -/
lemma independentRadiusNormalForm_contDiffAt (m : ℕ) (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ m (Function.uncurry independentRadiusNormalForm) (θ, 0) := by
  -- First package the two analytic factor pairs through the canonical quotient interface.
  have hS := independentRadiusSecondSpectral_analyticAt θ
  have hG := independentRadiusSecondGradient_analyticAt θ
  have hS0 := independentRadiusSecondSpectral_zero θ
  have hG0 := independentRadiusSecondGradient_zero θ
  have hRadius :
      (independentRadiusSecondSpectral (θ, 0)).2 *
          (independentRadiusSecondGradient (θ, 0)).2 ≠ 0 := by
    rw [hS0, hG0]
    norm_num
  have hShape :
      (independentRadiusSecondSpectral (θ, 0)).1 *
          (independentRadiusSecondGradient (θ, 0)).1 ^ 2 ≠ 0 := by
    rw [hS0, hG0]
    norm_num
  have hrec' := AnalyticRecovery.analyticAt_recoveryFactors
    hS hG hRadius hShape
  have hrec : AnalyticAt ℝ independentRadiusRecoveryFactors (θ, 0) := by
    have hEq : independentRadiusRecoveryFactors =
        AnalyticRecovery.recoveryFactors independentRadiusSecondSpectral
          independentRadiusSecondGradient := by
      funext z
      rfl
    rw [hEq]
    exact hrec'
  -- Multiply the recovered radius factor by the independent radius coordinate;
  -- the resulting analytic triple is definitionally the normal form.
  have hr : AnalyticAt ℝ (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) :=
    analyticAt_snd
  have hρ : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        z.2 * (independentRadiusRecoveryFactors z).1) (θ, 0) := by
    exact hr.mul (analyticAt_fst.comp hrec)
  have hp : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusRecoveryFactors z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hrec)
  have hhigh : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusRecoveryFactors z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hrec)
  have htriple := hρ.prod (hp.prod hhigh)
  have hEq : (Function.uncurry independentRadiusNormalForm) =
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (z.2 * (independentRadiusRecoveryFactors z).1,
          (independentRadiusRecoveryFactors z).2.1,
          (independentRadiusRecoveryFactors z).2.2)) := by
    funext z
    exact independentRadiusNormalForm_eq_recoveryFactors z.1 z.2
  rw [hEq]
  exact htriple.contDiffAt

end DFP.TwoLeg.Mixed
