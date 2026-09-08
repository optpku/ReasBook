module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableMapCenterInterface
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableMapCenterInterface
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoLeg.Mixed

/-!
This companion exposes the raw two-leg evaluator through a small certificate.  The
certificate contains only the source-specific frame and displacement facts; the
projection and residual transport are reusable algebraic interfaces.
-/

namespace CenterRaw

/-- Helper for Infrastructure I.16a: the initial metric used by the raw center evaluator. -/
def initialMetric (state : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![state.2.2 * state.2.1 * state.1 ^ 2, state.2.2]

/-- Helper for Infrastructure I.16a: the initial raw gradient used by the center evaluator. -/
def initialGradient (state : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  ![(1 : ℝ), state.2.1 * state.1]

/-- Helper for Infrastructure I.16a: the first raw DFP step of the center evaluator. -/
def firstStep (b : ℝ) (state : ℝ × ℝ × ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  rawObservableStep (initialMetric state) (initialGradient state)
    (TwoPhaseControls.first b)

/-- Helper for Infrastructure I.16a: the oriented frame selected after the first raw step. -/
def firstFrame (b : ℝ) (state : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let step := firstStep b state
  OrientedEigenframe.frame (step.1 0 0) (step.1 0 1) (step.1 1 1)
    (WithLp.toLp 2 step.2.1)

/-- Helper for Infrastructure I.16a: the second metric after transporting the first raw step. -/
def secondMetric (b : ℝ) (state : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (firstFrame b state).transpose * (firstStep b state).1 * firstFrame b state

/-- Helper for Infrastructure I.16a: the second gradient in the first-step frame. -/
def secondGradient (b : ℝ) (state : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  (firstFrame b state).transpose *ᵥ (firstStep b state).2.1

/-- Helper for Infrastructure I.16a: the second raw DFP step of the center evaluator. -/
def secondStep (b : ℝ) (state : ℝ × ℝ × ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  rawObservableStep (secondMetric b state) (secondGradient b state)
    (TwoPhaseControls.second b)

/-- Infrastructure I.16a: the first normalized displacement vector in the raw chart. -/
def firstNormalizedDisplacement (b r p : ℝ) : Fin 2 → ℝ :=
  (-(2 / 3 : ℝ) * (p + 1) /
      (1 + 2 * b * r + r ^ 2)) • ![r, 1]

/-- Infrastructure I.16a: the second normalized displacement vector in the raw chart. -/
def secondNormalizedDisplacement (b r L H Q U : ℝ) : Fin 2 → ℝ :=
  let β := r * L * Q * (r * L * Q - 2 * b * H * U) +
    H * U * (H * U - 2 * b * r * L * Q)
  (-(1 / 3 : ℝ) * (L * Q ^ 2 + H * U ^ 2) / β) •
    ![r * L * Q, H * U]

/-- Infrastructure I.16a: on the punctured first raw chart, the first displacement
has the radius-scaled normalized direction used by the center bracket. -/
theorem firstDisplacement_eq_radius_smul
    (b r p h G : ℝ)
    (hden : h ^ 2 * p ^ 2 * G ^ 2 * r ^ 2 *
      (1 + 2 * b * r + r ^ 2) ≠ 0) :
    (rawObservableStep
      (Matrix.diagonal ![h * p * r ^ 2, h])
    (G • ![(1 : ℝ), p * r])
      (TwoPhaseControls.first b)).2.2 =
      G • (r • firstNormalizedDisplacement b r p) := by
  have hh : h ≠ 0 := by
    intro hh
    apply hden
    simp [hh]
  have hp : p ≠ 0 := by
    intro hp
    apply hden
    simp [hp]
  have hG : G ≠ 0 := by
    intro hG
    apply hden
    simp [hG]
  have hr : r ≠ 0 := by
    intro hr
    apply hden
    simp [hr]
  have hB : 1 + 2 * b * r + r ^ 2 ≠ 0 :=
    right_ne_zero_of_mul hden
  unfold rawObservableStep
  dsimp
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      TwoPhaseControls.first_matrix, TwoPhaseControls.first_tau,
      firstNormalizedDisplacement]
    field_simp [hh, hp, hG, hr, hB]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      TwoPhaseControls.first_matrix, TwoPhaseControls.first_tau,
      firstNormalizedDisplacement]
    field_simp [hh, hp, hG, hr, hB]
    ring

/-- Infrastructure I.16a: on the punctured second raw chart, the second displacement
has the radius-scaled normalized direction determined by the incoming factors. -/
theorem secondDisplacement_eq_radius_smul
    (b r L H Q U G : ℝ)
    (hden : G ^ 2 * r ^ 2 *
      (r * L * Q * (r * L * Q - 2 * b * H * U) +
        H * U * (H * U - 2 * b * r * L * Q)) ≠ 0) :
    (rawObservableStep
      (Matrix.diagonal ![r ^ 2 * L, H])
    (G • ![Q, r * U])
      (TwoPhaseControls.second b)).2.2 =
      G • (r • secondNormalizedDisplacement b r L H Q U) := by
  have hG : G ≠ 0 := by
    intro hG
    apply hden
    simp [hG]
  have hr : r ≠ 0 := by
    intro hr
    apply hden
    simp [hr]
  let β : ℝ :=
    r * L * Q * (r * L * Q - 2 * b * H * U) +
      H * U * (H * U - 2 * b * r * L * Q)
  have houter : G ^ 2 * r ^ 2 * β ≠ 0 := by
    simpa only [β] using hden
  have hβ : β ≠ 0 := by
    intro hβ
    apply houter
    simp [hβ]
  have hthree : (3 : ℝ) ≠ 0 := by
    norm_num
  have hβ3 : 3 * β ≠ 0 := mul_ne_zero hthree hβ
  unfold rawObservableStep
  dsimp
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      TwoPhaseControls.second_matrix, TwoPhaseControls.second_tau,
      secondNormalizedDisplacement]
    field_simp [hG, hr, hβ, hβ3]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      TwoPhaseControls.second_matrix, TwoPhaseControls.second_tau,
      secondNormalizedDisplacement]
    field_simp [hG, hr, hβ, hβ3]
    ring

/-- Infrastructure I.16a: the first evaluator projection exposes the normalized
displacement used by a bracket certificate. -/
theorem firstStep_displacement_eq_radius_smul
    (b r p h : ℝ)
    (hden : h ^ 2 * p ^ 2 * r ^ 2 *
      (1 + 2 * b * r + r ^ 2) ≠ 0) :
    (firstStep b (r, p, h)).2.2 =
      r • firstNormalizedDisplacement b r p := by
  have hden' : h ^ 2 * p ^ 2 * (1 : ℝ) ^ 2 * r ^ 2 *
      (1 + 2 * b * r + r ^ 2) ≠ 0 := by
    simpa using hden
  have hraw := firstDisplacement_eq_radius_smul b r p h 1 hden'
  simpa [firstStep, initialMetric, initialGradient] using hraw

/-- Infrastructure I.16a: the second evaluator projection exposes the normalized
displacement after a diagonal metric/gradient specification. -/
theorem secondStep_displacement_eq_radius_smul
    (b r L H Q U G : ℝ) (state : ℝ × ℝ × ℝ)
    (hmetric : secondMetric b state = Matrix.diagonal ![r ^ 2 * L, H])
    (hgradient : secondGradient b state = G • ![Q, r * U])
    (hden : G ^ 2 * r ^ 2 *
      (r * L * Q * (r * L * Q - 2 * b * H * U) +
        H * U * (H * U - 2 * b * r * L * Q)) ≠ 0) :
    (secondStep b state).2.2 =
      G • (r • secondNormalizedDisplacement b r L H Q U) := by
  have hraw := secondDisplacement_eq_radius_smul b r L H Q U G hden
  simpa [secondStep, hmetric, hgradient, secondNormalizedDisplacement] using hraw

/-- Helper for Infrastructure I.16a: a source certificate for the frame and both normalized
raw displacements entering the center bracket. -/
structure BracketCertificate (b r : ℝ) (state : ℝ × ℝ × ℝ) where
  /-- Infrastructure I.16a: normalized first-leg displacement coordinates. -/
  firstNormalized : Fin 2 → ℝ
  /-- Infrastructure I.16a: normalized second-leg displacement coordinates. -/
  secondNormalized : Fin 2 → ℝ
  /-- Infrastructure I.16a: orthogonality of the intermediate raw frame. -/
  frame_orthogonal : firstFrame b state * (firstFrame b state).transpose = 1
  /-- Infrastructure I.16a: first raw displacement equals its signed radius scale. -/
  first_displacement : (firstStep b state).2.2 = r • firstNormalized
  /-- Infrastructure I.16a: second raw displacement equals its signed radius scale. -/
  second_displacement : (secondStep b state).2.2 = r • secondNormalized

/-- Helper for Infrastructure I.16a: the normalized center bracket carried by a raw-frame
certificate. -/
def BracketCertificate.bracket {b r : ℝ} {state : ℝ × ℝ × ℝ}
    (certificate : BracketCertificate b r state) : EuclideanSpace ℝ (Fin 2) :=
  weightedCenterBracket (firstFrame b state)
    certificate.firstNormalized certificate.secondNormalized

end CenterRaw

/-- Helper for Infrastructure I.16a: the linear-in-radius coefficient whose control-scaled
value is the prescribed quadratic center drift coefficient. -/
def centerBracketCoefficient (θ : ℝ × ℝ × ℝ) : ℝ :=
  -(2 * θ.1 * (6 * θ.2.2 - θ.2.1 + 96) / 9)

/-- Helper for Infrastructure I.16a: the scalar physical center residual is named once so
quotient and cubic-kernel interfaces can rewrite it without unfolding `observableMap`. -/
def physicalCenterResidual (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
    centerDriftCoefficient θ * r ^ 2

/-- Helper for Infrastructure I.16a: the prescribed center drift coefficient factors through
the control scale and the raw-frame bracket coefficient. -/
theorem centerDriftCoefficient_eq_control_mul_centerBracketCoefficient
    (θ : ℝ × ℝ × ℝ) :
    centerDriftCoefficient θ = θ.1 * centerBracketCoefficient θ := by
  unfold centerDriftCoefficient centerBracketCoefficient
  ring

/-- Helper for Infrastructure I.16a: a raw-frame certificate transports the full center
evaluator to the radius-scaled weighted bracket. -/
theorem CenterRaw.BracketCertificate.fullCenterDisplacement_coord_zero_eq_mul_bracket
    {b r : ℝ} {state : ℝ × ℝ × ℝ}
    (certificate : CenterRaw.BracketCertificate b r state) :
    (observableMap b state).fullCenterDisplacement 0 =
      (b * r) * certificate.bracket 0 := by
  let H₀ := CenterRaw.initialMetric state
  let g₀ := CenterRaw.initialGradient state
  let F := CenterRaw.firstFrame b state
  let H₁ := CenterRaw.secondMetric b state
  let firstStep := CenterRaw.firstStep b state
  let secondStep := CenterRaw.secondStep b state
  have hobs := observableMap_fullCenterDisplacement_coord_zero_eq_rawSteps b state
  have hfirst :
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.2 =
        r • certificate.firstNormalized := by
    simpa [CenterRaw.firstStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
      H₀, g₀, firstStep] using certificate.first_displacement
  have hsecond :
      (rawObservableStep H₁
        (F.transpose *ᵥ (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.1)
        (TwoPhaseControls.second b)).2.2 =
        r • certificate.secondNormalized := by
    simpa [CenterRaw.secondStep, CenterRaw.secondMetric, CenterRaw.secondGradient,
      CenterRaw.firstStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
      H₀, g₀, F, H₁, firstStep, secondStep] using certificate.second_displacement
  have hraw := rawObservableStep_centerDisplacement_coord_zero_eq_mul_scaledBracket
    b r F H₀ H₁ g₀ certificate.firstNormalized certificate.secondNormalized
    certificate.frame_orthogonal hfirst hsecond
  simpa [CenterRaw.BracketCertificate.bracket, CenterRaw.firstFrame,
    CenterRaw.secondMetric, CenterRaw.secondGradient, CenterRaw.firstStep,
    CenterRaw.secondStep, CenterRaw.initialMetric, CenterRaw.initialGradient,
    H₀, g₀, F, H₁, firstStep, secondStep] using hobs.trans hraw

/-- Helper for Infrastructure I.16a: the raw-frame center residual is a control-radius factor
times the bracket residual, with no division by the radius or scale. -/
theorem CenterRaw.BracketCertificate.centerResidual_eq_controlRadius_mul_bracketResidual
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (certificate : CenterRaw.BracketCertificate θ.1 r (input θ r)) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 =
      (θ.1 * r) *
        (certificate.bracket 0 - centerBracketCoefficient θ * r) := by
  rw [certificate.fullCenterDisplacement_coord_zero_eq_mul_bracket]
  rw [centerDriftCoefficient_eq_control_mul_centerBracketCoefficient]
  ring

/-- Helper for Infrastructure I.16a: a denominator-cleared raw bracket kernel gives the
cubic center residual, including the zero-radius and zero-scale branches. -/
theorem CenterRaw.BracketCertificate.centerResidual_eq_cubicKernel
    {θ : ℝ × ℝ × ℝ} {r K : ℝ}
    (certificate : CenterRaw.BracketCertificate θ.1 r (input θ r))
    (hkernel : certificate.bracket 0 - centerBracketCoefficient θ * r = r ^ 2 * K) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 =
      (θ.1 * r ^ 3) • K := by
  rw [certificate.centerResidual_eq_controlRadius_mul_bracketResidual, hkernel]
  simp only [smul_eq_mul]
  ring

/-- Infrastructure I.16a: a compact quadratic germ of raw-frame brackets and local
certificate witnesses imply the uniform zero-filled cubic quotient bound for the physical
center residual. -/
theorem centerResidual_zeroFilledQuotient_uniformBound_of_bracketGerm
    {K : Set (ℝ × ℝ × ℝ)}
    {W : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hK : IsCompact K)
    (hW : IndependentRadiusTruncatedGerm W K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hcertificate : ∀ θ ∈ K, ∀ r : ℝ, |r| < δ₀ →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 = W θ r) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤ C := by
  have htransport : ∀ θ ∈ K, ∀ r : ℝ, |r| < δ₀ →
      physicalCenterResidual θ r =
        θ.1 * r * (W θ r - centerBracketCoefficient θ * r) := by
    intro θ hθ r hr
    obtain ⟨certificate, hbracket⟩ := hcertificate θ hθ r hr
    have hres := certificate.centerResidual_eq_controlRadius_mul_bracketResidual
    rw [hbracket] at hres
    simpa only [physicalCenterResidual] using hres
  exact centerBracket_zeroFilledQuotient_uniformBound hK hW δ₀ hδ₀ htransport

end DFP.TwoLeg.Mixed
