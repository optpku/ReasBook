module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterTelescoping

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-!
This companion turns the weighted two-leg telescope into a radius-scaled
center-bracket identity.  Source-specific frame and displacement certificates
remain hypotheses; the algebraic extraction of the mixed `b * r` factor is
proved here once.
-/

/-- Helper for Infrastructure I.16a: the normalized vector bracket made from the two
control defects and an intermediate frame. -/
def weightedCenterBracket
    (F : Matrix (Fin 2) (Fin 2) ℝ)
    (u₀ u₁ : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-u₀ 1, -u₀ 0] +
    WithLp.toLp 2 (F *ᵥ ![2 * u₁ 1, 2 * u₁ 0])

/-- Infrastructure I.16a: radius-scaled leg displacements expose the signed control
scale times the normalized center bracket. -/
theorem centerDisplacement_eq_scaledBracket
    (b r : ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ g₁ g₂ s₀ s₁ u₀ u₁ : Fin 2 → ℝ)
    (horth : F * F.transpose = 1)
    (hfirst : g₁ = g₀ + (TwoPhaseControls.first b).matrix *ᵥ s₀)
    (hsecond : g₂ = F.transpose *ᵥ g₁ +
      (TwoPhaseControls.second b).matrix *ᵥ s₁)
    (hs₀ : s₀ = r • u₀)
    (hs₁ : s₁ = r • u₁) :
    WithLp.toLp 2 s₀ + WithLp.toLp 2 (F *ᵥ s₁) -
        (WithLp.toLp 2 (F *ᵥ g₂) - WithLp.toLp 2 g₀) =
      (b * r) • weightedCenterBracket F u₀ u₁ := by
  have hcenter := centerDisplacement_eq_controlScale_smul b F g₀ g₁ g₂ s₀ s₁
    horth hfirst hsecond
  rw [hcenter, hs₀, hs₁]
  simp only [weightedCenterBracket, Pi.smul_apply, smul_eq_mul]
  have hvec₀ : ![-(r * u₀ 1), -(r * u₀ 0)] =
      r • ![-u₀ 1, -u₀ 0] := by
    funext i
    fin_cases i
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]
  have hvec₁ : ![2 * (r * u₁ 1), 2 * (r * u₁ 0)] =
      r • ![2 * u₁ 1, 2 * u₁ 0] := by
    funext i
    fin_cases i
    · simp [smul_eq_mul]
      ring
    · simp [smul_eq_mul]
      ring
  have hmul : F *ᵥ ![2 * (r * u₁ 1), 2 * (r * u₁ 0)] =
      r • (F *ᵥ ![2 * u₁ 1, 2 * u₁ 0]) := by
    rw [hvec₁, Matrix.mulVec_smul]
  have htoLp : WithLp.toLp 2 (F *ᵥ ![2 * (r * u₁ 1), 2 * (r * u₁ 0)]) =
      r • WithLp.toLp 2 (F *ᵥ ![2 * u₁ 1, 2 * u₁ 0]) := by
    rw [hmul, WithLp.toLp_smul]
  have htoLp₀ : WithLp.toLp 2 (r • ![-u₀ 1, -u₀ 0]) =
      r • WithLp.toLp 2 ![-u₀ 1, -u₀ 0] := by
    rw [WithLp.toLp_smul]
  rw [hvec₀, htoLp₀, htoLp]
  simp only [smul_add, smul_smul]

/-- Helper for Infrastructure I.16a: the public raw-step evaluator inherits the radius-scaled
center-bracket identity from two displacement scaling certificates. -/
theorem rawObservableStep_centerDisplacement_eq_scaledBracket
    (b r : ℝ) (F H₀ H₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ u₀ u₁ : Fin 2 → ℝ) (horth : F * F.transpose = 1)
    (hs₀ : (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.2 = r • u₀)
    (hs₁ : (rawObservableStep H₁
      (F.transpose *ᵥ (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.1)
      (TwoPhaseControls.second b)).2.2 = r • u₁) :
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first b)
    let g₁ := F.transpose *ᵥ firstStep.2.1
    let secondStep := rawObservableStep H₁ g₁ (TwoPhaseControls.second b)
    WithLp.toLp 2 firstStep.2.2 + WithLp.toLp 2 (F *ᵥ secondStep.2.2) -
        (WithLp.toLp 2 (F *ᵥ secondStep.2.1) - WithLp.toLp 2 g₀) =
      (b * r) • weightedCenterBracket F u₀ u₁ := by
  let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first b)
  let g₁ := F.transpose *ᵥ firstStep.2.1
  let secondStep := rawObservableStep H₁ g₁ (TwoPhaseControls.second b)
  have hfirstRaw := rawObservableStep_gradient_update H₀ g₀
    (TwoPhaseControls.first b)
  have hsecondRaw := rawObservableStep_gradient_update H₁ g₁
    (TwoPhaseControls.second b)
  have hfirst : firstStep.2.1 = g₀ +
      (TwoPhaseControls.first b).matrix *ᵥ firstStep.2.2 := by
    simpa [firstStep] using hfirstRaw
  have hsecond : secondStep.2.1 = F.transpose *ᵥ firstStep.2.1 +
      (TwoPhaseControls.second b).matrix *ᵥ secondStep.2.2 := by
    simpa [secondStep, g₁, firstStep] using hsecondRaw
  have hs₀' : firstStep.2.2 = r • u₀ := by
    simpa [firstStep] using hs₀
  have hs₁' : secondStep.2.2 = r • u₁ := by
    simpa [secondStep, g₁, firstStep] using hs₁
  exact centerDisplacement_eq_scaledBracket b r F g₀ firstStep.2.1
    secondStep.2.1 firstStep.2.2 secondStep.2.2 u₀ u₁ horth hfirst hsecond hs₀' hs₁'

/-- Helper for Infrastructure I.16a: taking the first Euclidean coordinate preserves the
radius-scaled center-bracket identity. -/
theorem rawObservableStep_centerDisplacement_coord_zero_eq_scaledBracket
    (b r : ℝ) (F H₀ H₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ u₀ u₁ : Fin 2 → ℝ) (horth : F * F.transpose = 1)
    (hs₀ : (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.2 = r • u₀)
    (hs₁ : (rawObservableStep H₁
      (F.transpose *ᵥ (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.1)
      (TwoPhaseControls.second b)).2.2 = r • u₁) :
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first b)
    let g₁ := F.transpose *ᵥ firstStep.2.1
    let secondStep := rawObservableStep H₁ g₁ (TwoPhaseControls.second b)
    (WithLp.toLp 2 firstStep.2.2 + WithLp.toLp 2 (F *ᵥ secondStep.2.2) -
        (WithLp.toLp 2 (F *ᵥ secondStep.2.1) - WithLp.toLp 2 g₀)) 0 =
      ((b * r) • weightedCenterBracket F u₀ u₁) 0 := by
  have hvector := rawObservableStep_centerDisplacement_eq_scaledBracket b r F H₀ H₁
    g₀ u₀ u₁ horth hs₀ hs₁
  exact congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hvector

/-- Helper for Infrastructure I.16a: the first-coordinate projection of the scaled center
bracket is scalar multiplication by `b * r` on the projected bracket. -/
theorem rawObservableStep_centerDisplacement_coord_zero_eq_mul_scaledBracket
    (b r : ℝ) (F H₀ H₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ u₀ u₁ : Fin 2 → ℝ) (horth : F * F.transpose = 1)
    (hs₀ : (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.2 = r • u₀)
    (hs₁ : (rawObservableStep H₁
      (F.transpose *ᵥ (rawObservableStep H₀ g₀ (TwoPhaseControls.first b)).2.1)
      (TwoPhaseControls.second b)).2.2 = r • u₁) :
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first b)
    let g₁ := F.transpose *ᵥ firstStep.2.1
    let secondStep := rawObservableStep H₁ g₁ (TwoPhaseControls.second b)
    (WithLp.toLp 2 firstStep.2.2 + WithLp.toLp 2 (F *ᵥ secondStep.2.2) -
        (WithLp.toLp 2 (F *ᵥ secondStep.2.1) - WithLp.toLp 2 g₀)) 0 =
      (b * r) * (weightedCenterBracket F u₀ u₁) 0 := by
  have hvector := rawObservableStep_centerDisplacement_coord_zero_eq_scaledBracket
    b r F H₀ H₁ g₀ u₀ u₁ horth hs₀ hs₁
  have hscalar : ((b * r) • weightedCenterBracket F u₀ u₁) 0 =
      (b * r) * (weightedCenterBracket F u₀ u₁) 0 := by
    rfl
  exact hvector.trans hscalar

end DFP.TwoLeg.Mixed
