module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterTelescopingAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-- Helper for Infrastructure I.16a: a raw observable step updates its gradient by the
control matrix applied to the recorded displacement. -/
theorem rawObservableStep_gradient_update
    (H : Matrix (Fin 2) (Fin 2) ℝ)
    (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    (rawObservableStep H g control).2.1 =
      g + control.matrix *ᵥ (rawObservableStep H g control).2.2 := by
  unfold rawObservableStep
  rfl

/-- Helper for Infrastructure I.16a: the first mixed control defect exchanges the two
coordinates and is linear in the signed control scale. -/
theorem firstControl_defect
    (b : ℝ) (s : Fin 2 → ℝ) :
    s - (TwoPhaseControls.first b).matrix *ᵥ s = ![-b * s 1, -b * s 0] := by
  rw [TwoPhaseControls.first_matrix]
  funext i
  fin_cases i
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]

/-- Helper for Infrastructure I.16a: the second mixed control defect has the same
coordinate exchange with the doubled signed control scale. -/
theorem secondControl_defect
    (b : ℝ) (s : Fin 2 → ℝ) :
    s - (TwoPhaseControls.second b).matrix *ᵥ s = ![2 * b * s 1, 2 * b * s 0] := by
  rw [TwoPhaseControls.second_matrix]
  funext i
  fin_cases i
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [dotProduct, Fin.sum_univ_two]

/-- Infrastructure I.16a: the two-leg center displacement splits into the defects of
the two control matrices after the intermediate orthogonal-frame transport. -/
theorem centerDisplacement_eq_weightedControls
    (F A₀ A₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ g₁ g₂ s₀ s₁ : Fin 2 → ℝ)
    (horth : F * F.transpose = 1)
    (hfirst : g₁ = g₀ + A₀ *ᵥ s₀)
    (hsecond : g₂ = F.transpose *ᵥ g₁ + A₁ *ᵥ s₁) :
    WithLp.toLp 2 s₀ + WithLp.toLp 2 (F *ᵥ s₁) -
        (WithLp.toLp 2 (F *ᵥ g₂) - WithLp.toLp 2 g₀) =
      WithLp.toLp 2 (s₀ - A₀ *ᵥ s₀) +
        WithLp.toLp 2 (F *ᵥ (s₁ - A₁ *ᵥ s₁)) := by
  have htransport : F *ᵥ g₂ =
      g₀ + A₀ *ᵥ s₀ + F *ᵥ (A₁ *ᵥ s₁) := by
    rw [hsecond, hfirst, Matrix.mulVec_add, Matrix.mulVec_mulVec, horth,
      Matrix.one_mulVec]
  rw [htransport]
  simp only [WithLp.toLp_add, WithLp.toLp_sub, Matrix.mulVec_sub]
  module

/-- Helper for Infrastructure I.16a: for the two mixed controls, the full center displacement
has an explicit factor of the signed scale. -/
theorem centerDisplacement_eq_controlScale_smul
    (b : ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ g₁ g₂ s₀ s₁ : Fin 2 → ℝ)
    (horth : F * F.transpose = 1)
    (hfirst : g₁ = g₀ + (TwoPhaseControls.first b).matrix *ᵥ s₀)
    (hsecond : g₂ = F.transpose *ᵥ g₁ +
      (TwoPhaseControls.second b).matrix *ᵥ s₁) :
    WithLp.toLp 2 s₀ + WithLp.toLp 2 (F *ᵥ s₁) -
        (WithLp.toLp 2 (F *ᵥ g₂) - WithLp.toLp 2 g₀) =
      b • (WithLp.toLp 2 ![-s₀ 1, -s₀ 0] +
        WithLp.toLp 2 (F *ᵥ ![2 * s₁ 1, 2 * s₁ 0])) := by
  have hweighted := centerDisplacement_eq_weightedControls F
    (TwoPhaseControls.first b).matrix (TwoPhaseControls.second b).matrix
    g₀ g₁ g₂ s₀ s₁ horth hfirst hsecond
  have hvec₀ : ![-b * s₀ 1, -b * s₀ 0] =
      b • ![-s₀ 1, -s₀ 0] := by
    funext i
    fin_cases i
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]
  have hvec₁ : ![2 * b * s₁ 1, 2 * b * s₁ 0] =
      b • ![2 * s₁ 1, 2 * s₁ 0] := by
    funext i
    fin_cases i
    · simp [smul_eq_mul]
      ring
    · simp [smul_eq_mul]
      ring
  rw [hweighted, firstControl_defect, secondControl_defect, hvec₀, hvec₁]
  simp only [Matrix.mulVec_smul, WithLp.toLp_smul, smul_add]

/-- Helper for Infrastructure I.16a: the public raw-step evaluator inherits the explicit
signed-scale factor once its second leg is formed in the transported first-leg frame. -/
theorem rawObservableStep_centerDisplacement_eq_controlScale_smul
    (b : ℝ) (F H₀ H₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (g₀ : Fin 2 → ℝ) (horth : F * F.transpose = 1) :
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first b)
    let g₁ := F.transpose *ᵥ firstStep.2.1
    let secondStep := rawObservableStep H₁ g₁ (TwoPhaseControls.second b)
    WithLp.toLp 2 firstStep.2.2 + WithLp.toLp 2 (F *ᵥ secondStep.2.2) -
        (WithLp.toLp 2 (F *ᵥ secondStep.2.1) - WithLp.toLp 2 g₀) =
      b • (WithLp.toLp 2 ![-firstStep.2.2 1, -firstStep.2.2 0] +
        WithLp.toLp 2 (F *ᵥ ![2 * secondStep.2.2 1, 2 * secondStep.2.2 0])) := by
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
  exact centerDisplacement_eq_controlScale_smul b F g₀ firstStep.2.1
    secondStep.2.1 firstStep.2.2 secondStep.2.2 horth hfirst hsecond

end DFP.TwoLeg.Mixed
