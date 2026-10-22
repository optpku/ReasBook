/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace TikhonovPredictiveRisk

/-- The nonsaturated bias coefficient `C₁` from the predictive-risk asymptotic
formula `(7.86)`, written using the kernel moment `I_{p,3}^{p - q}`. -/
@[expose]
def predictiveRiskC1 (b c p q : ℝ) : ℝ :=
  b * c ^ (-(q - 1) / p) * KernelMoment.integral p 3 (p - q)

/-- The variance coefficient `C₂` from `(7.86)`, written using the kernel
moment `I_{p,3}^p`. -/
@[expose]
def predictiveRiskC2 (c p : ℝ) : ℝ :=
  c ^ (1 / p) * KernelMoment.integral p 3 p

/-- The concrete `α`-indexed predictive-risk objective from `(7.86)` in the
nonsaturated regime. -/
@[expose]
def objective (b c p q σ : ℝ) : ℕ → ℝ → ℝ :=
  fun n α ↦
    predictiveRiskC1 b c p q * α ^ ((q - 1) / p) +
      predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * α ^ (-(1 / p))

/-- The source-condition predictive-risk objective where the bias term is
written using the source norm term `‖f_true‖_{K*}^2`. -/
@[expose]
def sourceConditionObjective (sourceNormSq c p σ : ℝ) : ℕ → ℝ → ℝ :=
  fun n α ↦
    sourceNormSq * α +
      predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * α ^ (-(1 / p))

/-- The explicit positive constant multiplying `((σ ^ 2) / n) ^ (p / q)` in the
root-equation benchmark `β_pred`. -/
@[expose]
def betaPredConstant (b c p q : ℝ) : ℝ :=
  (predictiveRiskC2 c p / ((q - 1) * predictiveRiskC1 b c p q)) ^ (p / q)

/-- The root-equation benchmark sequence `β_pred` for the predictive-risk
minimizer in Theorem 7.23. -/
@[expose]
def betaPred (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ betaPredConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / q))

/-- The displayed root equation defining the positive benchmark `β_pred`. -/
def BetaPredRootEquation (b c p q σ : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  (q - 1) * predictiveRiskC1 b c p q * α ^ (q / p) =
    predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ))

/-- The defining formula for `predictiveRiskC1`. -/
theorem predictiveRiskC1_def (b c p q : ℝ) :
    predictiveRiskC1 b c p q =
      b * c ^ (-(q - 1) / p) * KernelMoment.integral p 3 (p - q) := rfl

/-- The defining formula for `predictiveRiskC2`. -/
theorem predictiveRiskC2_def (c p : ℝ) :
    predictiveRiskC2 c p =
      c ^ (1 / p) * KernelMoment.integral p 3 p := rfl

/-- The defining formula for the predictive-risk objective `(7.86)`. -/
theorem objective_def (b c p q σ : ℝ) (n : ℕ) (α : ℝ) :
    objective b c p q σ n α =
      predictiveRiskC1 b c p q * α ^ ((q - 1) / p) +
        predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * α ^ (-(1 / p)) := rfl

/-- The defining formula for the source-condition predictive objective. -/
theorem sourceConditionObjective_def
    (sourceNormSq c p σ : ℝ) (n : ℕ) (α : ℝ) :
    sourceConditionObjective sourceNormSq c p σ n α =
      sourceNormSq * α +
        predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) * α ^ (-(1 / p)) := rfl

/-- The defining formula for `betaPredConstant`. -/
theorem betaPredConstant_def (b c p q : ℝ) :
    betaPredConstant b c p q =
      (predictiveRiskC2 c p / ((q - 1) * predictiveRiskC1 b c p q)) ^ (p / q) := rfl

/-- The defining closed form of the benchmark sequence `β_pred`. -/
theorem betaPred_def (b c p q σ : ℝ) (n : ℕ) :
    betaPred b c p q σ n =
      betaPredConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / q)) := rfl

/-- The defining equation for `BetaPredRootEquation`. -/
theorem betaPredRootEquation_iff (b c p q σ : ℝ) (n : ℕ) (α : ℝ) :
    BetaPredRootEquation b c p q σ n α ↔
      (q - 1) * predictiveRiskC1 b c p q * α ^ (q / p) =
        predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) :=
  Iff.rfl

/-- The benchmark `β_pred` satisfies the displayed root equation from Theorem
7.23 once the predictive-risk coefficients are positive and the data size is
strictly positive. -/
theorem betaPred_rootEquation
    (b c p q σ : ℝ)
    (hC1_pos : 0 < predictiveRiskC1 b c p q)
    (hC2_pos : 0 < predictiveRiskC2 c p)
    (h_p : 0 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (n : ℕ+) :
    BetaPredRootEquation b c p q σ n (betaPred b c p q σ n) := by
  have hq_pos : 0 < q := by
    linarith
  have hp_ne : p ≠ 0 := ne_of_gt h_p
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq1 : 0 < q - 1 := by
    linarith
  set ratio : ℝ :=
    predictiveRiskC2 c p / ((q - 1) * predictiveRiskC1 b c p q)
  set scale : ℝ := (σ ^ 2) / (n : ℝ)
  have hden_pos :
      0 < (q - 1) * predictiveRiskC1 b c p q := by
    exact mul_pos hq1 hC1_pos
  have hratio_pos : 0 < ratio := by
    exact div_pos hC2_pos hden_pos
  have hscale_pos : 0 < scale := by
    have hσ_sq : 0 < σ ^ 2 := by
      nlinarith [sq_pos_of_pos h_σ]
    exact div_pos hσ_sq (by exact_mod_cast n.2)
  have hexp : (p / q) * (q / p) = (1 : ℝ) := by
    field_simp [hp_ne, hq_ne]
  have hratio_cancel :
      (q - 1) * predictiveRiskC1 b c p q * ratio = predictiveRiskC2 c p := by
    dsimp [ratio]
    field_simp [hden_pos.ne']
  -- Normalize the positive closed form of `β_pred` and cancel the ratio
  -- hidden inside `betaPredConstant`.
  rw [betaPredRootEquation_iff, betaPred_def, betaPredConstant_def]
  calc
    (q - 1) * predictiveRiskC1 b c p q *
        ((ratio ^ (p / q) * scale ^ (p / q)) ^ (q / p))
        =
          (q - 1) * predictiveRiskC1 b c p q *
            ((ratio ^ (p / q)) ^ (q / p) * (scale ^ (p / q)) ^ (q / p)) := by
              congr 1
              exact
                Real.mul_rpow
                  (show 0 ≤ ratio ^ (p / q) by positivity)
                  (show 0 ≤ scale ^ (p / q) by positivity)
    _ =
          (q - 1) * predictiveRiskC1 b c p q *
            (ratio ^ ((p / q) * (q / p)) * scale ^ ((p / q) * (q / p))) := by
              congr 1
              rw [← Real.rpow_mul hratio_pos.le (p / q) (q / p)]
              rw [← Real.rpow_mul hscale_pos.le (p / q) (q / p)]
    _ = (q - 1) * predictiveRiskC1 b c p q * (ratio * scale) := by
          simp [hexp]
    _ = ((q - 1) * predictiveRiskC1 b c p q * ratio) * scale := by ring
    _ = predictiveRiskC2 c p * scale := by rw [hratio_cancel]
    _ = predictiveRiskC2 c p * ((σ ^ 2) / (n : ℝ)) := by rfl

end TikhonovPredictiveRisk
