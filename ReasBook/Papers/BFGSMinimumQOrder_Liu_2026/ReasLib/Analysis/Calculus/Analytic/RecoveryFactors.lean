module

public import Mathlib.Analysis.Analytic.Constructions

public section

noncomputable section

namespace AnalyticRecovery

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quotient package used by a two-factor radius/shape recovery map. -/
def recoveryFactors (S G : E → ℝ × ℝ) (x : E) : ℝ × ℝ × ℝ :=
  ((S x).1 * (G x).1 / ((S x).2 * (G x).2),
    (S x).2 * (G x).2 ^ 2 / ((S x).1 * (G x).1 ^ 2),
    (S x).2)

/-- Helper for Appendix Lemma A.5: analytic spectral and gradient factor pairs give an
analytic recovery package whenever the two quotient denominators are nonzero. -/
theorem analyticAt_recoveryFactors
    {S G : E → ℝ × ℝ} {x : E}
    (hS : AnalyticAt ℝ S x) (hG : AnalyticAt ℝ G x)
    (hRadius : (S x).2 * (G x).2 ≠ 0)
    (hShape : (S x).1 * (G x).1 ^ 2 ≠ 0) :
    AnalyticAt ℝ (recoveryFactors S G) x := by
  have hS₁ : AnalyticAt ℝ (fun y ↦ (S y).1) x := analyticAt_fst.comp hS
  have hS₂ : AnalyticAt ℝ (fun y ↦ (S y).2) x := analyticAt_snd.comp hS
  have hG₁ : AnalyticAt ℝ (fun y ↦ (G y).1) x := analyticAt_fst.comp hG
  have hG₂ : AnalyticAt ℝ (fun y ↦ (G y).2) x := analyticAt_snd.comp hG
  have hRadiusDen : AnalyticAt ℝ
      (fun y ↦ (S y).2 * (G y).2) x := hS₂.mul hG₂
  have hShapeDen : AnalyticAt ℝ
      (fun y ↦ (S y).1 * (G y).1 ^ 2) x := hS₁.mul (hG₁.pow 2)
  have hRadiusNum : AnalyticAt ℝ
      (fun y ↦ (S y).1 * (G y).1) x := hS₁.mul hG₁
  have hShapeNum : AnalyticAt ℝ
      (fun y ↦ (S y).2 * (G y).2 ^ 2) x := hS₂.mul (hG₂.pow 2)
  have hRadius : AnalyticAt ℝ
      (fun y ↦ (S y).1 * (G y).1 / ((S y).2 * (G y).2)) x :=
    hRadiusNum.div hRadiusDen hRadius
  have hShape : AnalyticAt ℝ
      (fun y ↦ (S y).2 * (G y).2 ^ 2 / ((S y).1 * (G y).1 ^ 2)) x :=
    hShapeNum.div hShapeDen hShape
  have hTriple := hRadius.prod (hShape.prod hS₂)
  unfold recoveryFactors
  apply hTriple.congr
  filter_upwards [] with y
  rfl

end AnalyticRecovery
