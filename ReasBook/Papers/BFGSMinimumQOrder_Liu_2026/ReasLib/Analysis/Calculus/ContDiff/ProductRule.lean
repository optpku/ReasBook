module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

public section

universe u

/-- The second Fréchet derivative of a product of real-valued `C²` functions satisfies
the four-term Leibniz rule. Here the outer derivative is applied first to `v`, and the
resulting continuous linear map is then evaluated at `u`. -/
theorem fderiv_fderiv_mul_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x v u : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f y * g y)) x v u =
      f x * fderiv ℝ (fderiv ℝ g) x v u +
        fderiv ℝ f x v * fderiv ℝ g x u +
        fderiv ℝ f x u * fderiv ℝ g x v +
        g x * fderiv ℝ (fderiv ℝ f) x v u := by
  have hdf : DifferentiableAt ℝ f x := by
    apply hf.differentiableAt
    norm_num
  have hdg : DifferentiableAt ℝ g x := by
    apply hg.differentiableAt
    norm_num
  have hf_fderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x := by
    apply hf.fderiv_right (m := 1)
    norm_num
  have hg_fderiv : ContDiffAt ℝ 1 (fderiv ℝ g) x := by
    apply hg.fderiv_right (m := 1)
    norm_num
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x := by
    apply hf_fderiv.differentiableAt
    norm_num
  have hDg : DifferentiableAt ℝ (fderiv ℝ g) x := by
    apply hg_fderiv.differentiableAt
    norm_num
  have hprod :
      fderiv ℝ (fun y ↦ f y * g y) =ᶠ[nhds x]
        fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    have hf_eventually : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := by
      apply hf.eventually
      norm_num
    have hg_eventually : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 g y := by
      apply hg.eventually
      norm_num
    filter_upwards [hf_eventually, hg_eventually] with y hfy hgy
    have hfy_diff : DifferentiableAt ℝ f y := by
      apply hfy.differentiableAt
      norm_num
    have hgy_diff : DifferentiableAt ℝ g y := by
      apply hgy.differentiableAt
      norm_num
    exact fderiv_fun_mul hfy_diff hgy_diff
  rw [hprod.fderiv_eq]
  change ((fderiv ℝ (f • fderiv ℝ g + g • fderiv ℝ f) x) v) u = _
  rw [fderiv_add (hdf.smul hDg) (hdg.smul hDf),
    fderiv_smul hdf hDg, fderiv_smul hdg hDf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  ring
