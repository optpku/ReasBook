module

public import ReasLib.Analysis.Convex.HessianPerturbation

public section

universe u

namespace HessianPerturbation

/-- A perturbation value that vanishes at a point leaves the translated quadratic value
unchanged there. -/
theorem halfNormSq_sub_add_apply_of_eq_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E) {Ψ : E → ℝ} {x : E} (hΨ : Ψ x = 0) :
    (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x = (1 / 2 : ℝ) * ‖x - C‖ ^ 2 := by
  rw [hΨ, add_zero]

/-- A certified perturbation gradient adds to the displacement gradient of the translated
quadratic base. -/
theorem hasGradientAt_halfNormSq_sub_add
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) {Ψ : E → ℝ} {x a : E} (hΨ : HasGradientAt Ψ a x) :
    HasGradientAt (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + Ψ y) (x - C + a) x := by
  have hquad : DifferentiableAt ℝ (fun y : E ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2) x := by
    have hsub : DifferentiableAt ℝ (fun y : E ↦ y - C) x :=
      differentiableAt_id.sub_const C
    exact (differentiableAt_const (c := (1 / 2 : ℝ))).mul (hsub.norm_sq (𝕜 := ℝ))
  have htotal : DifferentiableAt ℝ
      (fun y : E ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + Ψ y) x :=
    hquad.add hΨ.differentiableAt
  have hcanonical := htotal.hasGradientAt
  rw [gradient_halfNormSq_sub_add C Ψ x hΨ.differentiableAt, hΨ.gradient] at hcanonical
  exact hcanonical

/-- Under a perturbation gradient certificate, the canonical gradient of the translated
quadratic plus the perturbation is the displacement plus the certified gradient. -/
theorem gradient_halfNormSq_sub_add_of_hasGradientAt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) {Ψ : E → ℝ} {x a : E} (hΨ : HasGradientAt Ψ a x) :
    gradient (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + Ψ y) x = x - C + a := by
  exact (hasGradientAt_halfNormSq_sub_add C hΨ).gradient

end HessianPerturbation
