module

public import ReasLib.Analysis.Calculus.Gradient.HessianNorm
public import ReasLib.Analysis.Convex.Hessian

public section

open Set

universe u

namespace HessianPerturbation

/-- The gradient of a translated squared norm plus a differentiable perturbation is the
displacement vector plus the perturbation gradient. -/
theorem gradient_halfNormSq_sub_add
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + f y) x =
      x - C + gradient f x := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hquad :=
    ((hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) C).norm_sq.const_smul (1 / 2 : ℝ))
  have hsum := hquad.add hf.hasGradientAt.hasFDerivAt
  have hRiesz :
      (1 / 2 : ℝ) •
          (2 • (innerSL ℝ (x - C)).comp (ContinuousLinearMap.id ℝ E)) +
        InnerProductSpace.toDual ℝ E (gradient f x) =
      InnerProductSpace.toDual ℝ E (x - C + gradient f x) := by
    ext v
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply,
      inner_add_left, innerSL_apply_apply, one_div, smul_eq_mul]
    ring
  have hderiv := hsum.congr_fderiv hRiesz
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [smul_eq_mul]

/-- The Hessian of a translated squared norm plus a twice continuously differentiable
perturbation is the identity operator plus the perturbation Hessian. -/
theorem fderiv_gradient_halfNormSq_sub_add
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Ψ : E → ℝ) (z : E) (hΨ : ContDiff ℝ 2 Ψ) :
    fderiv ℝ (gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x)) z =
      1 + fderiv ℝ (gradient Ψ) z := by
  have htwo_ne : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hΨdiff : Differentiable ℝ Ψ := hΨ.differentiable htwo_ne
  have hgrad :
      gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) =
        fun x ↦ x - C + gradient Ψ x := by
    funext x
    exact gradient_halfNormSq_sub_add C Ψ x hΨdiff.differentiableAt
  have horder : 1 + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right horder
  have hgradientContDiff : ContDiff ℝ 1 (gradient Ψ) := by
    have hgradient_eq : gradient Ψ = fun y ↦
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
          (fderiv ℝ Ψ y) := by
      funext y
      rfl
    rw [hgradient_eq]
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hfderiv
  calc
    fderiv ℝ (gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x)) z =
        fderiv ℝ (fun x ↦ x - C + gradient Ψ x) z := by rw [hgrad]
    _ = fderiv ℝ (fun x ↦ x - C) z + fderiv ℝ (gradient Ψ) z :=
      fderiv_fun_add (differentiableAt_id.sub_const C)
        (hgradientContDiff.differentiable_one.differentiableAt)
    _ = 1 + fderiv ℝ (gradient Ψ) z := by
      rw [fderiv_sub_const, fderiv_fun_id, ← ContinuousLinearMap.one_def]

/-- A global Hessian norm bound below one makes a quadratic base plus the perturbation
strongly convex with the reduced modulus `1 - η`. -/
theorem strongConvexOn_halfNormSq_add_of_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Ψ : E → ℝ) (η : ℝ) (hΨ : ContDiff ℝ 2 Ψ) (hη : η < 1)
    (hbound : ∀ z, ‖fderiv ℝ (gradient Ψ) z‖ ≤ η) :
    StrongConvexOn Set.univ (1 - η)
      (fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + Ψ z) := by
  have htwo_ne : (2 : WithTop ℕ∞) ≠ 0 := by
    norm_num
  have hsub : ContDiff ℝ 2 (fun z : E ↦ z - C) :=
    contDiff_id.sub contDiff_const
  have hquad : ContDiff ℝ 2 (fun z : E ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2) := by
    simpa only [smul_eq_mul] using
      ((hsub.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ))
  have htotal : ContDiff ℝ 2 (fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + Ψ z) :=
    hquad.add hΨ
  have hm : 0 < 1 - η := by linarith
  refine ContDiff.strongConvexOnOfHessianLowerBound
    (fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + Ψ z) (1 - η) htotal hm ?_
  intro z v
  rw [fderiv_gradient_halfNormSq_sub_add C Ψ z hΨ, add_apply,
    one_apply_eq_self, inner_add_left, real_inner_self_eq_norm_sq]
  have hnorm :
      ‖fderiv ℝ (gradient Ψ) z v‖ ≤ η * ‖v‖ :=
    (fderiv ℝ (gradient Ψ) z).le_of_opNorm_le (hbound z) v
  have habs :
      |inner ℝ (fderiv ℝ (gradient Ψ) z v) v| ≤ η * ‖v‖ ^ 2 := by
    calc
      |inner ℝ (fderiv ℝ (gradient Ψ) z v) v| ≤
          ‖fderiv ℝ (gradient Ψ) z v‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (η * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
      _ = η * ‖v‖ ^ 2 := by
        rw [pow_two, mul_assoc]
  have hlower :
      -η * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient Ψ) z v) v := by
    simpa only [neg_mul] using neg_le_of_abs_le habs
  linarith

/-- The same strong-convexity conclusion can be consumed directly from a uniform bound
on the ordinary second Fréchet derivative of the perturbation. -/
theorem strongConvexOn_halfNormSq_add_of_secondFDeriv_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Ψ : E → ℝ) (η : ℝ) (hΨ : ContDiff ℝ 2 Ψ) (hη : η < 1)
    (hbound : ∀ z, ‖fderiv ℝ (fderiv ℝ Ψ) z‖ ≤ η) :
    StrongConvexOn Set.univ (1 - η)
      (fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + Ψ z) := by
  apply strongConvexOn_halfNormSq_add_of_hessian_norm_le C Ψ η hΨ hη
  intro z
  rw [norm_fderiv_gradient_eq_norm_fderiv_fderiv]
  exact hbound z

end HessianPerturbation
