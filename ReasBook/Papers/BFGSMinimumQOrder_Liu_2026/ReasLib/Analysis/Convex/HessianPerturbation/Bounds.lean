module

public import ReasLib.Analysis.Calculus.Gradient.Hessian
public import ReasLib.Analysis.Convex.HessianPerturbation
public import ReasLib.Analysis.InnerProductSpace.OperatorBounds

public section

open Filter

universe u

namespace HessianPerturbation

/-- Adding a twice continuously differentiable perturbation to half the squared distance
preserves twice continuous differentiability at the base point. -/
theorem contDiffAt_halfNormSq_sub_add
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Psi : E → ℝ) (z : E) (hPsi : ContDiffAt ℝ 2 Psi z) :
    ContDiffAt ℝ 2 (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x) z := by
  have hsub : ContDiffAt ℝ 2 (fun x : E ↦ x - C) z :=
    contDiffAt_id.sub contDiffAt_const
  have hquad : ContDiffAt ℝ 2 (fun x : E ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2) z := by
    simpa only [smul_eq_mul] using
      ((hsub.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ))
  exact hquad.add hPsi

/-- The Hessian of half the squared distance plus a `C²` perturbation is the identity
operator plus the perturbation Hessian. -/
theorem hessian_halfNormSq_sub_add
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Psi : E → ℝ) (z : E) (hPsi : ContDiffAt ℝ 2 Psi z) :
    hessian (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x) z = 1 + hessian Psi z := by
  have finiteOrder :
      (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hgrad :
      gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x) =ᶠ[nhds z]
        fun x ↦ x - C + gradient Psi x := by
    filter_upwards [hPsi.eventually finiteOrder] with x hx
    exact gradient_halfNormSq_sub_add C Psi x (hx.differentiableAt two_ne_zero)
  have horder : 1 + 1 ≤ (2 : WithTop ℕ∞) := by
    norm_num
  have hgradientContDiff : ContDiffAt ℝ 1 (gradient Psi) z := by
    unfold gradient
    exact (hPsi.fderiv_right (m := 1) horder).continuousLinearMap_comp
      ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E)
  rw [hessian_def, hessian_def]
  calc
    fderiv ℝ (gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x)) z =
        fderiv ℝ (fun x ↦ x - C + gradient Psi x) z := hgrad.fderiv_eq
    _ = fderiv ℝ (fun x ↦ x - C) z + fderiv ℝ (gradient Psi) z :=
      fderiv_fun_add (differentiableAt_id.sub_const C)
        (hgradientContDiff.differentiableAt one_ne_zero)
    _ = 1 + fderiv ℝ (gradient Psi) z := by
      rw [fderiv_sub_const, fderiv_fun_id, ← ContinuousLinearMap.one_def]

/-- An operator-norm bound on a perturbation Hessian gives pointwise two-sided Loewner
bounds for half the squared distance plus that perturbation. -/
theorem hasHessianBoundsAt_halfNormSq_sub_add_of_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Psi : E → ℝ) (z : E) (eta : ℝ) (hPsi : ContDiffAt ℝ 2 Psi z)
    (hNorm : ‖hessian Psi z‖ ≤ eta) :
    HasHessianBoundsAt (1 - eta) (1 + eta)
      (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x) z := by
  apply HasHessianBoundsAt.of_quadraticForm
  · exact hessian_isSelfAdjoint (contDiffAt_halfNormSq_sub_add C Psi z hPsi)
  · intro v
    have hbounds := ContinuousLinearMap.inner_apply_bounds_of_norm_le
      (hessian Psi z) eta hNorm v
    rw [hessian_halfNormSq_sub_add C Psi z hPsi, add_apply,
      one_apply_eq_self, inner_add_left, real_inner_self_eq_norm_sq]
    constructor
    · linarith [hbounds.1]
    · linarith [hbounds.2]

/-- A uniform perturbation-Hessian norm bound gives global two-sided Loewner bounds for
half the squared distance plus the perturbation. -/
theorem hasHessianBounds_halfNormSq_sub_add_of_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Psi : E → ℝ) (eta : ℝ) (hPsi : ContDiff ℝ 2 Psi)
    (hNorm : ∀ z, ‖hessian Psi z‖ ≤ eta) :
    HasHessianBounds (1 - eta) (1 + eta)
      (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x) := by
  apply HasHessianBounds.of_forall
  intro z
  exact hasHessianBoundsAt_halfNormSq_sub_add_of_hessian_norm_le
    C Psi z eta hPsi.contDiffAt (hNorm z)

/-- A uniform bound on the ordinary second Frechet derivative can be consumed directly as
global two-sided Hessian bounds for a quadratic base plus a perturbation. -/
theorem hasHessianBounds_halfNormSq_sub_add_of_secondFDeriv_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : E) (Psi : E → ℝ) (eta : ℝ) (hPsi : ContDiff ℝ 2 Psi)
    (hNorm : ∀ z, ‖fderiv ℝ (fderiv ℝ Psi) z‖ ≤ eta) :
    HasHessianBounds (1 - eta) (1 + eta)
      (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Psi x) := by
  apply hasHessianBounds_halfNormSq_sub_add_of_hessian_norm_le C Psi eta hPsi
  intro z
  rw [hessian_def, norm_fderiv_gradient_eq_norm_fderiv_fderiv]
  exact hNorm z

end HessianPerturbation
