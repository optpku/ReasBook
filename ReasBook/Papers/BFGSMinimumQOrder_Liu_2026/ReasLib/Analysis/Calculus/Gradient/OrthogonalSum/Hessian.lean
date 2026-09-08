module

public import ReasLib.Analysis.Calculus.Gradient.Hessian
public import ReasLib.Analysis.Calculus.Gradient.OrthogonalSum

public section

/-!
# Hessian bounds for orthogonal-sum objectives
-/

noncomputable section

universe u v

namespace EuclideanSpace.OrthogonalSum.Gradient

/-- Adding a half squared norm on an orthogonal summand preserves twice continuous
differentiability. -/
theorem contDiff_objective {iota : Type u} {kappa : Type v}
    [Fintype iota] [Fintype kappa] {f : EuclideanSpace ℝ iota → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (objective (κ := kappa) f) := by
  have hleft := hf.comp (left (ι := iota) (κ := kappa)).contDiff
  have hright : ContDiff ℝ 2 (fun p : EuclideanSpace ℝ (iota ⊕ kappa) =>
      ‖right p‖ ^ 2 / 2) :=
    ((right (ι := iota) (κ := kappa)).contDiff.norm_sq ℝ).div_const 2
  have hobjective := hleft.add hright
  have hobjectiveEq : objective (κ := kappa) f =
      fun p : EuclideanSpace ℝ (iota ⊕ kappa) =>
        (f ∘ left) p + ‖right p‖ ^ 2 / 2 := by
    funext p
    exact objective_apply f p
  rw [hobjectiveEq]
  exact hobjective

/-- If the original Hessian lies between `m I` and `M I`, adjoining an identity quadratic
block preserves those bounds whenever `m ≤ 1 ≤ M`. -/
theorem hasHessianBounds_objective {iota : Type u} {kappa : Type v}
    [Fintype iota] [Fintype kappa] {m M : ℝ} {f : EuclideanSpace ℝ iota → ℝ}
    (hf : ContDiff ℝ 2 f) (h : HasHessianBounds m M f) (hm : m ≤ 1) (hM : 1 ≤ M) :
    HasHessianBounds m M (objective (κ := kappa) f) := by
  have hfDiff : Differentiable ℝ f := by
    apply hf.differentiable
    norm_num
  have hgradientContDiff : ContDiff ℝ 1 (gradient f) := by
    have hfderivContDiff : ContDiff ℝ 1 (fderiv ℝ f) := by
      apply hf.fderiv_right
      norm_num
    unfold gradient
    exact hfderivContDiff.continuousLinearMap_comp
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ iota)).symm :
        StrongDual ℝ (EuclideanSpace ℝ iota) →L[ℝ] EuclideanSpace ℝ iota)
  have hgradientDiff : Differentiable ℝ (gradient f) := by
    apply hgradientContDiff.differentiable
    norm_num
  have hgradientEq : gradient (objective (κ := kappa) f) =
      fun p : EuclideanSpace ℝ (iota ⊕ kappa) =>
        (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm
          (gradient f (left p), right p) := by
    funext p
    exact gradient_objective (hfDiff (left p))
  apply HasHessianBounds.of_forall
  intro p
  have hgradLeft :
      HasFDerivAt (fun q : EuclideanSpace ℝ (iota ⊕ kappa) => gradient f (left q))
        ((hessian f (left p)).comp left) p := by
    have hgradF : HasFDerivAt (gradient f) (hessian f (left p)) (left p) := by
      rw [hessian_def]
      exact (hgradientDiff (left p)).hasFDerivAt
    exact hgradF.comp p (left (ι := iota) (κ := kappa)).hasFDerivAt
  have hpair := hgradLeft.prodMk (right (ι := iota) (κ := kappa)).hasFDerivAt
  have hblock :=
    (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := iota) (κ := kappa)).symm.hasFDerivAt.comp
      p hpair
  have hhessianAction (w : EuclideanSpace ℝ (iota ⊕ kappa)) :
      hessian (objective (κ := kappa) f) p w =
        (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm
          (hessian f (left p) (left w), right w) := by
    have hblockFDeriv := hblock.fderiv
    simp only [Function.comp_def] at hblockFDeriv
    rw [hessian_def, hgradientEq, hblockFDeriv]
    rfl
  apply HasHessianBoundsAt.of_quadraticForm
  · exact hessian_isSelfAdjoint ((contDiff_objective hf).contDiffAt)
  · intro w
    have hbounds := (h.at (left p)).quadraticForm (left w)
    have hrightNonneg : 0 ≤ ‖right w‖ ^ 2 := sq_nonneg _
    have hlowerRight : m * ‖right w‖ ^ 2 ≤ 1 * ‖right w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hm hrightNonneg
    have hupperRight : 1 * ‖right w‖ ^ 2 ≤ M * ‖right w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hM hrightNonneg
    have hquadratic :
        inner ℝ (hessian (objective (κ := kappa) f) p w) w =
          inner ℝ (hessian f (left p) (left w)) (left w) + ‖right w‖ ^ 2 := by
      rw [hhessianAction, inner_eq_left_add_right]
      simp only [left_sumEquivProd_symm, right_sumEquivProd_symm,
        real_inner_self_eq_norm_sq]
    rw [hquadratic, norm_sq_eq_left_add_right]
    constructor
    · nlinarith [hbounds.1]
    · nlinarith [hbounds.2]

end EuclideanSpace.OrthogonalSum.Gradient
