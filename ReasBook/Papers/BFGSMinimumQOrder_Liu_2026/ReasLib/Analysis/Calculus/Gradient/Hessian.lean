module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import ReasLib.Analysis.Calculus.Gradient.CoordinateChange
public import ReasLib.Analysis.Calculus.Gradient.HessianNorm
public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# Operator-valued Hessians and uniform bounds

The canonical Hessian is represented as the derivative of the gradient on a real Hilbert space.
Bounds use the Loewner order, so coordinate changes are ordinary operator congruences.
-/

noncomputable section

universe u v

open scoped InnerProduct

/-- The gradient of a `C^{n+1}` real-valued function is `C^n`. -/
theorem ContDiff.gradient_succ {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ∞} {f : E → ℝ}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (gradient f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  unfold gradient
  exact hf.contDiffAt.fderiv_right_succ.continuousLinearMap_comp
    ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E)

/-- Pointwise, the gradient of a `C^{n+1}` real-valued function is `C^n`. -/
theorem ContDiffAt.gradient_succ {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ∞} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ (n + 1) f x) : ContDiffAt ℝ n (gradient f) x := by
  unfold gradient
  exact hf.fderiv_right_succ.continuousLinearMap_comp
    ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E)

/-- The Hessian of a real-valued function, represented as a continuous linear endomorphism. -/
def hessian {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient f) x

/-- The operator-valued Hessian is the derivative of the gradient. -/
theorem hessian_def {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    hessian f x = fderiv ℝ (gradient f) x := by
  rfl

/-- Pairing the Hessian with two directions evaluates the second iterated Frechet derivative. -/
theorem hessian_apply_inner {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x u v : E) :
    inner ℝ (hessian f x u) v = iteratedFDeriv ℝ 2 f x ![u, v] := by
  unfold hessian gradient
  have hRiesz :
      fderiv ℝ
          (fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) x =
        ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E) ∘L
          fderiv ℝ (fderiv ℝ f) x := by
    have hfun :
        (fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) =
          (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f := rfl
    rw [hfun]
    exact LinearIsometryEquiv.comp_fderiv (InnerProductSpace.toDual ℝ E).symm
  rw [hRiesz, ContinuousLinearMap.comp_apply]
  calc
    inner ℝ
        ((InnerProductSpace.toDual ℝ E).symm
          (fderiv ℝ (fderiv ℝ f) x u)) v =
        fderiv ℝ (fderiv ℝ f) x u v := InnerProductSpace.toDual_symm_apply
    _ = iteratedFDeriv ℝ 2 f x ![u, v] := (iteratedFDeriv_two_apply f x ![u, v]).symm

/-- The Hessian norm agrees with the norm of the second iterated Frechet derivative. -/
theorem norm_hessian_eq_norm_iteratedFDeriv_two {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x : E) :
    ‖hessian f x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  exact norm_fderiv_gradient_eq_norm_iteratedFDeriv_two f x

/-- Twice continuous differentiability makes the Hessian self-adjoint. -/
theorem hessian_isSelfAdjoint {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : IsSelfAdjoint (hessian f x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  calc
    inner ℝ (hessian f x u) v = iteratedFDeriv ℝ 2 f x ![u, v] :=
      hessian_apply_inner f x u v
    _ = iteratedFDeriv ℝ 2 f x ![v, u] := by
      have hSmooth : minSmoothness ℝ 2 ≤ 2 := by simp
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
      exact (hf.isSymmSndFDerivAt hSmooth).eq u v
    _ = inner ℝ (hessian f x v) u := (hessian_apply_inner f x v u).symm
    _ = inner ℝ u (hessian f x v) := real_inner_comm _ _

/-- Pointwise lower and upper Loewner bounds on a Hessian. -/
structure HasHessianBoundsAt {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (m M : ℝ) (f : E → ℝ) (x : E) : Prop where
  lower : m • (1 : E →L[ℝ] E) ≤ hessian f x
  upper : hessian f x ≤ M • (1 : E →L[ℝ] E)

/-- Global lower and upper Loewner bounds on a Hessian. -/
def HasHessianBounds {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (m M : ℝ) (f : E → ℝ) : Prop :=
  ∀ x, HasHessianBoundsAt m M f x

/-- A global Hessian bound specializes at every point. -/
theorem HasHessianBounds.at {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {m M : ℝ} {f : E → ℝ}
    (h : HasHessianBounds m M f) (x : E) : HasHessianBoundsAt m M f x :=
  h x

/-- Pointwise Hessian bounds at every point assemble into a global Hessian bound. -/
theorem HasHessianBounds.of_forall {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {m M : ℝ} {f : E → ℝ}
    (h : ∀ x, HasHessianBoundsAt m M f x) : HasHessianBounds m M f := by
  exact h

/-- Loewner Hessian bounds imply the corresponding quadratic-form inequalities. -/
theorem HasHessianBoundsAt.quadraticForm {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {m M : ℝ} {f : E → ℝ} {x : E}
    (h : HasHessianBoundsAt m M f x) (v : E) :
    m * ‖v‖ ^ 2 ≤ inner ℝ (hessian f x v) v ∧
      inner ℝ (hessian f x v) v ≤ M * ‖v‖ ^ 2 := by
  constructor
  · have lower := (ContinuousLinearMap.le_def _ _).mp h.lower
    have hv := lower.inner_nonneg_left v
    simp only [sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hv
    linarith
  · have upper := (ContinuousLinearMap.le_def _ _).mp h.upper
    have hv := upper.inner_nonneg_left v
    simp only [sub_apply, smul_apply,
      one_apply_eq_self, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hv
    linarith

/-- A self-adjoint Hessian satisfying quadratic-form inequalities has the corresponding
Loewner bounds. -/
theorem HasHessianBoundsAt.of_quadraticForm {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {m M : ℝ} {f : E → ℝ} {x : E}
    (selfAdjoint : IsSelfAdjoint (hessian f x))
    (bounds : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner ℝ (hessian f x v) v ∧
      inner ℝ (hessian f x v) v ≤ M * ‖v‖ ^ 2) :
    HasHessianBoundsAt m M f x := by
  constructor
  · rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
    constructor
    · exact selfAdjoint.sub ((IsSelfAdjoint.all m).smul (IsSelfAdjoint.one _))
    · intro v
      have lower := (bounds v).1
      simp only [sub_apply, smul_apply,
        one_apply_eq_self, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      linarith
  · rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
    constructor
    · exact ((IsSelfAdjoint.all M).smul (IsSelfAdjoint.one _)).sub selfAdjoint
    · intro v
      have upper := (bounds v).2
      simp only [sub_apply, smul_apply,
        one_apply_eq_self, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      linarith

/-- Hessians transform by adjoint congruence under a continuous linear equivalence. -/
theorem ContinuousLinearEquiv.comp_right_hessian
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (f : F → ℝ) (x : E)
    (hf : DifferentiableAt ℝ (gradient f) (L x)) :
    hessian (f ∘ L) x = L.toContinuousLinearMap.pullback (hessian f (L x)) := by
  have gradient_eq : gradient (f ∘ L) =
      (L.toContinuousLinearMap†) ∘ fun z ↦ gradient f (L z) := by
    funext z
    exact L.comp_right_gradient f z
  rw [hessian, gradient_eq]
  have innerDerivative : HasFDerivAt (fun z ↦ gradient f (L z))
      ((fderiv ℝ (gradient f) (L x)).comp L.toContinuousLinearMap) x :=
    hf.hasFDerivAt.comp x L.hasFDerivAt
  have pullbackDerivative := L.toContinuousLinearMap.adjoint.hasFDerivAt.comp x innerDerivative
  simpa [ContinuousLinearMap.pullback_def, ContinuousLinearMap.comp_assoc, hessian] using
    pullbackDerivative.fderiv

/-- Relative norm bounds on a coordinate map transport pointwise Hessian bounds. -/
theorem HasHessianBoundsAt.comp_continuousLinearEquiv
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {m M a b : ℝ} {f : F → ℝ} {x : E} (L : E ≃L[ℝ] F)
    (h : HasHessianBoundsAt m M f (L x))
    (hf : DifferentiableAt ℝ (gradient f) (L x)) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (lowerMap : a • (1 : E →L[ℝ] E) ≤ L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤ b • (1 : E →L[ℝ] E)) :
    HasHessianBoundsAt (m * a) (M * b) (f ∘ L) x := by
  constructor
  · rw [L.comp_right_hessian f x hf]
    calc
      (m * a) • (1 : E →L[ℝ] E) = m • (a • (1 : E →L[ℝ] E)) := by
        rw [smul_smul]
      _ ≤ m • L.toContinuousLinearMap.pullback 1 :=
        ContinuousLinearMap.smul_mono lowerMap hm
      _ = L.toContinuousLinearMap.pullback (m • (1 : F →L[ℝ] F)) := by
        rw [ContinuousLinearMap.pullback_smul]
      _ ≤ L.toContinuousLinearMap.pullback (hessian f (L x)) :=
        L.toContinuousLinearMap.pullback_mono h.lower
  · rw [L.comp_right_hessian f x hf]
    calc
      L.toContinuousLinearMap.pullback (hessian f (L x)) ≤
          L.toContinuousLinearMap.pullback (M • (1 : F →L[ℝ] F)) :=
        L.toContinuousLinearMap.pullback_mono h.upper
      _ = M • L.toContinuousLinearMap.pullback 1 := by
        rw [ContinuousLinearMap.pullback_smul]
      _ ≤ M • (b • (1 : E →L[ℝ] E)) :=
        ContinuousLinearMap.smul_mono upperMap hM
      _ = (M * b) • (1 : E →L[ℝ] E) := by
        rw [smul_smul]

/-- Relative norm bounds on a coordinate map transport global Hessian bounds. -/
theorem HasHessianBounds.comp_continuousLinearEquiv
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {m M a b : ℝ} {f : F → ℝ} (L : E ≃L[ℝ] F)
    (h : HasHessianBounds m M f) (hf : Differentiable ℝ (gradient f))
    (hm : 0 ≤ m) (hM : 0 ≤ M)
    (lowerMap : a • (1 : E →L[ℝ] E) ≤ L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤ b • (1 : E →L[ℝ] E)) :
    HasHessianBounds (m * a) (M * b) (f ∘ L) := by
  intro x
  exact HasHessianBoundsAt.comp_continuousLinearEquiv L (h (L x)) (hf (L x)) hm hM
    lowerMap upperMap

/-- Hessian bounds are invariant under an isometric linear change of coordinates. -/
theorem HasHessianBounds.comp_linearIsometryEquiv
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {m M : ℝ} {f : F → ℝ} (Q : E ≃ₗᵢ[ℝ] F) (h : HasHessianBounds m M f)
    (hf : Differentiable ℝ (gradient f)) (hm : 0 ≤ m) (hM : 0 ≤ M) :
    HasHessianBounds m M (f ∘ Q) := by
  let L : E ≃L[ℝ] F := Q.toContinuousLinearEquiv
  have hgram : L.toContinuousLinearMap.pullback (1 : F →L[ℝ] F) =
      (1 : E →L[ℝ] E) := by
    change Q.toLinearIsometry.toContinuousLinearMap.pullback (1 : F →L[ℝ] F) =
      (1 : E →L[ℝ] E)
    rw [ContinuousLinearMap.pullback_one]
    exact Q.toLinearIsometry.adjoint_comp_self
  have htransport := h.comp_continuousLinearEquiv
    (a := 1) (b := 1) L hf hm hM
    (by rw [one_smul, hgram]) (by rw [one_smul, hgram])
  have hfun : f ∘ L = f ∘ Q := by rfl
  rw [hfun] at htransport
  simpa only [mul_one] using htransport

end
