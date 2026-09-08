module

public import ReasLib.Analysis.InnerProductSpace.OperatorBounds
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Lp.Matrix

public section

noncomputable section

namespace EuclideanPlane

open scoped Matrix

/-- The Hessian of a real-valued function on the Euclidean plane, represented as the
Fréchet derivative of its gradient. -/
def hessian (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  fderiv ℝ (gradient f) x

/-- The operator-valued Hessian unfolds to the Fréchet derivative of the gradient. -/
theorem hessian_def (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    hessian f x = fderiv ℝ (gradient f) x := by
  -- Unfolding the Hessian exposes the same Fréchet derivative on both sides.
  rfl

/-- Pairing the operator-valued Hessian with a direction recovers the second iterated
Fréchet derivative. -/
theorem hessian_apply_inner (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x u v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (hessian f x u) v = iteratedFDeriv ℝ 2 f x ![u, v] := by
  -- Route correction: the owned scope includes the full companion API, beginning with this bridge.
  -- Differentiate the Riesz representative and then evaluate its representing functional.
  unfold hessian gradient
  have hRiesz :
      fderiv ℝ
          (fun y ↦ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
            (fderiv ℝ f y)) x =
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm :
          StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘L
            fderiv ℝ (fderiv ℝ f) x := by
    have hfun :
        (fun y ↦ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
          (fderiv ℝ f y)) =
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm ∘ fderiv ℝ f := rfl
    rw [hfun]
    exact LinearIsometryEquiv.comp_fderiv
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
  rw [hRiesz, ContinuousLinearMap.comp_apply]
  calc
    inner ℝ
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm
          (fderiv ℝ (fderiv ℝ f) x u)) v =
        fderiv ℝ (fderiv ℝ f) x u v := InnerProductSpace.toDual_symm_apply
    _ = iteratedFDeriv ℝ 2 f x ![u, v] := (iteratedFDeriv_two_apply f x ![u, v]).symm

/-- At a point where `f` is `C²`, its operator-valued Hessian is self-adjoint. -/
theorem hessian_isSelfAdjoint (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (hf : ContDiffAt ℝ 2 f x) :
    IsSelfAdjoint (hessian f x) := by
  -- Reduce self-adjointness to symmetry of the associated bilinear pairing.
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  -- Schwarz symmetry applies because the function is twice continuously differentiable.
  calc
    inner ℝ (hessian f x u) v = iteratedFDeriv ℝ 2 f x ![u, v] :=
      hessian_apply_inner f x u v
    _ = iteratedFDeriv ℝ 2 f x ![v, u] := by
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
      exact (hf.isSymmSndFDerivAt (by simp)).eq u v
    _ = inner ℝ (hessian f x v) u := (hessian_apply_inner f x v u).symm
    _ = inner ℝ u (hessian f x v) := real_inner_comm _ _

/-- The matrix of the Hessian in the canonical orthonormal coordinates on the Euclidean plane. -/
def hessianMatrix (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Matrix.toEuclideanCLM :
    Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).symm (hessian f x)

/-- Converting the Hessian matrix back to a Euclidean continuous linear map recovers the Hessian. -/
theorem toEuclideanCLM_hessianMatrix (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (Matrix.toEuclideanCLM :
      Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (hessianMatrix f x) = hessian f x := by
  -- The matrix was defined by applying the inverse equivalence to the Hessian.
  unfold hessianMatrix
  exact (Matrix.toEuclideanCLM :
    Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).apply_symm_apply _

/-- Applying the Hessian agrees in canonical coordinates with multiplying by its Hessian matrix. -/
theorem hessianMatrix_apply (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace.equiv (Fin 2) ℝ (hessian f x u) =
      hessianMatrix f x *ᵥ EuclideanSpace.equiv (Fin 2) ℝ u := by
  -- Replace the Hessian by its matrix realization and read the result in coordinates.
  rw [← toEuclideanCLM_hessianMatrix f x]
  exact Matrix.ofLp_toEuclideanCLM (hessianMatrix f x) u

/-- At a point where `f` is `C²`, its Hessian matrix is Hermitian, hence symmetric over `ℝ`. -/
theorem hessianMatrix_isHermitian (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (hf : ContDiffAt ℝ 2 f x) :
    (hessianMatrix f x).IsHermitian := by
  -- Transport self-adjointness through the canonical matrix-to-operator equivalence.
  rw [← Matrix.isSymmetric_toEuclideanLin_iff,
    ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rw [toEuclideanCLM_hessianMatrix]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hessian_isSelfAdjoint f x hf)

/-- The determinant of the Hessian matrix equals the determinant of the Hessian linear map. -/
theorem det_hessianMatrix (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (hessianMatrix f x).det = LinearMap.det (hessian f x).toLinearMap := by
  -- Compute the determinant after converting both sides to the same coordinate linear map.
  have hop : Matrix.toEuclideanLin (hessianMatrix f x) = (hessian f x).toLinearMap := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanCLM_hessianMatrix]
  calc
    (hessianMatrix f x).det =
        LinearMap.det (Matrix.toEuclideanLin (hessianMatrix f x)) :=
      (LinearMap.det_toLin (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (hessianMatrix f x)).symm
    _ = LinearMap.det (hessian f x).toLinearMap := congrArg LinearMap.det hop

/-- Positive semidefiniteness of a real matrix is positivity of its Euclidean operator. -/
private lemma posSemidef_iff_isPositive_toEuclideanCLM {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℝ) :
    A.PosSemidef ↔
      ((Matrix.toEuclideanCLM :
        Matrix n n ℝ ≃⋆ₐ[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A).IsPositive := by
  -- Pass through the underlying Euclidean linear map, where mathlib states the equivalence.
  rw [← Matrix.isPositive_toEuclideanLin_iff,
    ← ContinuousLinearMap.isPositive_toLinearMap_iff,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]

/-- A lower Loewner bound on the Hessian matrix is equivalent to the corresponding quadratic-form
bound on the Hessian operator. -/
theorem lowerBound_hessianMatrix_iff (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (m : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    (hessianMatrix f x - m • 1).PosSemidef ↔
      ∀ v : EuclideanSpace ℝ (Fin 2),
        m * ‖v‖ ^ 2 ≤ inner ℝ (hessian f x v) v := by
  -- Convert the matrix inequality into positivity of the shifted Hessian operator.
  rw [posSemidef_iff_isPositive_toEuclideanCLM]
  simp only [map_sub, map_smul, map_one, toEuclideanCLM_hessianMatrix]
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · rintro ⟨_, hquad⟩ v
    -- Expanding the shifted quadratic form gives the stated scalar lower bound.
    have hv := hquad v
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq] at hv
    linarith
  · intro hquad
    refine ⟨(hessian_isSelfAdjoint f x hf).sub
      ((IsSelfAdjoint.all m).smul (IsSelfAdjoint.one _)), ?_⟩
    intro v
    -- The assumed lower bound is exactly nonnegativity after subtracting `m I`.
    specialize hquad v
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq]
    linarith

/-- An upper Loewner bound on the Hessian matrix is equivalent to the corresponding quadratic-form
bound on the Hessian operator. -/
theorem upperBound_hessianMatrix_iff (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) (M : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    (M • 1 - hessianMatrix f x).PosSemidef ↔
      ∀ v : EuclideanSpace ℝ (Fin 2),
        inner ℝ (hessian f x v) v ≤ M * ‖v‖ ^ 2 := by
  -- Convert the matrix inequality into positivity of `M I - Hessian`.
  rw [posSemidef_iff_isPositive_toEuclideanCLM]
  simp only [map_sub, map_smul, map_one, toEuclideanCLM_hessianMatrix]
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · rintro ⟨_, hquad⟩ v
    -- Expanding the shifted quadratic form gives the stated scalar upper bound.
    have hv := hquad v
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq] at hv
    linarith
  · intro hquad
    refine ⟨((IsSelfAdjoint.all M).smul (IsSelfAdjoint.one _)).sub
      (hessian_isSelfAdjoint f x hf), ?_⟩
    intro v
    -- The assumed upper bound is exactly nonnegativity after subtracting the Hessian.
    specialize hquad v
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq]
    linarith

/-- The gradient transforms contravariantly under an orthogonal change of frame. -/
theorem gradient_comp_linearIsometry (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (Q : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) :
    gradient (fun y ↦ f (Q y)) x = Q.symm (gradient f (Q x)) := by
  -- Compose the Riesz derivative of `f` with `Q` and identify its representing vector.
  have hRiesz :
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)))
          (Q.symm (gradient f (Q x))) =
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)) (gradient f (Q x))) ∘L
          (Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    calc
      inner ℝ (Q.symm (gradient f (Q x))) v =
          inner ℝ v (Q.symm (gradient f (Q x))) := real_inner_comm _ _
      _ = inner ℝ (Q v) (gradient f (Q x)) :=
        (Q.inner_map_eq_flip v (gradient f (Q x))).symm
      _ = inner ℝ (gradient f (Q x)) (Q v) := real_inner_comm _ _
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).injective
  rw [hRiesz]
  simp only [toDual_gradient]
  have hfun : (fun y ↦ f (Q y)) =
      f ∘ (Q : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) := rfl
  rw [hfun]
  exact ContinuousLinearEquiv.comp_right_fderiv
    (Q : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (f := f) (x := x)

/-- Twice continuous differentiability makes the gradient continuously differentiable. -/
private lemma contDiffAt_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (gradient f) x := by
  -- Differentiate once, then compose with the inverse Riesz isometry.
  unfold gradient
  exact (hf.fderiv_right (m := 1) (by norm_num)).continuousLinearMap_comp
    ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E)

/-- The Hessian transforms by orthogonal conjugation under a change of frame. -/
theorem hessian_comp_linearIsometry (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (Q : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) (hf : ContDiffAt ℝ 2 f (Q x)) :
    hessian (fun y ↦ f (Q y)) x =
      (Q.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘L
        hessian f (Q x) ∘L
          (Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  -- The pointwise gradient covariance holds throughout a neighborhood of `x`.
  have hgrad :
      gradient (fun y ↦ f (Q y)) =ᶠ[nhds x]
        Q.symm ∘ gradient f ∘ Q := by
    filter_upwards [Q.continuousAt.eventually (hf.eventually (by simp))] with y hy
    simpa only [Function.comp_apply] using
      gradient_comp_linearIsometry f Q y
  -- Differentiate that local identity, then use the two linear-isometry derivative rules.
  unfold hessian
  calc
    fderiv ℝ (gradient (fun y ↦ f (Q y))) x =
        fderiv ℝ (Q.symm ∘ gradient f ∘ Q) x := hgrad.fderiv_eq
    _ = (Q.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘L
        fderiv ℝ (gradient f ∘ Q) x := LinearIsometryEquiv.comp_fderiv Q.symm
    _ = (Q.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) ∘L
        fderiv ℝ (gradient f) (Q x) ∘L
          (Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
      have hright : fderiv ℝ (gradient f ∘ Q) x =
          fderiv ℝ (gradient f) (Q x) ∘L
            (Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
        exact (Q : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
          EuclideanSpace ℝ (Fin 2)).comp_right_fderiv
      rw [hright]

/-- The gradient of half the squared distance plus a differentiable function is the
displacement vector plus the function's gradient. -/
private lemma gradient_halfNormSq_sub_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (C : E) (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    gradient (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 + f y) x =
      x - C + gradient f x := by
  -- Build the derivative of the squared norm and add the derivative represented by `∇f`.
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
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      InnerProductSpace.toDual_apply_apply, inner_add_left,
      innerSL_apply_apply, one_div, smul_eq_mul]
    ring
  have hderiv := hsum.congr_fderiv hRiesz
  apply hderiv.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y ↦ by simp [smul_eq_mul])

/-- The Hessian of half the squared distance from `C` plus `Ψ` is the identity operator plus
the Hessian of `Ψ`. -/
theorem hessian_sqNorm_add (C : EuclideanSpace ℝ (Fin 2))
    (Ψ : EuclideanSpace ℝ (Fin 2) → ℝ) (z : EuclideanSpace ℝ (Fin 2))
    (hΨ : ContDiffAt ℝ 2 Ψ z) :
    hessian (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) z = 1 + hessian Ψ z := by
  -- The explicit gradient formula holds on a neighborhood supplied by `C²` regularity.
  have finiteOrder :
      (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hgrad :
      gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) =ᶠ[nhds z]
        fun x ↦ x - C + gradient Ψ x := by
    filter_upwards [hΨ.eventually finiteOrder] with x hx
    exact gradient_halfNormSq_sub_add C Ψ x (hx.differentiableAt two_ne_zero)
  -- Differentiate the local formula; the displacement contributes the identity operator.
  unfold hessian
  calc
    fderiv ℝ (gradient (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x)) z =
        fderiv ℝ (fun x ↦ x - C + gradient Ψ x) z := hgrad.fderiv_eq
    _ = fderiv ℝ (fun x ↦ x - C) z + fderiv ℝ (gradient Ψ) z :=
      fderiv_fun_add (differentiableAt_id.sub_const C)
        ((contDiffAt_gradient hΨ).differentiableAt one_ne_zero)
    _ = 1 + fderiv ℝ (gradient Ψ) z := by
      rw [fderiv_sub_const, fderiv_fun_id, ← ContinuousLinearMap.one_def]

/-- A norm bound on the perturbation Hessian bounds the Hessian matrix of half the squared
distance plus the perturbation between the corresponding scalar identity matrices. -/
theorem hessianMatrix_sqNorm_add_bounds_of_norm_le (C : EuclideanSpace ℝ (Fin 2))
    (Ψ : EuclideanSpace ℝ (Fin 2) → ℝ) (z : EuclideanSpace ℝ (Fin 2)) (η : ℝ)
    (hΨ : ContDiffAt ℝ 2 Ψ z) (h_norm : ‖hessian Ψ z‖ ≤ η) :
    (hessianMatrix (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) z -
      (1 - η) • 1).PosSemidef ∧
    ((1 + η) • 1 -
      hessianMatrix (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) z).PosSemidef := by
  -- The total function is `C²`, so both matrix Loewner characterizations apply.
  have hsub : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) ↦ x - C) z :=
    contDiffAt_id.sub contDiffAt_const
  have hquad : ContDiffAt ℝ 2
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2) z := by
    simpa only [smul_eq_mul] using
      ((hsub.norm_sq (𝕜 := ℝ)).const_smul (1 / 2 : ℝ))
  have htotal : ContDiffAt ℝ 2
      (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) z := hquad.add hΨ
  have hbounds := ContinuousLinearMap.inner_apply_bounds_of_norm_le
    (hessian Ψ z) η h_norm
  constructor
  · rw [lowerBound_hessianMatrix_iff _ _ _ htotal]
    intro v
    -- Insert `Hessian(total) = I + Hessian(Ψ)` and use the lower norm bound.
    rw [hessian_sqNorm_add C Ψ z hΨ, add_apply,
      one_apply_eq_self, inner_add_left, real_inner_self_eq_norm_sq]
    linarith [((hbounds v).1)]
  · rw [upperBound_hessianMatrix_iff _ _ _ htotal]
    intro v
    -- The upper norm bound gives the other scalar identity shift.
    rw [hessian_sqNorm_add C Ψ z hΨ, add_apply,
      one_apply_eq_self, inner_add_left, real_inner_self_eq_norm_sq]
    linarith [((hbounds v).2)]

end EuclideanPlane
