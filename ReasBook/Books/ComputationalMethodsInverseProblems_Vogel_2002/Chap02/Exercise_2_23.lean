/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_36

public section

noncomputable section

universe u v

variable {H1 : Type u} [NormedAddCommGroup H1] [InnerProductSpace ℝ H1] [CompleteSpace H1]
variable {H2 : Type v} [NormedAddCommGroup H2] [InnerProductSpace ℝ H2] [CompleteSpace H2]

/-- Exercise 2.23. For Example 2.36, Definition 2.40 identifies the Hessian of
the Hilbert-space Tikhonov functional with the constant operator
`K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1`. -/
theorem tikhonovFunctional_hessian_eq_operatorForm (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ)
    (f : H1) :
    hessian (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α) f =
      K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1 := by
  let A : H1 →L[ℝ] H1 := K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1
  have hfderiv_eq :
      fderiv ℝ (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α) =
        fun x ↦
          (InnerProductSpace.toDual ℝ H1) (A x) -
            (InnerProductSpace.toDual ℝ H1) (K.adjoint g) := by
    funext x
    simpa [A] using
      tikhonovFunctional_fderiv_eq_toDual_operatorForm K g α x
  have hsecond :
      fderiv ℝ
          (fderiv ℝ (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α)) f =
        ((InnerProductSpace.toDual ℝ H1).toLinearIsometry.toContinuousLinearMap).comp A := by
    have hLinear :
        HasFDerivAt (fun x ↦ (InnerProductSpace.toDual ℝ H1) (A x))
          (((InnerProductSpace.toDual ℝ H1).toLinearIsometry.toContinuousLinearMap).comp A) f := by
      exact
        ((InnerProductSpace.toDual ℝ H1).toLinearIsometry.toContinuousLinearMap).hasFDerivAt.comp
          f A.hasFDerivAt
    have hDual :
        HasFDerivAt
          (fun x ↦ (InnerProductSpace.toDual ℝ H1) (A x) -
            (InnerProductSpace.toDual ℝ H1) (K.adjoint g))
          (((InnerProductSpace.toDual ℝ H1).toLinearIsometry.toContinuousLinearMap).comp A) f := by
      simpa using hLinear.sub_const ((InnerProductSpace.toDual ℝ H1) (K.adjoint g))
    rw [hfderiv_eq]
    exact hDual.fderiv
  ext h
  apply ext_inner_right ℝ
  intro k
  rw [hessian_inner, hsecond]
  rw [ContinuousLinearMap.comp_apply]
  change inner ℝ (A h) k =
    inner ℝ ((ContinuousLinearMap.adjoint K ∘SL K + α • ContinuousLinearMap.id ℝ H1) h) k
  rfl
