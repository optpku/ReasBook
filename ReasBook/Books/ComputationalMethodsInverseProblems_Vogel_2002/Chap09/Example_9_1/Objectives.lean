/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Diagonal

public section

noncomputable section

open scoped BigOperators

/-! Reusable Example 9.1 objective-function backend.

This item-owned foundation module contains the Chapter 9 objective-function
owners and displayed derivative formulas reused by later files without
importing the full source-facing `Book.Ch9.Example_9_1` item.
-/

/-- The shifted Poisson-likelihood functional with the formula displayed in
`(9.5)`, using data truncation `d̄_i = max {d_i, 0}` and variance shift `σ2`. -/
def example91LikelihoodFunctional (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun f ↦
    (∑ i : Fin n, Matrix.toEuclideanLin K f i + σ2) -
      ∑ i : Fin n, (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) +
        (α / 2) * ‖f‖ ^ 2

/-- The defining formula for `example91LikelihoodFunctional`. -/
theorem example91LikelihoodFunctional_def (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 α : ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    example91LikelihoodFunctional n K d σ2 α f =
      (∑ i : Fin n, Matrix.toEuclideanLin K f i + σ2) -
        ∑ i : Fin n, (max (d i) 0 + σ2) * Real.log (Matrix.toEuclideanLin K f i + σ2) +
          (α / 2) * ‖f‖ ^ 2 := by
  simp [example91LikelihoodFunctional]

/-- The diagonal matrix `D(f)` from `(9.8)` for the shifted likelihood
Hessian. -/
def example91LikelihoodDiagonal (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 : ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal
    (fun i ↦ (max (d i) 0 + σ2) / (Matrix.toEuclideanLin K f i + σ2) ^ 2)

/-- The matrix `D(f)` from `(9.8)` is diagonal with entries
`(d̄_i + σ2) / ([K f]_i + σ2)^2`. -/
theorem example91LikelihoodDiagonal_def (n : ℕ) (K : Matrix (Fin n) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (σ2 : ℝ) (f : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    example91LikelihoodDiagonal n K d σ2 f i j =
      if i = j then
        (max (d i) 0 + σ2) / (Matrix.toEuclideanLin K f i + σ2) ^ 2
      else 0 := by
  by_cases h : i = j
  · simp [example91LikelihoodDiagonal, h]
  · simp [example91LikelihoodDiagonal, h]

/-- Helper for Example 9.1-extra-1: the Fréchet derivative of the shifted
likelihood functional applied to a direction `h` has the displayed
Poisson-likelihood form. -/
theorem example91LikelihoodFunctional_fderiv_apply (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 α : ℝ) (f h : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    fderiv ℝ (example91LikelihoodFunctional n K d σ2 α) f h =
      ∑ i : Fin n,
        ((Matrix.toEuclideanLin K f i - max (d i) 0) /
            (Matrix.toEuclideanLin K f i + σ2)) *
          Matrix.toEuclideanLin K h i +
        α * inner ℝ f h := by
  let coordCLM : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun i ↦ (EuclideanSpace.proj i).comp (Matrix.toEuclideanLin K).toContinuousLinearMap
  let arg : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x ↦ coordCLM i x + σ2
  let weight : Fin n → ℝ := fun i ↦ max (d i) 0 + σ2
  let coeff : Fin n → ℝ :=
    fun i ↦ (Matrix.toEuclideanLin K f i - max (d i) 0) / (Matrix.toEuclideanLin K f i + σ2)
  have harg :
      ∀ i : Fin n, HasFDerivAt (arg i) (coordCLM i) f := by
    intro i
    simpa [arg, coordCLM] using ((coordCLM i).hasFDerivAt.add_const σ2)
  have hterm :
      ∀ i : Fin n,
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ coordCLM i x - weight i * Real.log (arg i x))
          (coeff i • coordCLM i) f := by
    intro i
    have hlog :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ Real.log (arg i x))
          ((arg i f)⁻¹ • coordCLM i) f := by
      exact (harg i).log (by simpa [arg, coordCLM] using (hpos i).ne')
    have hscaled :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ weight i * Real.log (arg i x))
          (weight i • ((arg i f)⁻¹ • coordCLM i)) f := by
      simpa [weight] using hlog.const_mul (weight i)
    have hsub :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ coordCLM i x - weight i * Real.log (arg i x))
          (coordCLM i - weight i • ((arg i f)⁻¹ • coordCLM i)) f :=
      (coordCLM i).hasFDerivAt.sub hscaled
    have hderiv :
        coordCLM i - weight i • ((arg i f)⁻¹ • coordCLM i) = coeff i • coordCLM i := by
      ext x
      dsimp [arg, weight, coeff, coordCLM]
      simp only [sub_apply, smul_apply, smul_eq_mul]
      have hne : σ2 + K.mulVec f.ofLp i ≠ 0 := by
        simpa [add_comm] using (hpos i).ne'
      have hσ :
          K.mulVec x.ofLp i - K.mulVec x.ofLp i * σ2 * (σ2 + K.mulVec f.ofLp i)⁻¹ =
            K.mulVec x.ofLp i * K.mulVec f.ofLp i * (σ2 + K.mulVec f.ofLp i)⁻¹ := by
        apply mul_right_cancel₀ hne
        field_simp [hne]
        ring
      calc
        K.mulVec x.ofLp i -
            (max (d.ofLp i) 0 + σ2) * ((K.mulVec f.ofLp i + σ2)⁻¹ * K.mulVec x.ofLp i)
            =
          -(K.mulVec x.ofLp i * max (d.ofLp i) 0 * (σ2 + K.mulVec f.ofLp i)⁻¹) +
            (K.mulVec x.ofLp i - K.mulVec x.ofLp i * σ2 * (σ2 + K.mulVec f.ofLp i)⁻¹) := by
              ring
        _ =
          -(K.mulVec x.ofLp i * max (d.ofLp i) 0 * (σ2 + K.mulVec f.ofLp i)⁻¹) +
            K.mulVec x.ofLp i * K.mulVec f.ofLp i * (σ2 + K.mulVec f.ofLp i)⁻¹ := by
              rw [hσ]
        _ =
          ((K.mulVec f.ofLp i - max (d.ofLp i) 0) / (K.mulVec f.ofLp i + σ2)) *
            K.mulVec x.ofLp i := by
              have hsum : K.mulVec f.ofLp i + σ2 = σ2 + K.mulVec f.ofLp i := by ring
              rw [hsum]
              field_simp [hne]
              ring
    simpa [hderiv] using hsub
  have hsum :
      HasFDerivAt
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          ∑ i : Fin n, (coordCLM i x - weight i * Real.log (arg i x)))
        (∑ i : Fin n, coeff i • coordCLM i) f := by
    exact HasFDerivAt.fun_sum fun i _ ↦ hterm i
  have hpenNorm :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ 2)
        (2 • innerSL ℝ f) f := by
    simpa using (hasStrictFDerivAt_norm_sq f).hasFDerivAt
  have hpenAlpha :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ α * ‖x‖ ^ 2)
        (α • (2 • innerSL ℝ f)) f := by
    simpa using hpenNorm.const_mul α
  have hpen :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ (α / 2) * ‖x‖ ^ 2)
        (α • innerSL ℝ f) f := by
    have hpenHalf :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ α * ‖x‖ ^ 2 * (1 / 2 : ℝ))
          ((1 / 2 : ℝ) • (α • (2 • innerSL ℝ f))) f :=
      hpenAlpha.mul_const (1 / 2 : ℝ)
    have hpenHalf' :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ α * ‖x‖ ^ 2 * (1 / 2 : ℝ))
          (α • innerSL ℝ f) f := by
      refine hpenHalf.congr_fderiv ?_
      ext x
      simp [innerSL_apply_apply]
      ring_nf
    refine hpenHalf'.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by
      ring
  have hJ :
      HasFDerivAt (example91LikelihoodFunctional n K d σ2 α)
        ((∑ i : Fin n, coeff i • coordCLM i) + α • innerSL ℝ f) f := by
    refine ((hsum.add hpen).add_const σ2).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [example91LikelihoodFunctional_def]
      simp [arg, weight, coordCLM, EuclideanSpace.proj, Finset.sum_sub_distrib]
      ring
  rw [hJ.fderiv]
  simp [coordCLM, coeff, innerSL_apply_apply, EuclideanSpace.proj]

/-- The gradient formula `(9.6)` for the shifted likelihood functional, under
the positivity condition required by the log terms. -/
theorem gradient_example91LikelihoodFunctional (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 α : ℝ) (f : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    gradient (example91LikelihoodFunctional n K d σ2 α) f =
      Matrix.toEuclideanLin K.transpose
        (WithLp.toLp 2
          (fun i ↦
            (Matrix.toEuclideanLin K f i - max (d i) 0) /
              (Matrix.toEuclideanLin K f i + σ2))) +
        α • f := by
  let coeff : Fin n → ℝ :=
    fun i ↦
      (Matrix.toEuclideanLin K f i - max (d i) 0) /
        (Matrix.toEuclideanLin K f i + σ2)
  have hAdj :
      LinearMap.adjoint (Matrix.toEuclideanLin K) = Matrix.toEuclideanLin K.transpose := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
  rw [toDual_gradient]
  ext h
  calc
    fderiv ℝ (example91LikelihoodFunctional n K d σ2 α) f h
        = ∑ i : Fin n, coeff i * Matrix.toEuclideanLin K h i + α * inner ℝ f h := by
            simpa [coeff] using
              example91LikelihoodFunctional_fderiv_apply n K d σ2 α f h hpos
    _ = inner ℝ (WithLp.toLp 2 coeff) (Matrix.toEuclideanLin K h) + α * inner ℝ f h := by
          simp [coeff, PiLp.inner_apply, mul_comm]
    _ = inner ℝ (Matrix.toEuclideanLin K.transpose (WithLp.toLp 2 coeff)) h +
          α * inner ℝ f h := by
          rw [← hAdj]
          simpa using (congrArg
            (fun t ↦ t + α * inner ℝ f h)
            (LinearMap.adjoint_inner_left
              (A := Matrix.toEuclideanLin K) (x := h) (y := WithLp.toLp 2 coeff))).symm
    _ = inner ℝ
          (Matrix.toEuclideanLin K.transpose (WithLp.toLp 2 coeff) + α • f) h := by
          rw [inner_add_left, real_inner_smul_left]

/-- The Hessian formula `(9.7)` for the shifted likelihood functional, under
the positivity condition required by the log terms. -/
theorem hessian_example91LikelihoodFunctional (n : ℕ)
    (K : Matrix (Fin n) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin n))
    (σ2 α : ℝ) (f h : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ i : Fin n, 0 < Matrix.toEuclideanLin K f i + σ2) :
    hessian (example91LikelihoodFunctional n K d σ2 α) f h =
      Matrix.toEuclideanLin
        (K.transpose * example91LikelihoodDiagonal n K d σ2 f * K +
          α • (1 : Matrix (Fin n) (Fin n) ℝ)) h := by
  let J : EuclideanSpace ℝ (Fin n) → ℝ :=
    example91LikelihoodFunctional n K d σ2 α
  let coordCLM : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun i ↦ (EuclideanSpace.proj i).comp (Matrix.toEuclideanLin K).toContinuousLinearMap
  let arg : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x ↦ coordCLM i x + σ2
  let weight : Fin n → ℝ := fun i ↦ max (d i) 0 + σ2
  let coeff : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x ↦ 1 - weight i * (arg i x)⁻¹
  let coeffPiDeriv :
      EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ ((weight i) / (arg i f) ^ 2) • coordCLM i
  let coeffDeriv :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap).comp coeffPiDeriv
  let hessMatrixOp : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Matrix.toEuclideanLin
      (K.transpose * example91LikelihoodDiagonal n K d σ2 f * K +
        α • (1 : Matrix (Fin n) (Fin n) ℝ))).toContinuousLinearMap
  let gradRep : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x ↦
      Matrix.toEuclideanLin K.transpose ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ coeff i x) +
        α • x
  let toDualCLM :
      EuclideanSpace ℝ (Fin n) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toLinearIsometry.toContinuousLinearMap)
  have harg :
      ∀ i : Fin n, HasFDerivAt (arg i) (coordCLM i) f := by
    intro i
    simpa [arg, coordCLM] using ((coordCLM i).hasFDerivAt.add_const σ2)
  have hcoeff :
      ∀ i : Fin n,
        HasFDerivAt (coeff i) (((weight i) / (arg i f) ^ 2) • coordCLM i) f := by
    intro i
    have harg_ne : arg i f ≠ 0 := (hpos i).ne'
    have hinvRaw :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ (arg i x)⁻¹)
          ((ContinuousLinearMap.toSpanSingleton ℝ (-((arg i f) ^ 2)⁻¹)).comp (coordCLM i)) f :=
      (hasFDerivAt_inv harg_ne).comp f (harg i)
    have hinv :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ (arg i x)⁻¹)
          ((-((arg i f) ^ 2)⁻¹) • coordCLM i) f := by
      convert hinvRaw using 1
      ext x
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
    have hscaled :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ weight i * (arg i x)⁻¹)
          (weight i • (((-((arg i f) ^ 2)⁻¹)) • coordCLM i)) f := by
      simpa [smul_eq_mul] using hinv.const_mul (weight i)
    have hsub :
        HasFDerivAt (coeff i)
          ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) -
            weight i • (((-((arg i f) ^ 2)⁻¹)) • coordCLM i)) f := by
      have hsubRaw :
          HasFDerivAt
            (fun x : EuclideanSpace ℝ (Fin n) ↦ 1 - weight i * (arg i x)⁻¹)
            ((0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) -
              weight i • (((-((arg i f) ^ 2)⁻¹)) • coordCLM i)) f :=
        (hasFDerivAt_const (1 : ℝ) f).sub hscaled
      simpa [coeff] using hsubRaw
    have hderiv :
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) -
            weight i • (((-((arg i f) ^ 2)⁻¹)) • coordCLM i) =
          ((weight i) / (arg i f) ^ 2) • coordCLM i := by
      ext x
      simp [smul_eq_mul]
      ring_nf
    exact hsub.congr_fderiv hderiv
  have hcoeffPi :
      HasFDerivAt (fun x i ↦ coeff i x) coeffPiDeriv f := by
    simpa [coeffPiDeriv] using hasFDerivAt_pi.2 hcoeff
  have hcoeffVec :
      HasFDerivAt
        (fun x ↦ (EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ coeff i x)
        coeffDeriv f := by
    exact
      ((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp f hcoeffPi)
  have hgradRep :
      HasFDerivAt gradRep hessMatrixOp f := by
    have hlinear :
        HasFDerivAt
          (fun x ↦
            Matrix.toEuclideanLin K.transpose
              ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ coeff i x))
          (((Matrix.toEuclideanLin K.transpose).toContinuousLinearMap).comp coeffDeriv) f := by
      exact
        ((Matrix.toEuclideanLin K.transpose).toContinuousLinearMap.hasFDerivAt.comp f
          hcoeffVec)
    have halpha :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦ α • x)
          (α • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) f := by
      exact
        ((α • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt :
          HasFDerivAt
            (fun x : EuclideanSpace ℝ (Fin n) ↦ α • x)
            (α • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) f)
    have hsum :
        HasFDerivAt gradRep
          (((Matrix.toEuclideanLin K.transpose).toContinuousLinearMap).comp coeffDeriv +
            α • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) f := by
      exact hlinear.add halpha
    have hOp :
        ((Matrix.toEuclideanLin K.transpose).toContinuousLinearMap).comp coeffDeriv +
            α • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) =
          hessMatrixOp := by
      ext x i
      simp [hessMatrixOp, coeffDeriv, coeffPiDeriv, coordCLM, arg, weight,
        example91LikelihoodDiagonal, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        ContinuousLinearMap.comp_apply, smul_eq_mul]
      have hmul :=
        congrFun
          (Matrix.mulVec_mulVec x.ofLp K.transpose
            ((Matrix.diagonal
                fun i ↦ (max (d i) 0 + σ2) / (Matrix.toEuclideanLin K f i + σ2) ^ 2) * K))
          i
      simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hsum.congr_fderiv hOp
  have hposNear :
      ∀ᶠ x : EuclideanSpace ℝ (Fin n) in nhds f, ∀ i : Fin n, 0 < arg i x := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (harg i).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (hpos i))
  have hlocalEq :
      fderiv ℝ J =ᶠ[nhds f] fun x ↦ toDualCLM (gradRep x) := by
    refine hposNear.mono ?_
    intro x hx
    have hcoeffEq :
        (fun i ↦ coeff i x) =
          (fun i ↦
            (Matrix.toEuclideanLin K x i - max (d i) 0) /
              (Matrix.toEuclideanLin K x i + σ2)) := by
      funext i
      have hne : Matrix.toEuclideanLin K x i + σ2 ≠ 0 := (hx i).ne'
      dsimp [coeff, arg, weight]
      simp [coordCLM]
      have hone :
          (1 : ℝ) =
            (σ2 + K.mulVec x.ofLp i) * (σ2 + K.mulVec x.ofLp i)⁻¹ := by
        have hsum : σ2 + K.mulVec x.ofLp i = K.mulVec x.ofLp i + σ2 := by ring
        simpa [div_eq_mul_inv, hsum] using (div_self hne).symm
      rw [hone]
      ring
    have hvecEq :
        ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ coeff i x) =
          WithLp.toLp 2
            (fun i ↦
              (Matrix.toEuclideanLin K x i - max (d i) 0) /
                (Matrix.toEuclideanLin K x i + σ2)) := by
      simpa using congrArg ((EuclideanSpace.equiv (Fin n) ℝ).symm) hcoeffEq
    calc
      fderiv ℝ J x =
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (gradient J x) := by
            rw [toDual_gradient]
      _ =
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
            (Matrix.toEuclideanLin K.transpose
              (WithLp.toLp 2
                (fun i ↦
                  (Matrix.toEuclideanLin K x i - max (d i) 0) /
                    (Matrix.toEuclideanLin K x i + σ2))) + α • x) := by
            congr 1
            simpa [J] using gradient_example91LikelihoodFunctional n K d σ2 α x hx
      _ =
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (gradRep x) := by
            congr 1
            simpa [gradRep] using
              congrArg
                (fun v : EuclideanSpace ℝ (Fin n) ↦
                  Matrix.toEuclideanLin K.transpose v + α • x)
                hvecEq |>.symm
  have hsecondRep :
      HasFDerivAt (fun x ↦ fderiv ℝ J x) (toDualCLM.comp hessMatrixOp) f :=
    (hlocalEq.hasFDerivAt_iff).2
      (toDualCLM.hasFDerivAt.comp f hgradRep)
  apply ext_inner_right ℝ
  intro k
  rw [hessian_inner, hsecondRep.fderiv, ContinuousLinearMap.comp_apply]
  simp [toDualCLM, hessMatrixOp, inner_add_left, real_inner_smul_left]
  rw [innerSL_apply_apply, innerSL_apply_apply]
