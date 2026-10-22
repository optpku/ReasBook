/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

open Matrix
open scoped BigOperators

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "residualCoords" => (EuclideanSpace.equiv (Fin m) ℝ)

-- Domain sampling for this remark:
-- * primary domain: least-squares quasi-Newton secant equations
-- * sampled canonical declarations in the same domain:
--   `satisfiesQuasiNewtonEquationHessianForm` from Chapter 5,
--   and `residualJacobianMatrix`, `leastSquaresGradient`,
--   `leastSquaresCorrectionMatrix`, `gaussNewtonNormalMatrix` from Chapter 7
-- * best owner abstraction: the Chapter 7 least-squares owners on
--   `EuclideanSpace ℝ (Fin n)` together with the Chapter 5 Hessian-form secant owner
-- * layer choice here:
--   (1) a bridge/view theorem from the source weighted Hessian approximation to the canonical
--       secant owner;
--   (2) a source-facing algebraic consequence stated directly on the Chapter 7 owners
-- * primitive data here: the residual map `r`, the points `xk`, `xk1`, the iterate
--   displacement `xk1 - xk`, the step `s` in (2), the aggregated approximation `Bnext`,
--   and the component Hessian approximants
-- * derived API here: the secant right-hand sides built from the residual Jacobian, the
--   least-squares gradient, and the Gauss-Newton normal matrix

/-- Helper for Chapter07 Remark 7.5-extra-1: pairing `J(x)ᵀ w` with a test vector agrees with
pairing `w` against the residual derivative in that direction. -/
private lemma innerTransposeJacobian_apply_vec
    (r : Point → Residual) (x : Point) (w : Residual) (y : Point) :
    inner ℝ (((residualJacobianMatrix r x)ᵀ).toEuclideanLin w) y =
      inner ℝ w ((fderiv ℝ r x) y) := by
  let pointBasis := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let residualBasis := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let jacobian : JacobianMatrix := residualJacobianMatrix r x
  -- Rewrite Euclidean coordinates through the canonical basis representations once.
  have hreprPoint (z : Point) : pointBasis.repr z = z.ofLp := by
    ext i
    simp [pointBasis]
  have hreprResidual (z : Residual) : residualBasis.repr z = z.ofLp := by
    ext i
    simp [residualBasis]
  have hderivCoords : ((fderiv ℝ r x) y).ofLp = jacobian *ᵥ y.ofLp := by
    rw [← hreprResidual, ← hreprPoint]
    simpa [jacobian, residualJacobianMatrix] using
      (LinearMap.toMatrix_mulVec_repr
        pointBasis residualBasis (fderiv ℝ r x).toLinearMap y).symm
  have htransposeCoords :
      (((jacobianᵀ).toEuclideanLin w).ofLp) = jacobianᵀ *ᵥ w.ofLp := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← hreprPoint, ← hreprResidual]
    simpa using
      (LinearMap.toMatrix_mulVec_repr residualBasis pointBasis
        ((Matrix.toLin residualBasis pointBasis) jacobianᵀ) w).symm
  -- Convert both inner products to coordinate dot-products and use `Aᵀ`.
  calc
    inner ℝ (((residualJacobianMatrix r x)ᵀ).toEuclideanLin w) y
        = y.ofLp ⬝ᵥ (((residualJacobianMatrix r x)ᵀ).toEuclideanLin w).ofLp := by
            simp [EuclideanSpace.inner_eq_star_dotProduct]
    _ = y.ofLp ⬝ᵥ (jacobianᵀ *ᵥ w.ofLp) := by
          rw [htransposeCoords]
    _ = (jacobian *ᵥ y.ofLp) ⬝ᵥ w.ofLp := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = ((fderiv ℝ r x) y).ofLp ⬝ᵥ w.ofLp := by
          rw [hderivCoords]
    _ = inner ℝ w ((fderiv ℝ r x) y) := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Helper for Chapter07 Remark 7.5-extra-1: differentiability of the residual map identifies
the gradient of one residual coordinate with the corresponding transpose-Jacobian basis vector. -/
private theorem residualCoordinateGradient_eq_transposeJacobianBasis
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hr : DifferentiableAt ℝ r x) :
    gradient (fun y : Point ↦ residualCoords (r y) i) x =
      ((residualJacobianMatrix r x)ᵀ).toEuclideanLin
        (EuclideanSpace.basisFun (Fin m) ℝ i) := by
  let coord : Residual →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      ((EuclideanSpace.equiv (Fin m) ℝ :
        Residual ≃L[ℝ] (Fin m → ℝ)).toContinuousLinearMap)
  have hcoord :
      HasFDerivAt (fun y : Point ↦ residualCoords (r y) i)
        (coord.comp (fderiv ℝ r x)) x := by
    -- Differentiate the scalar residual coordinate by composing with the coordinate projection.
    have hcoord' : HasFDerivAt (coord ∘ r) (coord.comp (fderiv ℝ r x)) x :=
      coord.hasFDerivAt.comp x hr.hasFDerivAt
    have hfun : (fun y : Point ↦ residualCoords (r y) i) = coord ∘ r := by
      funext y
      simp [coord, Function.comp]
    rw [hfun]
    exact hcoord'
  have hdual :
      coord.comp (fderiv ℝ r x) =
        (InnerProductSpace.toDual ℝ Point)
          (((residualJacobianMatrix r x)ᵀ).toEuclideanLin
            (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
    ext y
    -- Compare both linear functionals through the Euclidean basis coordinate `i`.
    calc
      coord ((fderiv ℝ r x) y) = residualCoords ((fderiv ℝ r x) y) i := by
        simp [coord]
      _ = inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ i) ((fderiv ℝ r x) y) := by
        symm
        simpa using
          (EuclideanSpace.basisFun_inner (ι := Fin m) (𝕜 := ℝ) ((fderiv ℝ r x) y) i)
      _ = inner ℝ
            (((residualJacobianMatrix r x)ᵀ).toEuclideanLin
              (EuclideanSpace.basisFun (Fin m) ℝ i)) y := by
            symm
            exact innerTransposeJacobian_apply_vec
              (r := r) (x := x) (w := EuclideanSpace.basisFun (Fin m) ℝ i) (y := y)
  have hgrad :
      HasGradientAt (fun y : Point ↦ residualCoords (r y) i)
        (((residualJacobianMatrix r x)ᵀ).toEuclideanLin
          (EuclideanSpace.basisFun (Fin m) ℝ i)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hcoord.congr_fderiv hdual
  exact hgrad.gradient

/-- Helper for Chapter07 Remark 7.5-extra-1: applying `J(x)ᵀ` to a residual-space vector is the
residual-coordinate weighted sum of the corresponding scalar-coordinate gradients. -/
private theorem transposeJacobian_apply_eq_residualCoordGradientSum
    (r : Point → Residual) (x : Point) (w : Residual)
    (hr : DifferentiableAt ℝ r x) :
    ((residualJacobianMatrix r x)ᵀ).toEuclideanLin w =
      ∑ i : Fin m,
        residualCoords w i • gradient (fun y : Point ↦ residualCoords (r y) i) x := by
  let coeff : Fin m → ℝ := residualCoords w
  have hResidualExpand :
      w = ∑ i : Fin m, coeff i • EuclideanSpace.basisFun (Fin m) ℝ i := by
    -- Expand the residual vector in the standard Euclidean basis.
    simpa [coeff] using ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr w).symm
  calc
    ((residualJacobianMatrix r x)ᵀ).toEuclideanLin w
        = ((residualJacobianMatrix r x)ᵀ).toEuclideanLin
            (∑ i : Fin m, coeff i • EuclideanSpace.basisFun (Fin m) ℝ i) := by
              rw [hResidualExpand]
    _ = ∑ i : Fin m,
          coeff i •
            ((residualJacobianMatrix r x)ᵀ).toEuclideanLin
              (EuclideanSpace.basisFun (Fin m) ℝ i) := by
            simp
    _ = ∑ i : Fin m,
          coeff i • gradient (fun y : Point ↦ residualCoords (r y) i) x := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [residualCoordinateGradient_eq_transposeJacobianBasis
              (r := r) (x := x) (i := i) hr]

/-- Helper for Chapter07 Remark 7.5-extra-1: subtracting two transpose-Jacobian Euclidean
actions is the same as acting by the transpose of the matrix difference. -/
private theorem transposeToEuclideanLin_sub_apply
    (A B : JacobianMatrix) (w : Residual) :
    (Aᵀ).toEuclideanLin w - (Bᵀ).toEuclideanLin w = ((A - B)ᵀ).toEuclideanLin w := by
  apply WithLp.ofLp_injective 2
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Chapter07 Remark 7.5-extra-1 (1): if `Bₖ₊₁ = ∑ i, r_i(xₖ₊₁) • (H_i)ₖ₊₁`, the residual map is
differentiable at `xₖ` and `xₖ₊₁`, and each component secant approximation satisfies
`(H_i)ₖ₊₁ (xₖ₊₁ - xₖ) = ∇r_i(xₖ₊₁) - ∇r_i(xₖ)`, then `Bₖ₊₁` satisfies the Hessian-form
quasi-Newton equation with secant vector `(J(xₖ₊₁) - J(xₖ))ᵀ r(xₖ₊₁)`. -/
theorem leastSquaresSecondOrderApproximation_secant
    (r : Point → Residual) (xk xk1 : Point)
    (Bnext : MatrixN) (componentHessians : Fin m → MatrixN)
    (hxk : DifferentiableAt ℝ r xk) (hxk1 : DifferentiableAt ℝ r xk1)
    (hB :
      Bnext = ∑ i : Fin m, residualCoords (r xk1) i • componentHessians i)
    (hHi :
      ∀ i : Fin m,
        (componentHessians i).toEuclideanLin (xk1 - xk) =
          gradient (fun y : Point ↦ residualCoords (r y) i) xk1 -
            gradient (fun y : Point ↦ residualCoords (r y) i) xk) :
    satisfiesQuasiNewtonEquationHessianForm
      Bnext.toEuclideanLin
      (xk1 - xk)
      (((residualJacobianMatrix r xk1 - residualJacobianMatrix r xk)ᵀ).toEuclideanLin
        (r xk1)) := by
  rw [satisfiesQuasiNewtonEquationHessianForm]
  -- Route correction: expand the weighted secant model for `Bnext`, apply each component secant
  -- equation, and refold the resulting weighted gradient sums back into transpose-Jacobian terms.
  calc
    Bnext.toEuclideanLin (xk1 - xk)
        = (∑ i : Fin m, residualCoords (r xk1) i • componentHessians i).toEuclideanLin
            (xk1 - xk) := by
              rw [hB]
    _ = ∑ i : Fin m,
          residualCoords (r xk1) i • (componentHessians i).toEuclideanLin (xk1 - xk) := by
            simp
    _ = ∑ i : Fin m,
          residualCoords (r xk1) i •
            (gradient (fun y : Point ↦ residualCoords (r y) i) xk1 -
              gradient (fun y : Point ↦ residualCoords (r y) i) xk) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hHi i]
    _ = ∑ i : Fin m,
          (residualCoords (r xk1) i • gradient (fun y : Point ↦ residualCoords (r y) i) xk1 -
            residualCoords (r xk1) i • gradient (fun y : Point ↦ residualCoords (r y) i) xk) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [smul_sub]
    _ = (∑ i : Fin m,
          residualCoords (r xk1) i •
            gradient (fun y : Point ↦ residualCoords (r y) i) xk1) -
        ∑ i : Fin m,
          residualCoords (r xk1) i •
            gradient (fun y : Point ↦ residualCoords (r y) i) xk := by
          rw [Finset.sum_sub_distrib]
    _ = ((residualJacobianMatrix r xk1)ᵀ).toEuclideanLin (r xk1) -
        ((residualJacobianMatrix r xk)ᵀ).toEuclideanLin (r xk1) := by
          rw [← transposeJacobian_apply_eq_residualCoordGradientSum
            (r := r) (x := xk1) (w := r xk1) hxk1]
          rw [← transposeJacobian_apply_eq_residualCoordGradientSum
            (r := r) (x := xk) (w := r xk1) hxk]
    _ = (((residualJacobianMatrix r xk1 - residualJacobianMatrix r xk)ᵀ).toEuclideanLin
          (r xk1)) := by
          -- Collapse the difference of transpose-Jacobian actions into a single matrix action.
          exact transposeToEuclideanLin_sub_apply
            (A := residualJacobianMatrix r xk1) (B := residualJacobianMatrix r xk)
            (w := r xk1)

/-- Chapter07 Remark 7.5-extra-1 (2): if
`(J(xₖ₊₁)ᵀ J(xₖ₊₁) + Bₖ₊₁) sₖ = ∇f(xₖ₊₁) - ∇f(xₖ)` for the Chapter 7 least-squares gradient
`∇f(x) = leastSquaresGradient r x`, then
`Bₖ₊₁ sₖ = ∇f(xₖ₊₁) - ∇f(xₖ) - J(xₖ₊₁)ᵀ J(xₖ₊₁) sₖ`. -/
theorem leastSquaresGradientDifferenceSecant_eq
    (r : Point → Residual) (xk xk1 s : Point) (Bnext : MatrixN)
    (hstep :
      (gaussNewtonNormalMatrix r xk1 + Bnext).toEuclideanLin s =
        leastSquaresGradient r xk1 - leastSquaresGradient r xk) :
    Bnext.toEuclideanLin s =
      leastSquaresGradient r xk1 - leastSquaresGradient r xk -
        (gaussNewtonNormalMatrix r xk1).toEuclideanLin s := by
  -- Subtract the Gauss-Newton contribution from the recorded mixed normal equation.
  apply WithLp.ofLp_injective 2
  have hstepOfLp := congrArg WithLp.ofLp hstep
  have hIsolated :=
    congrArg
      (fun z : Fin n → ℝ ↦ z - (gaussNewtonNormalMatrix r xk1).mulVec s.ofLp)
      hstepOfLp
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.add_mulVec, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using hIsolated

end
