/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

open Filter Matrix
open scoped BigOperators LeastSquares

section

variable {m n : ℕ}

-- Local declaration justification (source-local notation): this numbered item uses the
-- source's fixed Euclidean domain notation throughout and keeps the aliases local.
local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
local notation "residualCoords" => (EuclideanSpace.equiv (Fin m) ℝ)

/-- Helper for Chapter07 Notation 7.1-extra-2: pairing `J(x)ᵀ w` with a test vector agrees with
pairing `w` against the residual derivative in that direction. -/
private lemma innerTransposeJacobianApplyVec
    (r : Point → Residual) (x : Point) (w : Residual) (y : Point) :
    inner ℝ (((J[r](x))ᵀ).toEuclideanLin w) y =
      inner ℝ w ((fderiv ℝ r x) y) := by
  let pointBasis := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let residualBasis := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let jacobian : Matrix (Fin m) (Fin n) ℝ := J[r](x)
  -- Rewrite both Euclidean spaces once through their canonical basis coordinates.
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
  -- After moving to coordinates, this is the standard transpose identity.
  calc
    inner ℝ (((J[r](x))ᵀ).toEuclideanLin w) y
        = y.ofLp ⬝ᵥ (((J[r](x))ᵀ).toEuclideanLin w).ofLp := by
            simp [EuclideanSpace.inner_eq_star_dotProduct]
    _ = y.ofLp ⬝ᵥ (jacobianᵀ *ᵥ w.ofLp) := by
          rw [htransposeCoords]
    _ = (jacobian *ᵥ y.ofLp) ⬝ᵥ w.ofLp := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = ((fderiv ℝ r x) y).ofLp ⬝ᵥ w.ofLp := by
          rw [hderivCoords]
    _ = inner ℝ w ((fderiv ℝ r x) y) := by
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Helper for Chapter07 Notation 7.1-extra-2: differentiability of the residual map identifies
the canonical gradient of the least-squares objective with the source vector `J(x)ᵀ r(x)`. -/
private theorem leastSquaresObjectiveGradientEqGaussNewtonGradient
    (r : Point → Residual) (x : Point) (hr : DifferentiableAt ℝ r x) :
    gradient (nonlinearLeastSquaresObjective r) x = g[r](x) := by
  have hResidualDeriv : HasFDerivAt r (fderiv ℝ r x) x := hr.hasFDerivAt
  have hNormSq :
      HasFDerivAt (fun y : Point ↦ ‖r y‖ ^ (2 : ℕ))
        (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x) x := by
    -- Differentiate the squared residual norm before scaling by `1 / 2`.
    simpa using hResidualDeriv.norm_sq
  have hObjectiveRaw :
      HasFDerivAt (fun y : Point ↦ ((1 : ℝ) / 2) * ‖r y‖ ^ (2 : ℕ))
        (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x)) x := by
    simpa using hNormSq.const_mul ((1 / 2 : ℝ))
  have hObjectiveEq :
      nonlinearLeastSquaresObjective r = fun y : Point ↦ ((1 : ℝ) / 2) * ‖r y‖ ^ (2 : ℕ) := by
    ext y
    rw [nonlinearLeastSquaresObjective_eq_half_norm_sq]
  have hObjective :
      HasFDerivAt (nonlinearLeastSquaresObjective r)
        (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x)) x := by
    -- Rewrite the objective into the norm-square form used by the derivative rule.
    simpa [hObjectiveEq] using hObjectiveRaw
  have hDual :
      (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x)) =
        (InnerProductSpace.toDual ℝ Point) (g[r](x)) := by
    ext y
    -- The Fréchet derivative is the Riesz dual of the Chapter 7 gradient vector.
    simpa [leastSquaresGradient, _root_.smul_apply] using
      (innerTransposeJacobianApplyVec (r := r) (x := x) (w := r x) (y := y)).symm
  have hGradientAt : HasGradientAt (nonlinearLeastSquaresObjective r) g[r](x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    rw [← hDual]
    exact hObjective
  exact hGradientAt.gradient

/-- Gradient formula for Chapter07 Notation 7.1-extra-2: if `r` is differentiable at `x`,
then `g(x) = J(x)ᵀ r(x)`. -/
theorem leastSquaresObjective_gradient_eq
    (r : Point → Residual) (x : Point) (hr : DifferentiableAt ℝ r x) :
    gradient (nonlinearLeastSquaresObjective r) x = g[r](x) := by
  -- Reuse the local Riesz/Jacobian bridge for the source gradient identity.
  exact leastSquaresObjectiveGradientEqGaussNewtonGradient (r := r) (x := x) hr

/-- Helper for Chapter07 Notation 7.1-extra-2: the gradient of one residual coordinate is the
corresponding row of `J(x)` transported back through `J(x)ᵀ`. -/
private theorem residualCoordinateGradientEqTransposeJacobianBasis
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hr : DifferentiableAt ℝ r x) :
    gradient (fun y : Point ↦ residualCoords (r y) i) x =
      ((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i) := by
  let coord : Residual →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (residualCoords : Residual ≃L[ℝ] Fin m → ℝ).toContinuousLinearMap
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
          (((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
    ext y
    -- Identify the coordinate functional with pairing against the `i`-th standard basis vector.
    calc
      coord ((fderiv ℝ r x) y)
          = residualCoords ((fderiv ℝ r x) y) i := by
              simp [coord]
      _ = inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ i) ((fderiv ℝ r x) y) := by
            symm
            simpa using
              (EuclideanSpace.basisFun_inner (ι := Fin m) (𝕜 := ℝ) ((fderiv ℝ r x) y) i)
      _ = inner ℝ (((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i)) y := by
            symm
            exact innerTransposeJacobianApplyVec (r := r) (x := x)
              (w := EuclideanSpace.basisFun (Fin m) ℝ i) (y := y)
  have hgrad :
      HasGradientAt (fun y : Point ↦ residualCoords (r y) i)
        (((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hcoord.congr_fderiv hdual
  exact hgrad.gradient

/-- Helper for Chapter07 Notation 7.1-extra-2: the Chapter 7 gradient vector is the
residual-weighted sum of the residual-coordinate gradients. -/
private theorem gaussNewtonGradientEqResidualCoordSum
    (r : Point → Residual) (x : Point) (hr : DifferentiableAt ℝ r x) :
    g[r](x) =
      ∑ i : Fin m,
        residualCoords (r x) i •
          gradient (fun y : Point ↦ residualCoords (r y) i) x := by
  let coeff : Fin m → ℝ := residualCoords (r x)
  have hResidualExpand :
      r x = ∑ i : Fin m, coeff i • EuclideanSpace.basisFun (Fin m) ℝ i := by
    -- Expand the residual vector in the standard Euclidean basis.
    simpa [coeff] using ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr (r x)).symm
  calc
    g[r](x) = ((J[r](x))ᵀ).toEuclideanLin (r x) := by
      rfl
    _ = ((J[r](x))ᵀ).toEuclideanLin
          (∑ i : Fin m, coeff i • EuclideanSpace.basisFun (Fin m) ℝ i) := by
            rw [hResidualExpand]
    _ = ∑ i : Fin m,
          coeff i •
            ((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i) := by
            simp
    _ = ∑ i : Fin m,
          coeff i •
            gradient (fun y : Point ↦ residualCoords (r y) i) x := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [residualCoordinateGradientEqTransposeJacobianBasis (r := r) (x := x) (i := i) hr]

/-- Source-facing companion formula for the least-squares gradient expansion
`g(x) = ∑ i, r_i(x) • ∇ r_i(x)` when `r` is differentiable at `x`. -/
theorem leastSquaresObjective_gradient_sum_eq
    (r : Point → Residual) (x : Point) (hr : DifferentiableAt ℝ r x) :
    g[r](x) =
      ∑ i : Fin m,
        residualCoords (r x) i •
          gradient (fun y : Point ↦ residualCoords (r y) i) x := by
  -- Expand the residual vector into the Euclidean basis and push `J(x)ᵀ` through the sum.
  exact gaussNewtonGradientEqResidualCoordSum (r := r) (x := x) hr

/-- Helper for Chapter07 Notation 7.1-extra-2: a `C²` residual map at one point is
differentiable there. -/
private theorem residualDifferentiableAtOfContDiffAt
    (r : Point → Residual) (x : Point) (hResidualC2 : ContDiffAt ℝ 2 r x) :
    DifferentiableAt ℝ r x := by
  -- Reduce the local `C²` hypothesis to the first-order differentiability needed below.
  exact
    (show ContDiffAt ℝ 1 r x from hResidualC2.of_le (by norm_num)).differentiableAt (by norm_num)

/-- Helper for Chapter07 Notation 7.1-extra-2: a Hessian matrix is determined by the derivative
of the corresponding gradient field. -/
private theorem hessianMatrixAtEqOfGradientHasFDerivAt
    (φ : Point → ℝ) (x : Point) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA :
      HasFDerivAt
        (gradient φ)
        ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) x) :
    hessianMatrixAt φ x = A := by
  have hEq :
      (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (hessianMatrixAt φ x) =
        (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A := by
    -- Compare both matrices through the canonical continuous-linear-map owner.
    calc
      (Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (hessianMatrixAt φ x)
          = fderiv ℝ (gradient φ) x := by
              rw [toEuclideanCLM_hessianMatrixAt, hessianAt]
      _ =
          (Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A := by
              rw [hA.fderiv]
  exact (Matrix.toEuclideanCLM :
    Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point).injective hEq

/-- Helper for Chapter07 Notation 7.1-extra-2: the Hessian matrix attached to one residual
coordinate is exactly the derivative of that coordinate's gradient in Euclidean matrix form. -/
private theorem residualCoordinateGradientHasFDerivAtHessianMatrixLocal
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hResidualC2 : ContDiffAt ℝ 2 r x) :
    HasFDerivAt (gradient (fun y : Point ↦ residualCoords (r y) i))
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (residualCoordinateHessianMatrix r i x))) x := by
  let φ : Point → ℝ := fun y : Point ↦ residualCoords (r y) i
  let coord : Residual →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (residualCoords : Residual ≃L[ℝ] Fin m → ℝ).toContinuousLinearMap
  have hphiEq : φ = coord ∘ r := by
    funext y
    simp [φ, coord, Function.comp]
  have hcoordC2 : ContDiffAt ℝ 2 φ x := by
    -- The scalar residual coordinate inherits the ambient `C²` regularity by composition.
    rw [hphiEq]
    simpa using coord.contDiff.contDiffAt.comp x hResidualC2
  let e : StrongDual ℝ Point ≃L[ℝ] Point :=
    (InnerProductSpace.toDual ℝ Point).symm.toContinuousLinearEquiv
  have hfd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := by
    -- Route correction: differentiate the scalar residual coordinate directly, not the objective.
    exact (hcoordC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      |>.hasFDerivAt
  have hgrad := by
    -- Transport the second derivative through the Riesz isomorphism defining `gradient`.
    simpa [φ, gradient, Function.comp, e] using ((e.hasFDerivAt).comp x hfd)
  have hhessEq : residualCoordinateHessianMatrix r i x = hessianMatrixAt φ x := by
    -- Both matrix owners are the same derivative of `gradient φ`, written through two APIs.
    ext a b
    simp [φ, residualCoordinateHessianMatrix, hessianMatrixAt, hessianAt, Matrix.toEuclideanCLM]
  have hclmEq :
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (residualCoordinateHessianMatrix r i x)) =
        fderiv ℝ (gradient φ) x := by
    rw [hhessEq, toEuclideanCLM_hessianMatrixAt, hessianAt]
  have htarget :
      (e.toContinuousLinearMap ∘SL fderiv ℝ (fderiv ℝ φ) x) =
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (residualCoordinateHessianMatrix r i x)) := by
    exact (show fderiv ℝ (gradient φ) x = _ from
      (show HasFDerivAt (gradient φ) _ x from hgrad).fderiv).symm.trans hclmEq.symm
  -- Replace the intrinsic derivative spelling with the Chapter 7 matrix owner.
  simpa [φ] using (show HasFDerivAt (gradient φ) _ x from hgrad).congr_fderiv htarget

/-- Helper for Chapter07 Notation 7.1-extra-2: differentiating one residual-weighted
coordinate-gradient summand produces the textbook `∇ r_i(x) ∇ r_i(x)ᵀ + r_i(x) ∇² r_i(x)` term. -/
private theorem residualCoordinateWeightedGradientHasFDerivAt
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hResidualC2 : ContDiffAt ℝ 2 r x) :
    HasFDerivAt
      (fun y : Point ↦
        residualCoords (r y) i • gradient (fun z : Point ↦ residualCoords (r z) i) y)
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
          residualCoords (r x) i • residualCoordinateHessianMatrix r i x))) x := by
  let φ : Point → ℝ := fun y : Point ↦ residualCoords (r y) i
  have hrDiff : DifferentiableAt ℝ r x :=
    residualDifferentiableAtOfContDiffAt (r := r) (x := x) hResidualC2
  have hphiDiff : DifferentiableAt ℝ φ x := by
    -- The scalar coordinate is differentiable because it is a coordinate projection of `r`.
    let coord : Residual →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp
        (residualCoords : Residual ≃L[ℝ] Fin m → ℝ).toContinuousLinearMap
    have hphiEq : φ = coord ∘ r := by
      funext y
      simp [φ, coord, Function.comp]
    rw [hphiEq]
    exact (coord.hasFDerivAt.comp x hrDiff.hasFDerivAt).differentiableAt
  have hphiDeriv :
      HasFDerivAt φ ((InnerProductSpace.toDual ℝ Point) (gradient φ x)) x :=
    hphiDiff.hasGradientAt.hasFDerivAt
  have hgradDeriv :
      HasFDerivAt (gradient φ)
        (((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (residualCoordinateHessianMatrix r i x))) x :=
    residualCoordinateGradientHasFDerivAtHessianMatrixLocal
      (r := r) (x := x) (i := i) hResidualC2
  have hprod :
      HasFDerivAt (fun y : Point ↦ φ y • gradient φ y)
        (φ x •
            ((Matrix.toEuclideanCLM :
                Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
              (residualCoordinateHessianMatrix r i x)) +
          (((InnerProductSpace.toDual ℝ Point) (gradient φ x)).smulRight (gradient φ x))) x :=
    hphiDeriv.smul hgradDeriv
  have hgradCoords :
      (gradient φ x).ofLp = fun j : Fin n ↦ J[r](x) i j := by
    -- Read the gradient coordinates from the `i`-th row of the Jacobian.
    ext j
    have hgradEq :=
      residualCoordinateGradientEqTransposeJacobianBasis (r := r) (x := x) (i := i) hrDiff
    have hcoordEq := congrArg (fun v : Point ↦ v.ofLp j) hgradEq
    simpa [φ, Matrix.toEuclideanLin, Matrix.toLpLin_apply, residualJacobianMatrix,
      EuclideanSpace.basisFun_apply, dotProduct] using hcoordEq
  let gradφx : Point := gradient φ x
  have hRankOneSymm :
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm
        (((InnerProductSpace.toDual ℝ Point) gradφx).smulRight gradφx)) =
        Matrix.vecMulVec gradφx gradφx := by
    -- Express the scalar-derivative term as the Euclidean matrix of the rank-one map.
    change Matrix.toEuclideanLin.symm ((((innerSL ℝ gradφx).smulRight gradφx).toLinearMap)) = _
    simpa [gradφx, InnerProductSpace.rankOne_def] using
      (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℝ) (x := gradφx) (y := gradφx))
  have hRankOne :
      (((InnerProductSpace.toDual ℝ Point) gradφx).smulRight gradφx) =
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j))) := by
    have hRankOneMatrix :
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm
          (((InnerProductSpace.toDual ℝ Point) gradφx).smulRight gradφx)) =
          Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) := by
      simpa [gradφx, hgradCoords] using hRankOneSymm
    simpa using congrArg
      (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) hRankOneMatrix
  have hTargetDeriv :
      (φ x •
          ((Matrix.toEuclideanCLM :
              Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
            (residualCoordinateHessianMatrix r i x)) +
        (((InnerProductSpace.toDual ℝ Point) gradφx).smulRight gradφx)) =
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
            residualCoords (r x) i • residualCoordinateHessianMatrix r i x)) := by
    -- Keep the derivative on the CLM side and combine the rank-one and Hessian pieces once.
    rw [hRankOne, map_add, map_smul]
    simp [φ, add_comm]
  simpa [φ] using hprod.congr_fderiv hTargetDeriv

/-- Helper for Chapter07 Notation 7.1-extra-2: the Chapter 7 Hessian matrix `G(x)` is the sum of
the coordinate rank-one terms and correction Hessians. -/
private theorem leastSquaresHessianEqCoordinateSum
    (r : Point → Residual) (x : Point) :
    G[r](x) =
      ∑ i : Fin m,
        (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
          residualCoords (r x) i • residualCoordinateHessianMatrix r i x) := by
  -- This identity is purely algebraic: expand `J(x)ᵀ J(x)` entrywise and regroup the sum.
  ext a b
  simp only [leastSquaresHessianMatrix, leastSquaresCorrectionMatrix, Matrix.add_apply,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec, Matrix.transpose_apply,
    Matrix.of_apply, Finset.sum_add_distrib]

/-- Helper for Chapter07 Notation 7.1-extra-2: the derivative of the local Chapter 7 gradient
field `g[r]` at `x` is the local Chapter 7 Hessian matrix `G[r](x)`. -/
private theorem gaussNewtonGradientHasFDerivAtHessianLocal
    (r : Point → Residual) (x : Point)
    (hResidualC2 : ContDiffAt ℝ 2 r x) :
    HasFDerivAt (fun y : Point ↦ g[r](y))
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (G[r](x)))) x := by
  let sumField : Point → Point := fun y : Point ↦
    ∑ i : Fin m,
      residualCoords (r y) i • gradient (fun z : Point ↦ residualCoords (r z) i) y
  have hsum :
      HasFDerivAt sumField
        (∑ i : Fin m,
          ((Matrix.toEuclideanCLM :
              Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
            (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
              residualCoords (r x) i • residualCoordinateHessianMatrix r i x))) x := by
    -- Differentiate the finite coordinate sum term-by-term at the base point `x`.
    simpa [sumField] using
      (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        residualCoordinateWeightedGradientHasFDerivAt (r := r) (x := x) (i := i) hResidualC2)
  have hMatrixSum :
      (∑ i : Fin m,
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
            residualCoords (r x) i • residualCoordinateHessianMatrix r i x))) =
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (G[r](x))) := by
    -- Reassemble the matrix sum first, then move it back through `Matrix.toEuclideanCLM`.
    simpa using congrArg
      (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
      (leastSquaresHessianEqCoordinateSum (r := r) (x := x)).symm
  have hsumEventually : (fun y : Point ↦ g[r](y)) =ᶠ[nhds x] sumField := by
    have hResidualEventually : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 r y :=
      hResidualC2.eventually (by norm_num)
    filter_upwards [hResidualEventually] with y hy
    -- Near `x`, every point inherits enough regularity to use the coordinate-sum formula.
    exact gaussNewtonGradientEqResidualCoordSum (r := r) (x := y)
      (residualDifferentiableAtOfContDiffAt (r := r) (x := y) hy)
  exact (hsum.congr_fderiv hMatrixSum).congr_of_eventuallyEq hsumEventually

/-- Hessian formula for Chapter07 Notation 7.1-extra-2: if `r` is `C²` at `x`, then
`G(x) = J(x)ᵀ J(x) + S(x)`. -/
theorem leastSquaresObjective_hessianMatrix_eq
    (r : Point → Residual) (x : Point) (hResidualC2 : ContDiffAt ℝ 2 r x) :
    hessianMatrixAt (nonlinearLeastSquaresObjective r) x = G[r](x) := by
  have hGradientDeriv :
      HasFDerivAt (fun y : Point ↦ gradient (nonlinearLeastSquaresObjective r) y)
        ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G[r](x))) x := by
    have hGaussNewtonDeriv :=
      gaussNewtonGradientHasFDerivAtHessianLocal (r := r) (x := x) hResidualC2
    have hGradientEventually :
        (fun y : Point ↦ gradient (nonlinearLeastSquaresObjective r) y) =ᶠ[nhds x]
          fun y : Point ↦ g[r](y) := by
      have hResidualEventually : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 r y :=
        hResidualC2.eventually (by norm_num)
      filter_upwards [hResidualEventually] with y hy
      -- Nearby gradients agree with the Chapter 7 formula because nearby residuals are `C²`.
      exact leastSquaresObjective_gradient_eq (r := r) (x := y)
        (residualDifferentiableAtOfContDiffAt (r := r) (x := y) hy)
    exact hGaussNewtonDeriv.congr_of_eventuallyEq hGradientEventually
  -- Convert the derivative of the gradient field back to the Euclidean Hessian matrix owner.
  exact hessianMatrixAtEqOfGradientHasFDerivAt
    (φ := nonlinearLeastSquaresObjective r) (x := x) (A := G[r](x)) hGradientDeriv

/-- Source-facing companion formula for the least-squares Hessian expansion
`G(x) = ∑ i, (∇ r_i(x) ∇ r_i(x)ᵀ + r_i(x) • ∇² r_i(x))` when `r` is `C²` at `x`. -/
theorem leastSquaresObjective_hessianMatrix_sum_eq
    (r : Point → Residual) (x : Point) (hResidualC2 : ContDiffAt ℝ 2 r x) :
    G[r](x) =
      ∑ i : Fin m,
        (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
          residualCoords (r x) i • residualCoordinateHessianMatrix r i x) := by
  -- This companion identity is algebraic; the local `C²` hypothesis aligns it with the source.
  let _ := hResidualC2
  exact leastSquaresHessianEqCoordinateSum (r := r) (x := x)

/-- Chapter07 Notation 7.1-extra-2 (3): the quadratic model at the base point `xk`,
`f(xk) + g(xk)ᵀ (x - xk) + (1 / 2) * (x - xk)ᵀ G(xk) (x - xk)`, with
`g(xk) = J(xk)ᵀ r(xk)` and `G(xk) = J(xk)ᵀ J(xk) + S(xk)`, assuming `r`
is `C²` at `x_k` so the preceding gradient and Hessian identities are well-defined. -/
theorem leastSquaresQuadraticModel_expanded_eq
    (r : Point → Residual) (xk x : Point) (hResidualC2 : ContDiffAt ℝ 2 r xk) :
    newtonQuadraticModel
        (nonlinearLeastSquaresObjective r)
        xk
        (hessianMatrixAt (nonlinearLeastSquaresObjective r))
        (x - xk) =
      (1 / 2 : ℝ) * dotProduct (residualCoords (r xk)) (residualCoords (r xk)) +
        inner ℝ (((J[r](xk))ᵀ).toEuclideanLin (r xk)) (x - xk) +
        (1 / 2 : ℝ) *
          inner ℝ
            (x - xk)
            ((((J[r](xk))ᵀ * J[r](xk) + S[r](xk))).toEuclideanLin (x - xk)) := by
  have hr : DifferentiableAt ℝ r xk :=
    residualDifferentiableAtOfContDiffAt (r := r) (x := xk) hResidualC2
  -- Expand the quadratic model once, then rewrite the intrinsic gradient and Hessian owners.
  rw [newtonQuadraticModel,
    leastSquaresObjective_gradient_eq (r := r) (x := xk) hr,
    leastSquaresObjective_hessianMatrix_eq (r := r) (x := xk) hResidualC2]
  simp [nonlinearLeastSquaresObjective, leastSquaresGradient, leastSquaresHessianMatrix]

end
