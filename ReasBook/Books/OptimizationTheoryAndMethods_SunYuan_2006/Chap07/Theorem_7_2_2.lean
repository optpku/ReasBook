/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Sequences
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_22
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2.DifferentialData
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2.NormalEquation

noncomputable section

open Filter Matrix
open scoped LeastSquares
open scoped Matrix.Norms.L2Operator

section

variable {m n : ℕ}

-- Local declaration justification (source-local notation): this source-facing theorem keeps the
-- chapter's point-space formulas readable while confining the alias to the current item file.
local notation "Point" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): the residual codomain alias mirrors
-- the source statement and is intentionally kept local to avoid exporting a generic notation.
local notation "Residual" => EuclideanSpace ℝ (Fin m)

/-- Helper for Chapter07 Theorem 7.2.2: pairing `J(x)ᵀ w` with a test vector agrees with
pairing `w` against the residual derivative in that direction. -/
private lemma inner_transposeJacobian_apply_vec
    (r : Point → Residual) (x : Point) (w : Residual) (y : Point) :
    inner ℝ (((residualJacobianMatrix r x)ᵀ).toEuclideanLin w) y =
      inner ℝ w ((fderiv ℝ r x) y) := by
  let pointBasis := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let residualBasis := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  let jacobian : Matrix (Fin m) (Fin n) ℝ := residualJacobianMatrix r x
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

/-- Helper for Chapter07 Theorem 7.2.2: pairing `J(x)ᵀ r(x)` with a test vector agrees with
pairing `r(x)` against the residual derivative in that direction. -/
private lemma inner_transposeJacobian_apply
    (r : Point → Residual) (x : Point) (y : Point) :
    inner ℝ (((residualJacobianMatrix r x)ᵀ).toEuclideanLin (r x)) y =
      inner ℝ (r x) ((fderiv ℝ r x) y) := by
  -- Specialize the vector-valued pairing bridge to the residual vector itself.
  simpa using inner_transposeJacobian_apply_vec (r := r) (x := x) (w := r x) (y := y)

/-- Helper for Chapter07 Theorem 7.2.2: differentiability of the residual map identifies the
canonical gradient of the least-squares objective with the source vector `J(x)ᵀ r(x)`. -/
private theorem leastSquaresObjectiveGradient_eq_gaussNewtonGradient
    (r : Point → Residual) (x : Point) (hr : DifferentiableAt ℝ r x) :
    gradient (nonlinearLeastSquaresObjective r) x = g[r](x) := by
  have hResidualDeriv : HasFDerivAt r (fderiv ℝ r x) x := hr.hasFDerivAt
  have hNormSq :
      HasFDerivAt (fun y : Point ↦ ‖r y‖ ^ (2 : ℕ))
        (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x) x := by
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
    simpa [hObjectiveEq] using hObjectiveRaw
  have hDual :
      (((1 / 2 : ℝ) : ℝ) • (2 • (innerSL ℝ) (r x) ∘SL fderiv ℝ r x)) =
        (InnerProductSpace.toDual ℝ Point) (g[r](x)) := by
    ext y
    -- The derivative is the Riesz dual of `J(x)ᵀ r(x)`.
    simpa [leastSquaresGradient, _root_.smul_apply] using
      (inner_transposeJacobian_apply (r := r) (x := x) (y := y)).symm
  have hGradientAt : HasGradientAt (nonlinearLeastSquaresObjective r) g[r](x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    rw [← hDual]
    exact hObjective
  exact hGradientAt.gradient

/-- Helper for Chapter07 Theorem 7.2.2: a local minimizer of the least-squares objective is a
stationary point for the source Gauss-Newton gradient `g[r](x)`. -/
private theorem gaussNewtonGradient_eq_zero_of_localMin
    (r : Point → Residual) (xStar : Point)
    (hResidualC2 : ContDiff ℝ 2 r)
    (hLocalMin : IsLocalMin (nonlinearLeastSquaresObjective r) xStar) :
    g[r](xStar) = 0 := by
  have hObjectiveDiff : DifferentiableAt ℝ (nonlinearLeastSquaresObjective r) xStar := by
    have hObjectiveC1 : ContDiff ℝ 1 (nonlinearLeastSquaresObjective r) :=
      (hResidualC2.nonlinearLeastSquaresObjective).of_le (by norm_num)
    have hObjectiveC1At : ContDiffAt ℝ 1 (nonlinearLeastSquaresObjective r) xStar :=
      hObjectiveC1.contDiffAt
    exact hObjectiveC1At.differentiableAt (by norm_num)
  have hStationary :=
    isStationaryPoint_of_isLocalMin (nonlinearLeastSquaresObjective r) xStar hObjectiveDiff
      hLocalMin
  have hGradientZero : gradient (nonlinearLeastSquaresObjective r) xStar = 0 :=
    hStationary.gradient_eq_zero
  -- Replace the canonical gradient with the Chapter 7 source notation `g[r](xStar)`.
  have hResidualDiff : DifferentiableAt ℝ r xStar := by
    have hResidualC1 : ContDiff ℝ 1 r := hResidualC2.of_le (by norm_num)
    have hResidualC1At : ContDiffAt ℝ 1 r xStar := hResidualC1.contDiffAt
    exact hResidualC1At.differentiableAt (by norm_num)
  rw [leastSquaresObjectiveGradient_eq_gaussNewtonGradient r xStar hResidualDiff] at hGradientZero
  exact hGradientZero

/-- Helper for Chapter07 Theorem 7.2.2: a `C²` residual map is differentiable at every point. -/
private theorem residualDifferentiableAt_of_contDiff
    (r : Point → Residual)
    (hResidualC2 : ContDiff ℝ 2 r)
    (x : Point) :
    DifferentiableAt ℝ r x := by
  -- Reduce the global `C²` hypothesis to the first-order differentiability needed below.
  have hResidualC1 : ContDiff ℝ 1 r := hResidualC2.of_le (by norm_num)
  exact hResidualC1.contDiffAt.differentiableAt (by norm_num)

/-- Helper for Chapter07 Theorem 7.2.2: the gradient of a residual coordinate is the
corresponding row of `J(x)` transported back through `J(x)ᵀ`. -/
private theorem residualCoordinateGradient_eq_transposeJacobianBasis
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hr : DifferentiableAt ℝ r x) :
    gradient (fun y : Point ↦ residualCoords m (r y) i) x =
      ((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i) := by
  let coord : Residual →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (residualCoords m).toContinuousLinearMap
  have hcoord :
      HasFDerivAt (fun y : Point ↦ residualCoords m (r y) i)
        (coord.comp (fderiv ℝ r x)) x := by
    -- Differentiate the scalar residual coordinate by composing the residual map with the
    -- continuous coordinate projection.
    have hcoord' : HasFDerivAt (coord ∘ r) (coord.comp (fderiv ℝ r x)) x :=
      coord.hasFDerivAt.comp x hr.hasFDerivAt
    have hfun : (fun y : Point ↦ residualCoords m (r y) i) = coord ∘ r := by
      funext y
      simp [coord, Function.comp]
    rw [hfun]
    exact hcoord'
  have hdual :
      coord.comp (fderiv ℝ r x) =
        (InnerProductSpace.toDual ℝ Point)
          (((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i)) := by
    ext y
    -- Compare both linear functionals through the canonical Euclidean basis coordinate `i`.
    calc
      coord ((fderiv ℝ r x) y)
          = residualCoords m ((fderiv ℝ r x) y) i := by
              simp [coord]
      _ = inner ℝ (EuclideanSpace.basisFun (Fin m) ℝ i) ((fderiv ℝ r x) y) := by
            symm
            simpa using
              (EuclideanSpace.basisFun_inner (ι := Fin m) (𝕜 := ℝ) ((fderiv ℝ r x) y) i)
      _ = inner ℝ (((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i)) y := by
            symm
            exact inner_transposeJacobian_apply_vec (r := r) (x := x)
              (w := EuclideanSpace.basisFun (Fin m) ℝ i) (y := y)
  have hgrad :
      HasGradientAt (fun y : Point ↦ residualCoords m (r y) i)
        (((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hcoord.congr_fderiv hdual
  exact hgrad.gradient

/-- Helper for Chapter07 Theorem 7.2.2: the source Gauss-Newton gradient is the residual-weighted
sum of the residual-coordinate gradients. -/
private theorem gaussNewtonGradient_eq_residualCoordSum
    (r : Point → Residual) (x : Point) (hr : DifferentiableAt ℝ r x) :
    g[r](x) =
      ∑ i : Fin m,
        residualCoords m (r x) i •
          gradient (fun y : Point ↦ residualCoords m (r y) i) x := by
  let coeff : Fin m → ℝ := residualCoords m (r x)
  have hResidualExpand :
      r x = ∑ i : Fin m,
        coeff i • EuclideanSpace.basisFun (Fin m) ℝ i := by
    -- Expand the residual vector in the standard Euclidean basis.
    simpa [coeff, residualCoords] using ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr (r x)).symm
  calc
    g[r](x) = ((J[r](x))ᵀ).toEuclideanLin (r x) := by
      rfl
    _ = ((J[r](x))ᵀ).toEuclideanLin
          (∑ i : Fin m,
            coeff i • EuclideanSpace.basisFun (Fin m) ℝ i) := by
            rw [hResidualExpand]
    _ = ∑ i : Fin m,
          coeff i •
            ((J[r](x))ᵀ).toEuclideanLin (EuclideanSpace.basisFun (Fin m) ℝ i) := by
            simp
    _ = ∑ i : Fin m,
          coeff i •
            gradient (fun y : Point ↦ residualCoords m (r y) i) x := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [residualCoordinateGradient_eq_transposeJacobianBasis (r := r) (x := x)
              (i := i) hr]

/-- Helper for Chapter07 Theorem 7.2.2: the Hessian matrix attached to one residual coordinate
is exactly the derivative of that coordinate's gradient, expressed in the Euclidean matrix model. -/
private theorem residualCoordinateGradient_hasFDerivAt_hessianMatrix
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hResidualC2 : ContDiff ℝ 2 r) :
    HasFDerivAt (gradient (fun y : Point ↦ residualCoords m (r y) i))
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (residualCoordinateHessianMatrix r i x))) x := by
  let φ : Point → ℝ := fun y : Point ↦ residualCoords m (r y) i
  let coord : Residual →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (residualCoords m).toContinuousLinearMap
  have hphiEq : φ = coord ∘ r := by
    funext y
    simp [φ, coord, Function.comp]
  have hcoordC2 : ContDiffAt ℝ 2 φ x := by
    -- The residual coordinate inherits the ambient `C²` regularity by composing with a projection.
    rw [hphiEq]
    simpa using coord.contDiff.contDiffAt.comp x hResidualC2.contDiffAt
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
    -- Both matrix owners are the same `fderiv ℝ (gradient φ) x`, written through two interfaces.
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
  -- Replace the canonical derivative spelling by the Chapter 7 residual-coordinate Hessian owner.
  simpa [φ] using (show HasFDerivAt (gradient φ) _ x from hgrad).congr_fderiv htarget

/-- Helper for Chapter07 Theorem 7.2.2: differentiating one residual-weighted coordinate-gradient
summand produces the textbook rank-one `Jᵢ(x)ᵀ Jᵢ(x)` term plus the weighted Hessian correction. -/
private theorem residualCoordinateWeightedGradient_hasFDerivAt
    (r : Point → Residual) (x : Point) (i : Fin m)
    (hResidualC2 : ContDiff ℝ 2 r) :
    HasFDerivAt
      (fun y : Point ↦
        residualCoords m (r y) i • gradient (fun z : Point ↦ residualCoords m (r z) i) y)
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
          residualCoords m (r x) i • residualCoordinateHessianMatrix r i x))) x := by
  let φ : Point → ℝ := fun y : Point ↦ residualCoords m (r y) i
  have hrDiff : DifferentiableAt ℝ r x :=
    residualDifferentiableAt_of_contDiff (r := r) hResidualC2 x
  have hphiDiff : DifferentiableAt ℝ φ x := by
    -- The scalar residual coordinate is differentiable because it is a projection of `r`.
    let coord : Residual →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (residualCoords m).toContinuousLinearMap
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
    residualCoordinateGradient_hasFDerivAt_hessianMatrix (r := r) (x := x) (i := i) hResidualC2
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
    -- Read the gradient coordinates from the `i`-th Jacobian row.
    ext j
    have hgradEq :=
      residualCoordinateGradient_eq_transposeJacobianBasis (r := r) (x := x) (i := i) hrDiff
    have hcoordEq := congrArg (fun v : Point => v.ofLp j) hgradEq
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
            residualCoords m (r x) i • residualCoordinateHessianMatrix r i x)) := by
    -- Keep the derivative on the CLM side and combine the rank-one and Hessian pieces once.
    rw [hRankOne, map_add, map_smul]
    simp [φ, add_comm]
  simpa [φ] using hprod.congr_fderiv hTargetDeriv

/-- Helper for Chapter07 Theorem 7.2.2: the derivative of the Chapter 7 Gauss-Newton gradient
field `g[r]` is the Chapter 7 matrix field `G[r]`. -/
private theorem gaussNewtonGradient_hasFDerivAt_hessian
    (r : Point → Residual) (x : Point)
    (hResidualC2 : ContDiff ℝ 2 r) :
    HasFDerivAt (fun y : Point ↦ g[r](y))
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (G[r](x)))) x := by
  have hrDiff : DifferentiableAt ℝ r x :=
    residualDifferentiableAt_of_contDiff (r := r) hResidualC2 x
  have hgEq :
      (fun y : Point ↦ g[r](y)) =
        fun y : Point ↦
          ∑ i : Fin m,
            residualCoords m (r y) i • gradient (fun z : Point ↦ residualCoords m (r z) i) y := by
    funext y
    rw [gaussNewtonGradient_eq_residualCoordSum (r := r) (x := y)
      (residualDifferentiableAt_of_contDiff (r := r) hResidualC2 y)]
  rw [hgEq]
  -- Differentiate the finite residual-coordinate sum one summand at a time.
  have hsum :
      HasFDerivAt
        (fun y : Point ↦
          ∑ i : Fin m, residualCoords m (r y) i • gradient (fun z : Point ↦ residualCoords m (r z) i) y)
        (∑ i : Fin m,
          ((Matrix.toEuclideanCLM :
              Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
            (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
              residualCoords m (r x) i • residualCoordinateHessianMatrix r i x))) x := by
    simpa using
      (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        residualCoordinateWeightedGradient_hasFDerivAt (r := r) (x := x) (i := i) hResidualC2)
  have hMatrixSumMatrix :
      (∑ i : Fin m,
        (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
          residualCoords m (r x) i • residualCoordinateHessianMatrix r i x)) =
        G[r](x) := by
    -- Reassemble the textbook `J(x)ᵀ J(x) + S(x)` decomposition at the matrix level first.
    rw [leastSquaresHessianMatrix, leastSquaresCorrectionMatrix]
    ext a b
    rw [Finset.sum_add_distrib]
    simp [Matrix.mul_apply, Matrix.vecMulVec]
    rw [Matrix.sum_apply]
    simp
  have hMatrixSum :
      (∑ i : Fin m,
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (Matrix.vecMulVec (fun j : Fin n ↦ J[r](x) i j) (fun j : Fin n ↦ J[r](x) i j) +
            residualCoords m (r x) i • residualCoordinateHessianMatrix r i x))) =
      ((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (G[r](x))) := by
    simpa using congrArg
      (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) hMatrixSumMatrix
  exact hsum.congr_fderiv hMatrixSum

/-- Helper for Chapter07 Theorem 7.2.2: applying the inverse matrix action to the original
matrix action returns the starting vector. -/
private theorem toEuclideanLin_inv_toEuclideanCLM_apply
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A)
    (v : Point) :
    Matrix.toEuclideanLin (A⁻¹)
      (((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) v) = v := by
  letI := hA.invertible
  -- Cancel the inverse at the matrix-action layer before returning to Euclidean coordinates.
  apply WithLp.ofLp_injective
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toLpLin (p := (2 : ENNReal))
    (q := (2 : ENNReal)), Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
    Matrix.one_mulVec]

/-- Helper for Chapter07 Theorem 7.2.2: composing two Euclidean matrix actions matches
matrix multiplication before returning to the point-space notation. -/
private theorem toEuclideanLin_mul_apply
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (v : Point) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) =
      Matrix.toEuclideanLin (A * B) v := by
  -- Compare both sides through the coordinate `mulVec` action once.
  apply WithLp.ofLp_injective
  simp [Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal)), Matrix.mulVec_mulVec]

/-- Helper for Chapter07 Theorem 7.2.2: the Euclidean matrix action is bounded by the matrix
`ℓ₂` operator norm times the vector norm. -/
private theorem norm_toEuclideanLin_apply_le
    (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Point) :
    ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ := by
  -- Move once to the continuous-linear-map model where `le_opNorm` is the canonical bound.
  calc
    ‖Matrix.toEuclideanLin A v‖
        = ‖((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) v‖ := by
            rfl
    _ ≤ ‖((Matrix.toEuclideanCLM :
          Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A)‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖A‖ * ‖v‖ := by
          rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- Helper for Chapter07 Theorem 7.2.2: the Euclidean action of a sum of matrices is the sum of
the two Euclidean actions. -/
private theorem toEuclideanLin_add_apply
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (v : Point) :
    Matrix.toEuclideanLin (A + B) v =
      Matrix.toEuclideanLin A v + Matrix.toEuclideanLin B v := by
  -- Compare both sides through the coordinate `mulVec` action once.
  apply WithLp.ofLp_injective
  simp [Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))]

/-- Helper for Chapter07 Theorem 7.2.2: inverting one Gauss-Newton normal equation rewrites the
next error as the inverse normal matrix applied to `A(y) (y - xStar) - g(y)`. -/
private theorem gaussNewtonUpdateError_eq_inverseStepResidual
    (r : Point → Residual) (xStar y yNext : Point)
    (hAy : IsUnit (gaussNewtonNormalMatrix r y))
    (hStep : solvesGaussNewtonNormalEquation r y yNext) :
    yNext - xStar =
      Matrix.toEuclideanLin ((gaussNewtonNormalMatrix r y)⁻¹)
        (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) (y - xStar) - g[r](y)) := by
  let A : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r y
  letI := hAy.invertible
  have hStep' : Matrix.toEuclideanLin A (yNext - y) = -g[r](y) := by
    simpa [A, solvesGaussNewtonNormalEquation_iff] using hStep
  have hStepInv :
      yNext - y = Matrix.toEuclideanLin (A⁻¹) (-g[r](y)) := by
    -- Rewrite the normal equation after applying the inverse normal matrix.
    calc
      yNext - y
          = Matrix.toEuclideanLin (A⁻¹)
              (((Matrix.toEuclideanCLM :
                  Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A)
                (yNext - y)) := by
              simpa [A] using
                (toEuclideanLin_inv_toEuclideanCLM_apply (A := A) hAy (yNext - y)).symm
      _ = Matrix.toEuclideanLin (A⁻¹) (-g[r](y)) := by
            have hStepCLM :
                (((Matrix.toEuclideanCLM :
                    Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A)
                  (yNext - y)) = -g[r](y) := by
                  apply WithLp.ofLp_injective
                  simpa [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toLpLin (p := (2 : ENNReal))
                    (q := (2 : ENNReal))] using congrArg (fun z : Point => z.ofLp) hStep'
            rw [hStepCLM]
  -- Package the inverse-step formula once so the main proof can later inject the Taylor expansion
  -- of `g[r]` without reopening the inverse-cancellation algebra.
  calc
    yNext - xStar = (yNext - y) + (y - xStar) := by abel_nf
    _ = Matrix.toEuclideanLin (A⁻¹) (-g[r](y)) + (y - xStar) := by rw [hStepInv]
    _ = Matrix.toEuclideanLin (A⁻¹)
          (((Matrix.toEuclideanCLM :
              Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) (y - xStar)) +
        Matrix.toEuclideanLin (A⁻¹) (-g[r](y)) := by
          rw [toEuclideanLin_inv_toEuclideanCLM_apply (A := A) hAy (y - xStar)]
          ac_rfl
    _ = Matrix.toEuclideanLin (A⁻¹)
          (((Matrix.toEuclideanCLM :
              Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) (y - xStar) - g[r](y)) := by
          simpa [sub_eq_add_neg] using
            ((Matrix.toEuclideanLin (A⁻¹)).map_add
              (((Matrix.toEuclideanCLM :
                  Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) (y - xStar))
              (-g[r](y))).symm

/-- Helper for Chapter07 Theorem 7.2.2: the perturbation term `A(y)⁻¹ G(y) - A(xStar)⁻¹ G(xStar)`
is bounded linearly by the separate Lipschitz bounds for `G` and `A⁻¹`. -/
private theorem inverseNormalMatrixMulHessian_diff_le
    (r : Point → Residual) (xStar y : Point) (M LG LI : ℝ)
    (_hM_nonneg : 0 ≤ M)
    (hLG_nonneg : 0 ≤ LG)
    (_hLI_nonneg : 0 ≤ LI)
    (hInvNorm : ‖(gaussNewtonNormalMatrix r y)⁻¹‖ ≤ M)
    (hHessianDiff : ‖G[r](y) - G[r](xStar)‖ ≤ LG * ‖y - xStar‖)
    (hInverseDiff :
      ‖(gaussNewtonNormalMatrix r y)⁻¹ - (gaussNewtonNormalMatrix r xStar)⁻¹‖ ≤
        LI * ‖y - xStar‖) :
    ‖(gaussNewtonNormalMatrix r y)⁻¹ * G[r](y) -
        (gaussNewtonNormalMatrix r xStar)⁻¹ * G[r](xStar)‖ ≤
      (M * LG + LI * ‖G[r](xStar)‖) * ‖y - xStar‖ := by
  let AyInv : Matrix (Fin n) (Fin n) ℝ := (gaussNewtonNormalMatrix r y)⁻¹
  let AStarInv : Matrix (Fin n) (Fin n) ℝ := (gaussNewtonNormalMatrix r xStar)⁻¹
  let Gy : Matrix (Fin n) (Fin n) ℝ := G[r](y)
  let GStar : Matrix (Fin n) (Fin n) ℝ := G[r](xStar)
  have hdist_nonneg : 0 ≤ ‖y - xStar‖ := norm_nonneg _
  calc
    ‖AyInv * Gy - AStarInv * GStar‖
        = ‖AyInv * (Gy - GStar) + (AyInv - AStarInv) * GStar‖ := by
            rw [show AyInv * Gy - AStarInv * GStar =
                AyInv * (Gy - GStar) + (AyInv - AStarInv) * GStar by
                  rw [mul_sub, sub_mul]
                  abel_nf]
    _ ≤ ‖AyInv * (Gy - GStar)‖ + ‖(AyInv - AStarInv) * GStar‖ := norm_add_le _ _
    _ ≤ ‖AyInv‖ * ‖Gy - GStar‖ + ‖AyInv - AStarInv‖ * ‖GStar‖ := by
          gcongr <;> exact norm_mul_le _ _
    _ ≤ ‖AyInv‖ * (LG * ‖y - xStar‖) + (LI * ‖y - xStar‖) * ‖GStar‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hHessianDiff (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hInverseDiff (norm_nonneg _))
    _ ≤ M * (LG * ‖y - xStar‖) + (LI * ‖y - xStar‖) * ‖GStar‖ := by
          gcongr
    _ = (M * LG + LI * ‖G[r](xStar)‖) * ‖y - xStar‖ := by
          ring

/-- Helper for Chapter07 Theorem 7.2.2: inverting the normal matrix turns the source correction
matrix into `A(y)⁻¹ G(y) - I`, which is the stable form used in the perturbation estimate. -/
private theorem inverseNormalMatrix_mul_correction_eq_mul_hessian_sub_one
    (r : Point → Residual) (y : Point)
    (hAy : IsUnit (gaussNewtonNormalMatrix r y)) :
    (gaussNewtonNormalMatrix r y)⁻¹ * S[r](y) =
      (gaussNewtonNormalMatrix r y)⁻¹ * G[r](y) - 1 := by
  let Ay : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r y
  letI := hAy.invertible
  have hHessianSplit : G[r](y) = Ay + S[r](y) := by
    simp [Ay, gaussNewtonNormalMatrix_eq, leastSquaresHessianMatrix]
  -- Rewrite `G(y) = A(y) + S(y)` before cancelling the inverse-normal term.
  calc
    Ay⁻¹ * S[r](y) = Ay⁻¹ * G[r](y) - 1 := by
      symm
      calc
        Ay⁻¹ * G[r](y) - 1 = Ay⁻¹ * (Ay + S[r](y)) - 1 := by rw [hHessianSplit]
        _ = Ay⁻¹ * Ay + Ay⁻¹ * S[r](y) - 1 := by rw [mul_add]
        _ = Ay⁻¹ * S[r](y) := by simp [Matrix.inv_mul_of_invertible]

/-- Helper for Chapter07 Theorem 7.2.2: the correction-field perturbation is the same as the
`A(y)⁻¹ G(y)` perturbation once the identity terms cancel. -/
private theorem inverseNormalMatrixMulCorrection_diff_eq_inverseNormalMatrixMulHessian_diff
    (r : Point → Residual) (xStar y : Point)
    (hAy : IsUnit (gaussNewtonNormalMatrix r y))
    (hAStar : IsUnit (gaussNewtonNormalMatrix r xStar)) :
    (gaussNewtonNormalMatrix r y)⁻¹ * S[r](y) -
        (gaussNewtonNormalMatrix r xStar)⁻¹ * S[r](xStar) =
      (gaussNewtonNormalMatrix r y)⁻¹ * G[r](y) -
        (gaussNewtonNormalMatrix r xStar)⁻¹ * G[r](xStar) := by
  -- Rewrite both correction terms through `A⁻¹ G - I` and cancel the common identity.
  rw [inverseNormalMatrix_mul_correction_eq_mul_hessian_sub_one (r := r) (y := y) hAy,
    inverseNormalMatrix_mul_correction_eq_mul_hessian_sub_one (r := r) (y := xStar) hAStar]
  abel_nf

/-- Helper for Chapter07 Theorem 7.2.2: the remaining analytic input is a Taylor-style quadratic
bound for the source Gauss-Newton step residual `A(y)(y - xStar) - g(y) + S(y)(y - xStar)`. -/
private theorem gaussNewtonStepResidual_quadraticBound_onBall
    (r : Point → Residual) (xStar : Point)
    (hResidualC2 : ContDiff ℝ 2 r)
    (hGradientZero : g[r](xStar) = 0)
    (hHessianLipschitz :
      ∃ δ > 0, ∃ L > 0, ∀ x y : Point,
        x ∈ Metric.ball xStar δ →
        y ∈ Metric.ball xStar δ →
          ‖G[r](x) - G[r](y)‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∃ C > 0, ∀ y : Point,
      y ∈ Metric.ball xStar δ →
        ‖Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) (y - xStar) - g[r](y) +
            Matrix.toEuclideanLin (S[r](y)) (y - xStar)‖ ≤
          C * ‖y - xStar‖ ^ (2 : ℕ) := by
  rcases hHessianLipschitz with ⟨δ, hδ, L, hL_pos, hLipMatrix⟩
  refine ⟨δ, hδ, (Real.toNNReal L : ℝ) / 2, by positivity, ?_⟩
  intro y hy
  have hxStarBall : xStar ∈ Metric.ball xStar δ := by
    simpa [Metric.mem_ball] using hδ
  have hDiff :
      DifferentiableOn ℝ (fun z : Point ↦ g[r](z)) (Metric.ball xStar δ) := by
    -- The derivative bridge for `g[r]` gives differentiability at every point of the ball.
    intro z hz
    have hzDiff : DifferentiableAt ℝ (fun w : Point ↦ g[r](w)) z :=
      (gaussNewtonGradient_hasFDerivAt_hessian (r := r) (x := z) hResidualC2).differentiableAt
    exact hzDiff.differentiableWithinAt
  have hLip :
      LipschitzOnWith (Real.toNNReal L)
        (fun z : Point ↦ fderiv ℝ (fun w : Point ↦ g[r](w)) z)
        (Metric.ball xStar δ) := by
    -- Rewrite each `fderiv` through `G[r]` and transport the matrix Lipschitz bound by
    -- `Matrix.toEuclideanCLM`.
    exact
      LipschitzOnWith.of_dist_le'
        (s := Metric.ball xStar δ)
        (f := fun z : Point ↦ fderiv ℝ (fun w : Point ↦ g[r](w)) z)
        (K := L)
        (fun u hu v hv ↦ by
          calc
            dist (fderiv ℝ (fun w : Point ↦ g[r](w)) u) (fderiv ℝ (fun w : Point ↦ g[r](w)) v)
                = ‖fderiv ℝ (fun w : Point ↦ g[r](w)) u - fderiv ℝ (fun w : Point ↦ g[r](w)) v‖ := by
                    simp [dist_eq_norm]
            _ = ‖((Matrix.toEuclideanCLM :
                  Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G[r](u))) -
                  ((Matrix.toEuclideanCLM :
                    Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G[r](v)))‖ := by
                  rw [(gaussNewtonGradient_hasFDerivAt_hessian (r := r) (x := u) hResidualC2).fderiv,
                    (gaussNewtonGradient_hasFDerivAt_hessian (r := r) (x := v) hResidualC2).fderiv]
            _ = ‖(Matrix.toEuclideanCLM :
                  Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G[r](u) - G[r](v))‖ := by
                  simp [map_sub]
            _ = ‖G[r](u) - G[r](v)‖ := by
                  simpa using Matrix.l2_opNorm_toEuclideanCLM (G[r](u) - G[r](v))
            _ ≤ L * dist u v := by
                  simpa [dist_eq_norm] using hLipMatrix u v hu hv)
  have hyEq : y + (xStar - y) = xStar := by
    abel_nf
  have hxd : y + (xStar - y) ∈ Metric.ball xStar δ := by
    simpa [hyEq] using hxStarBall
  have hTaylor :=
    quadraticRemainderBound_of_fderiv_lipschitzOn
      (Metric.ball xStar δ)
      (fun z : Point ↦ g[r](z))
      y
      (xStar - y)
      (Real.toNNReal L)
      Metric.isOpen_ball
      (convex_ball xStar δ)
      hy
      hDiff
      hLip
      hxd
  have hRemainder :
      ‖Matrix.toEuclideanLin (G[r](y)) (y - xStar) - g[r](y)‖ ≤
        ((Real.toNNReal L : ℝ) / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
    -- Route correction: apply Taylor directly to `g[r]`, not to the objective gradient owner.
    have hTaylor' :
        ‖g[r](xStar) - g[r](y) -
            ((Matrix.toEuclideanCLM :
                Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
              (G[r](y))) (xStar - y)‖ ≤
          ((Real.toNNReal L : ℝ) / 2) * ‖xStar - y‖ ^ (2 : ℕ) := by
      simpa [hyEq, (gaussNewtonGradient_hasFDerivAt_hessian (r := r) (x := y) hResidualC2).fderiv]
        using hTaylor
    have hnorm_rev : ‖xStar - y‖ = ‖y - xStar‖ := by
      rw [norm_sub_rev]
    have hLinear :
        ((Matrix.toEuclideanCLM :
            Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (G[r](y))) (xStar - y) =
          -Matrix.toEuclideanLin (G[r](y)) (y - xStar) := by
      rw [show xStar - y = -(y - xStar) by abel_nf, map_neg]
      rfl
    calc
      ‖Matrix.toEuclideanLin (G[r](y)) (y - xStar) - g[r](y)‖
          = ‖g[r](xStar) - g[r](y) -
              ((Matrix.toEuclideanCLM :
                  Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
                (G[r](y))) (xStar - y)‖ := by
              rw [hGradientZero, hLinear]
              abel_nf
      _ ≤ ((Real.toNNReal L : ℝ) / 2) * ‖xStar - y‖ ^ (2 : ℕ) := hTaylor'
      _ = ((Real.toNNReal L : ℝ) / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
            rw [hnorm_rev]
  have hSplit :
      Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) (y - xStar) - g[r](y) +
          Matrix.toEuclideanLin (S[r](y)) (y - xStar) =
        Matrix.toEuclideanLin (G[r](y)) (y - xStar) - g[r](y) := by
    -- Split `G(y) = A(y) + S(y)` once and regroup the three source terms.
    rw [show G[r](y) = gaussNewtonNormalMatrix r y + S[r](y) by
          simp [leastSquaresHessianMatrix, gaussNewtonNormalMatrix_eq]]
    rw [toEuclideanLin_add_apply]
    abel_nf
  rw [hSplit]
  exact hRemainder

/-- Chapter07 Theorem 7.2.2: let `f(x) = nonlinearLeastSquaresObjective r x = (1 / 2) * ‖r x‖^2`,
assume `r ∈ C²`, `xStar` is a local minimizer of the nonlinear least-squares
problem, the Gauss-Newton iterates `x k` converge to `xStar`, `J(xStar)ᵀ * J(xStar)` is positive
definite, the normal matrix remains positive definite in a neighborhood of `xStar`, and both
`G(x) = leastSquaresHessianMatrix r x` and
`(J(x)ᵀ * J(x))⁻¹ = (gaussNewtonNormalMatrix r x)⁻¹` are Lipschitz in a neighborhood of `xStar`.
Then the one-step error satisfies the source bound, with the matrix norms in the linear
coefficient interpreted as Euclidean (`ℓ₂`) operator norms,
`‖x_(k+1) - xStar‖ ≤ ‖(J(xStar)ᵀ * J(xStar))⁻¹‖ * ‖S(xStar)‖ * ‖x_k - xStar‖ +
O(‖x_k - xStar‖^2)` in the standard eventual-inequality form. -/
theorem gaussNewton_errorNorm_eventually_le_linear_plus_quadratic
    (r : Point → Residual) (x : ℕ → Point) (xStar : Point)
    (hResidualC2 : ContDiff ℝ 2 r)
    (hLocalMin : IsLocalMin (nonlinearLeastSquaresObjective r) xStar)
    (hStep : ∀ k : ℕ, solvesGaussNewtonNormalEquation r (x k) (x (k + 1)))
    (hGramPosDef : (gaussNewtonNormalMatrix r xStar).PosDef)
    (hTendsto : Tendsto x atTop (nhds xStar))
    (hNormalMatrixPosDef :
      ∃ δ > 0, ∀ y : Point,
        y ∈ Metric.ball xStar δ →
          (gaussNewtonNormalMatrix r y).PosDef)
    (hHessianLipschitz :
      ∃ δ > 0, ∃ L > 0, ∀ x y : Point,
        x ∈ Metric.ball xStar δ →
        y ∈ Metric.ball xStar δ →
          ‖G[r](x) - G[r](y)‖ ≤ L * ‖x - y‖)
    (hInverseLipschitz :
      ∃ δ > 0, ∃ L > 0, ∀ x y : Point,
        x ∈ Metric.ball xStar δ →
        y ∈ Metric.ball xStar δ →
          ‖(gaussNewtonNormalMatrix r x)⁻¹ - (gaussNewtonNormalMatrix r y)⁻¹‖ ≤
            L * ‖x - y‖) :
    ∃ C > 0, ∀ᶠ k : ℕ in atTop,
      ‖x (k + 1) - xStar‖ ≤
        gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ +
          C * ‖x k - xStar‖ ^ (2 : ℕ) := by
  let A : Point → Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r
  -- Start from the stationary-point identity supplied by the local minimizer hypothesis.
  have hGradientZero : g[r](xStar) = 0 :=
    gaussNewtonGradient_eq_zero_of_localMin r xStar hResidualC2 hLocalMin
  rcases hNormalMatrixPosDef with ⟨δPos, hδPos, hPosDefNear⟩
  rcases hHessianLipschitz with ⟨δG, hδG, LG, hLG_pos, hGdiff⟩
  rcases hInverseLipschitz with ⟨δInv, hδInv, LI, hLI_pos, hInvDiff⟩
  rcases gaussNewtonStepResidual_quadraticBound_onBall r xStar hResidualC2 hGradientZero
      ⟨δG, hδG, LG, hLG_pos, hGdiff⟩ with
    ⟨δTaylor, hδTaylor, CTaylor, hCTaylor_pos, hTaylor⟩
  let ε : ℝ := min δPos (min δG (min δInv δTaylor))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    refine lt_min hδPos ?_
    refine lt_min hδG ?_
    exact lt_min hδInv hδTaylor
  have hxStarG : xStar ∈ Metric.ball xStar δG := by
    simpa [Metric.mem_ball] using hδG
  have hxStarInv : xStar ∈ Metric.ball xStar δInv := by
    simpa [Metric.mem_ball] using hδInv
  have hAStarUnit : IsUnit (A xStar) := hGramPosDef.isUnit
  let M : ℝ := ‖(A xStar)⁻¹‖ + LI * ε
  let quadraticCoeff : ℝ := M * CTaylor + (M * LG + LI * ‖G[r](xStar)‖)
  have hM_pos : 0 < M := by
    dsimp [M]
    nlinarith [norm_nonneg ((A xStar)⁻¹), hLI_pos, hε_pos]
  have hQuadraticCoeff_pos : 0 < quadraticCoeff := by
    have hTailNonneg : 0 ≤ M * LG + LI * ‖G[r](xStar)‖ := by
      positivity
    dsimp [quadraticCoeff]
    have hLeadPos : 0 < M * CTaylor := by positivity
    linarith
  have hTail :
      ∀ᶠ k : ℕ in atTop, x k ∈ Metric.ball xStar ε := by
    exact hTendsto.eventually (Metric.ball_mem_nhds xStar hε_pos)
  refine ⟨quadraticCoeff, hQuadraticCoeff_pos, hTail.mono ?_⟩
  intro k hxk
  have hxkPos : x k ∈ Metric.ball xStar δPos := by
    exact Metric.ball_subset_ball (by dsimp [ε]; exact min_le_left _ _) hxk
  have hxkG : x k ∈ Metric.ball xStar δG := by
    exact Metric.ball_subset_ball (by dsimp [ε]; exact le_trans (min_le_right _ _) (min_le_left _ _)) hxk
  have hxkInv : x k ∈ Metric.ball xStar δInv := by
    exact Metric.ball_subset_ball
      (by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      hxk
  have hxkTaylor : x k ∈ Metric.ball xStar δTaylor := by
    exact Metric.ball_subset_ball
      (by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      hxk
  have hPosDefk : (A (x k)).PosDef := hPosDefNear (x k) hxkPos
  have hAkUnit : IsUnit (A (x k)) := hPosDefk.isUnit
  have hInvNorm :
      ‖(A (x k))⁻¹‖ ≤ M := by
    have hxk_norm_le : ‖x k - xStar‖ ≤ ε := by
      have hxk_norm_lt : ‖x k - xStar‖ < ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using hxk
      exact le_of_lt hxk_norm_lt
    have hInvDiffk :
        ‖(A (x k))⁻¹ - (A xStar)⁻¹‖ ≤ LI * ‖x k - xStar‖ :=
      hInvDiff (x k) xStar hxkInv hxStarInv
    calc
      ‖(A (x k))⁻¹‖ = ‖((A (x k))⁻¹ - (A xStar)⁻¹) + (A xStar)⁻¹‖ := by
        congr 1
        abel_nf
      _ ≤ ‖(A (x k))⁻¹ - (A xStar)⁻¹‖ + ‖(A xStar)⁻¹‖ := norm_add_le _ _
      _ ≤ LI * ‖x k - xStar‖ + ‖(A xStar)⁻¹‖ := by
        gcongr
      _ ≤ LI * ε + ‖(A xStar)⁻¹‖ := by
        gcongr
      _ = M := by
        dsimp [M]
        ring
  have hTaylork :
      ‖Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
          Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)‖ ≤
        CTaylor * ‖x k - xStar‖ ^ (2 : ℕ) :=
    hTaylor (x k) hxkTaylor
  have hPerturbDiff :
      ‖(A (x k))⁻¹ * S[r](x k) - (A xStar)⁻¹ * S[r](xStar)‖ ≤
        (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ := by
    rw [inverseNormalMatrixMulCorrection_diff_eq_inverseNormalMatrixMulHessian_diff
      (r := r) (xStar := xStar) (y := x k) hAkUnit hAStarUnit]
    exact inverseNormalMatrixMulHessian_diff_le r xStar (x k) M LG LI
      (by positivity) (le_of_lt hLG_pos) (le_of_lt hLI_pos) hInvNorm
      (hGdiff (x k) xStar hxkG hxStarG)
      (hInvDiff (x k) xStar hxkInv hxStarInv)
  have hBaseLinear :
      ‖(A xStar)⁻¹ * S[r](xStar)‖ ≤ gaussNewtonLinearErrorCoefficient r xStar := by
    calc
      ‖(A xStar)⁻¹ * S[r](xStar)‖ ≤ ‖(A xStar)⁻¹‖ * ‖S[r](xStar)‖ := norm_mul_le _ _
      _ = gaussNewtonLinearErrorCoefficient r xStar := by
        rw [gaussNewtonLinearErrorCoefficient_eq]
  have hUpdate :
      x (k + 1) - xStar =
        Matrix.toEuclideanLin ((A (x k))⁻¹)
          (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k)) :=
    gaussNewtonUpdateError_eq_inverseStepResidual r xStar (x k) (x (k + 1)) hAkUnit (hStep k)
  have hCorrectionDecomp :
      Matrix.toEuclideanLin ((A (x k))⁻¹)
          (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k)) =
        Matrix.toEuclideanLin ((A (x k))⁻¹)
          (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
            Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) -
        Matrix.toEuclideanLin (((A (x k))⁻¹) * S[r](x k)) (x k - xStar) := by
    -- Separate the quadratic Taylor residual from the correction term before taking norms.
    calc
      Matrix.toEuclideanLin ((A (x k))⁻¹)
          (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k))
          =
          Matrix.toEuclideanLin ((A (x k))⁻¹)
            ((Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
                Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) -
              Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) := by
              congr 1
              abel_nf
      _ = Matrix.toEuclideanLin ((A (x k))⁻¹)
            (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
              Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) -
          Matrix.toEuclideanLin ((A (x k))⁻¹)
            (Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) := by
              rw [LinearMap.map_sub]
      _ = Matrix.toEuclideanLin ((A (x k))⁻¹)
            (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
              Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) -
          Matrix.toEuclideanLin (((A (x k))⁻¹) * S[r](x k)) (x k - xStar) := by
              rw [toEuclideanLin_mul_apply]
  have hCorrectionNorm :
      ‖Matrix.toEuclideanLin (((A (x k))⁻¹) * S[r](x k)) (x k - xStar)‖ ≤
        gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ +
          (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ ^ (2 : ℕ) := by
    have hBaseApply :
        ‖Matrix.toEuclideanLin ((A xStar)⁻¹ * S[r](xStar)) (x k - xStar)‖ ≤
          gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ := by
      calc
        ‖Matrix.toEuclideanLin ((A xStar)⁻¹ * S[r](xStar)) (x k - xStar)‖
            ≤ ‖(A xStar)⁻¹ * S[r](xStar)‖ * ‖x k - xStar‖ := by
                exact norm_toEuclideanLin_apply_le _ _
        _ ≤ gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ := by
              exact mul_le_mul_of_nonneg_right hBaseLinear (norm_nonneg _)
    have hPerturbApply :
        ‖Matrix.toEuclideanLin
            (((A (x k))⁻¹ * S[r](x k)) - ((A xStar)⁻¹ * S[r](xStar))) (x k - xStar)‖ ≤
          (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ ^ (2 : ℕ) := by
      calc
        ‖Matrix.toEuclideanLin
            (((A (x k))⁻¹ * S[r](x k)) - ((A xStar)⁻¹ * S[r](xStar))) (x k - xStar)‖
            ≤ ‖((A (x k))⁻¹ * S[r](x k)) - ((A xStar)⁻¹ * S[r](xStar))‖ * ‖x k - xStar‖ := by
                exact norm_toEuclideanLin_apply_le _ _
        _ ≤ ((M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖) * ‖x k - xStar‖ := by
              exact mul_le_mul_of_nonneg_right hPerturbDiff (norm_nonneg _)
        _ = (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ ^ (2 : ℕ) := by
              ring
    calc
      ‖Matrix.toEuclideanLin (((A (x k))⁻¹) * S[r](x k)) (x k - xStar)‖
          = ‖Matrix.toEuclideanLin
                ((((A (x k))⁻¹ * S[r](x k)) - ((A xStar)⁻¹ * S[r](xStar))) +
                  ((A xStar)⁻¹ * S[r](xStar))) (x k - xStar)‖ := by
              congr 1
              abel_nf
      _ = ‖Matrix.toEuclideanLin
              (((A (x k))⁻¹ * S[r](x k)) - ((A xStar)⁻¹ * S[r](xStar))) (x k - xStar) +
            Matrix.toEuclideanLin ((A xStar)⁻¹ * S[r](xStar)) (x k - xStar)‖ := by
            rw [toEuclideanLin_add_apply]
      _ ≤ ‖Matrix.toEuclideanLin
              (((A (x k))⁻¹ * S[r](x k)) - ((A xStar)⁻¹ * S[r](xStar))) (x k - xStar)‖ +
            ‖Matrix.toEuclideanLin ((A xStar)⁻¹ * S[r](xStar)) (x k - xStar)‖ := norm_add_le _ _
      _ ≤ (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ ^ (2 : ℕ) +
            gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ := by
            exact add_le_add hPerturbApply hBaseApply
      _ = gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ +
            (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ ^ (2 : ℕ) := by
            ring
  have hResidualNorm :
      ‖Matrix.toEuclideanLin ((A (x k))⁻¹)
          (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
            Matrix.toEuclideanLin (S[r](x k)) (x k - xStar))‖ ≤
        M * CTaylor * ‖x k - xStar‖ ^ (2 : ℕ) := by
    calc
      ‖Matrix.toEuclideanLin ((A (x k))⁻¹)
          (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
            Matrix.toEuclideanLin (S[r](x k)) (x k - xStar))‖
          ≤ ‖(A (x k))⁻¹‖ *
              ‖Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
                  Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)‖ := by
              exact norm_toEuclideanLin_apply_le _ _
      _ ≤ M * (CTaylor * ‖x k - xStar‖ ^ (2 : ℕ)) := by
            exact mul_le_mul hInvNorm hTaylork (norm_nonneg _) (by positivity)
      _ = M * CTaylor * ‖x k - xStar‖ ^ (2 : ℕ) := by
            ring
  -- The verified skeleton now isolates the remaining term as one linear base part and two
  -- quadratic perturbations.
  calc
    ‖x (k + 1) - xStar‖
        = ‖Matrix.toEuclideanLin ((A (x k))⁻¹)
            (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k))‖ := by
              rw [hUpdate]
    _ = ‖Matrix.toEuclideanLin ((A (x k))⁻¹)
            (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
              Matrix.toEuclideanLin (S[r](x k)) (x k - xStar)) -
          Matrix.toEuclideanLin (((A (x k))⁻¹) * S[r](x k)) (x k - xStar)‖ := by
            rw [hCorrectionDecomp]
    _ ≤ ‖Matrix.toEuclideanLin ((A (x k))⁻¹)
            (Matrix.toEuclideanLin (A (x k)) (x k - xStar) - g[r](x k) +
              Matrix.toEuclideanLin (S[r](x k)) (x k - xStar))‖ +
          ‖Matrix.toEuclideanLin (((A (x k))⁻¹) * S[r](x k)) (x k - xStar)‖ := by
            exact norm_sub_le _ _
    _ ≤ M * CTaylor * ‖x k - xStar‖ ^ (2 : ℕ) +
          (gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ +
            (M * LG + LI * ‖G[r](xStar)‖) * ‖x k - xStar‖ ^ (2 : ℕ)) := by
            exact add_le_add hResidualNorm hCorrectionNorm
    _ = gaussNewtonLinearErrorCoefficient r xStar * ‖x k - xStar‖ +
          quadraticCoeff * ‖x k - xStar‖ ^ (2 : ℕ) := by
            dsimp [quadraticCoeff]
            ring

end
