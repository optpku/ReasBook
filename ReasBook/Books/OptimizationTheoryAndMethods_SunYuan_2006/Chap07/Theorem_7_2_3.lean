/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Sequences
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_10
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

open Filter Matrix
open scoped LeastSquares Matrix.Norms.L2Operator

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
variable (r : Point → Residual)

-- Domain sampling for this file:
-- * primary domain: local existence and convergence statements for Gauss-Newton iterate
--   sequences;
-- * sampled owners reused here:
--   `nonlinearLeastSquaresObjective`,
--   `residualJacobianMatrix`,
--   `gaussNewtonNormalMatrix`,
--   `leastSquaresGradient`,
--   `solvesGaussNewtonNormalEquation`,
--   `Matrix.spectrum`;
-- * source/core/bridge triage:
--   - source-facing layer here: the existence theorem for an iterate family `x_k`;
--   - core/canonical owners reused here: the Chapter 7 objective and residual Jacobian owners;
--   - bridge/view layer here: the local one-step error estimates deduced from those core owners;
-- * primitive data here: the domain `D`, residual map `r`, initial point `x0`, and iterate
--   family `x`;
-- * derived API here: the canonical linear-convergence owner `HasLinearConvergenceTo x xStar`
--   together with the source pointwise error bounds `(7.2.18)` and `(7.2.19)`. The one-step
--   semantics themselves are reused from the Chapter 7 owner
--   `solvesGaussNewtonNormalEquation` rather than repackaged in a second owner structure.

/-- Helper for Chapter07 Theorem 7.2.3: the Euclidean action of `J[r](x)` is exactly the Fréchet
derivative `fderiv ℝ r x`. -/
private theorem jacobianApply_eq_fderiv
    (r : Point → Residual) (x v : Point) :
    Matrix.toEuclideanLin (J[r](x)) v = fderiv ℝ r x v := by
  -- Reconstruct the derivative map once from its matrix in the standard Euclidean bases.
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
          (J[r](x)) v =
        (fderiv ℝ r x).toLinearMap v := by
    rw [show J[r](x) = residualJacobianMatrix r x by rfl]
    exact
      congrArg
        (fun L : Point →ₗ[ℝ] Residual => L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
          ((fderiv ℝ r x).toLinearMap))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using hToLin

/-- Helper for Chapter07 Theorem 7.2.3: the continuous-linear-map avatar of `J[r](x)` is exactly
`fderiv ℝ r x`. -/
private theorem jacobianClm_eq_fderiv
    (r : Point → Residual) (x : Point) :
    (Matrix.toEuclideanLin (J[r](x))).toContinuousLinearMap = fderiv ℝ r x := by
  -- Extensionality moves the Jacobian-versus-derivative comparison to the pointwise action.
  ext v i
  exact congrArg (fun z : Residual => z i) (jacobianApply_eq_fderiv r x v)

/-- Helper for Chapter07 Theorem 7.2.3: pairing against `Aᵀ w` agrees with pairing `w` against
`A v`. -/
private theorem inner_toEuclideanLin_transpose_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Residual) (v : Point) :
    inner ℝ (Matrix.toEuclideanLin A.transpose w) v =
      inner ℝ w (Matrix.toEuclideanLin A v) := by
  have hAdjoint :
      LinearMap.adjoint (Matrix.toEuclideanLin A.transpose) = Matrix.toEuclideanLin A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A.transpose)).symm
  -- Rewrite the transpose action through the adjoint before evaluating the inner product.
  calc
    inner ℝ (Matrix.toEuclideanLin A.transpose w) v
        = inner ℝ w ((Matrix.toEuclideanLin A.transpose).adjoint v) := by
            symm
            simpa using
              (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A.transpose) w v)
    _ = inner ℝ w (Matrix.toEuclideanLin A v) := by
          rw [hAdjoint]

/-- Helper for Chapter07 Theorem 7.2.3: composing two Euclidean matrix actions is the same as
acting by the product matrix. -/
private theorem toEuclideanLin_mul_apply
    {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) =
      Matrix.toEuclideanLin (A * B) v := by
  -- Compare both sides through the coordinate `mulVec` model once.
  apply WithLp.ofLp_injective
  simp [Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal)), Matrix.mulVec_mulVec]

/-- Helper for Chapter07 Theorem 7.2.3: the Euclidean action of a matrix sum is the sum of the
two Euclidean actions. -/
private theorem toEuclideanLin_add_apply
    {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (A + B) v =
      Matrix.toEuclideanLin A v + Matrix.toEuclideanLin B v := by
  -- Compare both sides through the coordinate `mulVec` model once.
  apply WithLp.ofLp_injective
  simp [Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))]

/-- Helper for Chapter07 Theorem 7.2.3: the Euclidean matrix action is bounded by the matrix
`ℓ₂` operator norm times the vector norm. -/
private theorem norm_toEuclideanLin_apply_le
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A v‖ ≤ ‖A‖ * ‖v‖ := by
  -- Move once to the continuous-linear-map model where the operator-norm inequality is canonical.
  calc
    ‖Matrix.toEuclideanLin A v‖
        = ‖(((Matrix.toEuclideanLin :
            Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ]
              EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).trans
              LinearMap.toContinuousLinearMap) A v)‖ := by
            rfl
    _ ≤ ‖(((Matrix.toEuclideanLin :
          Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ]
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)).trans
            LinearMap.toContinuousLinearMap) A)‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖A‖ * ‖v‖ := by
          rw [Matrix.l2_opNorm_def]

/-- Helper for Chapter07 Theorem 7.2.3: a uniform quadratic lower bound on the Euclidean action of
`A` forces invertibility and bounds the inverse operator norm by `1 / μ`. -/
private theorem isUnit_and_inv_norm_le_of_quadratic_lower
    (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hLower :
      ∀ u : Point, μ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (Matrix.toEuclideanLin A u) u) :
    IsUnit A ∧ ‖A⁻¹‖ ≤ 1 / μ := by
  have hKernelZero :
      ∀ z : Fin n → ℝ, A.mulVec z = 0 → z = 0 := by
    intro z hz
    by_contra hz_ne
    let u : Point := WithLp.toLp 2 z
    have hu_ne : u ≠ 0 := by
      simpa [u] using hz_ne
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hLeftPos : 0 < μ * ‖u‖ ^ (2 : ℕ) := by
      positivity
    have hAu_zero : Matrix.toEuclideanLin A u = 0 := by
      apply WithLp.ofLp_injective
      simpa [u, Matrix.ofLp_toEuclideanCLM]
        using hz
    have hInnerZero : inner ℝ (Matrix.toEuclideanLin A u) u = 0 := by
      simp [hAu_zero]
    have hLoweru := hLower u
    linarith
  have hInjective : Function.Injective A.mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hKernelZero
    simpa [Matrix.mulVec_sub, hxy]
  have hAUnit : IsUnit A := (Matrix.mulVec_injective_iff_isUnit).mp hInjective
  letI := hAUnit.invertible
  have hInvApply :
      ∀ v : Point, ‖Matrix.toEuclideanLin (A⁻¹) v‖ ≤ (1 / μ) * ‖v‖ := by
    intro v
    let u : Point := Matrix.toEuclideanLin (A⁻¹) v
    by_cases hu : u = 0
    · simp [u, hu, hμ.le]
      positivity
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hAu : Matrix.toEuclideanLin A u = v := by
      dsimp [u]
      rw [toEuclideanLin_mul_apply]
      simpa [Matrix.inv_mul_of_invertible]
    have hBound :
        μ * ‖u‖ ^ (2 : ℕ) ≤ ‖v‖ * ‖u‖ := by
      calc
        μ * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (Matrix.toEuclideanLin A u) u := hLower u
        _ = inner ℝ v u := by rw [hAu]
        _ ≤ ‖v‖ * ‖u‖ := real_inner_le_norm _ _
    have hLinear : μ * ‖u‖ ≤ ‖v‖ := by
      nlinarith
    have hDiv : ‖u‖ ≤ ‖v‖ / μ := by
      exact (le_div_iff₀ hμ).2 (by nlinarith)
    simpa [u, div_eq_mul_inv, mul_comm] using hDiv
  refine ⟨hAUnit, ?_⟩
  rw [← Matrix.l2_opNorm_toEuclideanCLM (A⁻¹)]
  exact
    ContinuousLinearMap.opNorm_le_bound
      ((Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (A⁻¹))
      (by positivity) hInvApply

/-- Helper for Chapter07 Theorem 7.2.3: applying the inverse Euclidean matrix action to the
forward Euclidean action of an invertible matrix cancels back to the original vector. -/
private theorem inverseToEuclideanLin_apply_cancel
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

/-- Helper for Chapter07 Theorem 7.2.3: the Taylor remainder of `r` along the segment from `y`
to `xStar` is bounded by `(γ / 2) * ‖y - xStar‖²`. -/
private theorem residualQuadraticRemainderBound
    (D : Set Point) (r : Point → Residual) (xStar : Point) (γ : ℝ)
    (hOpen : IsOpen D) (hConvex : Convex ℝ D)
    (hResidualC2 : ContDiffOn ℝ 2 r D)
    (hJLipschitz :
      ∀ x ∈ D, ∀ y ∈ D,
        ‖(Matrix.toEuclideanLin
            (J[r](x) - J[r](y))).toContinuousLinearMap‖ ≤
          γ * ‖x - y‖)
    (hγ_nonneg : 0 ≤ γ)
    (hxStar : xStar ∈ D) :
    ∀ y : Point, y ∈ D →
      ‖r xStar - r y - Matrix.toEuclideanLin (J[r](y)) (xStar - y)‖ ≤
        (γ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
  intro y hy
  have hDiff : DifferentiableOn ℝ r D := hResidualC2.differentiableOn two_ne_zero
  have hLip :
      LipschitzOnWith (Real.toNNReal γ) (fderiv ℝ r) D := by
    -- Route correction: express the Lipschitz hypothesis directly on `fderiv ℝ r`, so the
    -- Chapter 1 Taylor-remainder theorem applies without matrix-norm detours.
    refine
      LipschitzOnWith.of_dist_le'
        (s := D) (f := fun z : Point ↦ fderiv ℝ r z) (K := γ) ?_
    intro u hu v hv
    calc
      dist (fderiv ℝ r u) (fderiv ℝ r v)
          = ‖fderiv ℝ r u - fderiv ℝ r v‖ := by
              simp [dist_eq_norm]
      _ = ‖(Matrix.toEuclideanLin (J[r](u) - J[r](v))).toContinuousLinearMap‖ := by
            rw [← jacobianClm_eq_fderiv (r := r) (x := u),
              ← jacobianClm_eq_fderiv (r := r) (x := v)]
            simp
      _ ≤ γ * dist u v := by
            simpa [dist_eq_norm] using hJLipschitz u hu v hv
  have hyEq : y + (xStar - y) = xStar := by
    abel_nf
  have hTaylor :=
    quadraticRemainderBound_of_fderiv_lipschitzOn
      D
      r
      y
      (xStar - y)
      (Real.toNNReal γ)
      hOpen
      hConvex
      hy
      hDiff
      hLip
      (by
        have hxd : y + (xStar - y) ∈ D := by
          simpa [hyEq] using hxStar
        exact hxd)
  have hnorm_rev : ‖xStar - y‖ = ‖y - xStar‖ := by
    rw [norm_sub_rev]
  -- Rewrite the Taylor remainder into the source `xStar - y` form used by the theorem.
  calc
    ‖r xStar - r y - Matrix.toEuclideanLin (J[r](y)) (xStar - y)‖
        ≤ (γ / 2) * ‖xStar - y‖ ^ (2 : ℕ) := by
            simpa [hyEq, jacobianApply_eq_fderiv, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc, max_eq_left hγ_nonneg] using hTaylor
    _ = (γ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
          rw [hnorm_rev]

/-- Helper for Chapter07 Theorem 7.2.3: the root normal matrix inherits the source smallest
eigenvalue `lam` as a quadratic lower bound on the Euclidean action. -/
private theorem gaussNewtonNormalMatrix_rootQuadraticLower
    (r : Point → Residual) (xStar : Point) (lam : ℝ)
    (hSmallest :
      IsLeast (spectrum ℝ (gaussNewtonNormalMatrix r xStar)) lam)
    (hlam_pos : 0 < lam) :
    ∀ u : Point,
      lam * ‖u‖ ^ (2 : ℕ) ≤
        inner ℝ (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r xStar) u) u := by
  let A : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r xStar
  have hPosSemidef : A.PosSemidef := by
    -- The root normal matrix is the Gram matrix `J(xStar)ᵀ * J(xStar)`.
    simpa [A, gaussNewtonNormalMatrix_eq, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (J[r](xStar)))
  have hAUnit : IsUnit A := by
    -- A positive smallest spectral point excludes `0` from the spectrum.
    apply (spectrum.zero_notMem_iff ℝ).mp
    intro hZero
    exact (not_le_of_gt hlam_pos) (hSmallest.2 hZero)
  have hPosDef : A.PosDef := (Matrix.PosSemidef.posDef_iff_isUnit hPosSemidef).2 hAUnit
  have hLeastPosDef :
      IsLeast (Set.range (posDefEigenvalues A hPosDef)) lam := by
    -- Rewrite the spectral endpoint through the Chapter 1 positive-definite eigenvalue owner.
    have hspectrum :
        spectrum ℝ A = Set.range (posDefEigenvalues A hPosDef) := by
      simpa [posDefEigenvalues_def] using hPosDef.isHermitian.spectrum_eq_image_range
    rw [← hspectrum]
    exact hSmallest
  intro u
  by_cases hu : u = 0
  · -- The zero direction contributes zero on both sides.
    subst hu
    simp
  · have hRay :=
      leastPosDefEigenvalue_le_euclideanRayleighQuotient A hPosDef lam hLeastPosDef u hu
    have hu_sq_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
      exact pow_pos (norm_pos_iff.mpr hu) 2
    -- Clear the positive denominator of the Rayleigh quotient inequality.
    exact (le_div_iff₀ hu_sq_pos).mp hRay

/-- Helper for Chapter07 Theorem 7.2.3: the normal matrix perturbation from `xStar` to `y` is
controlled by the Jacobian Lipschitz constant and the uniform Jacobian norm bound. -/
private theorem gaussNewtonNormalMatrix_difference_split
    (r : Point → Residual) (xStar y : Point) :
    gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar =
      (J[r](y)).transpose * (J[r](y) - J[r](xStar)) +
        (J[r](y) - J[r](xStar)).transpose * J[r](xStar) := by
  let JY : Matrix (Fin m) (Fin n) ℝ := J[r](y)
  let JStar : Matrix (Fin m) (Fin n) ℝ := J[r](xStar)
  -- Expand the Gram-matrix difference once around `xStar` before taking norms.
  calc
    gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar
        = JY.transpose * JY - JStar.transpose * JStar := by
            simp [JY, JStar, gaussNewtonNormalMatrix_eq]
    _ = (JY.transpose * JY - JY.transpose * JStar) +
          (JY.transpose * JStar - JStar.transpose * JStar) := by
          abel_nf
    _ = JY.transpose * (JY - JStar) + (JY.transpose - JStar.transpose) * JStar := by
          have hMulSub :
              JY.transpose * JY - JY.transpose * JStar = JY.transpose * (JY - JStar) := by
            ext i j
            simp [Matrix.mul_apply]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          have hSubMul :
              JY.transpose * JStar - JStar.transpose * JStar =
                (JY.transpose - JStar.transpose) * JStar := by
            ext i j
            simp [Matrix.mul_apply]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          rw [hMulSub, hSubMul]
    _ = JY.transpose * (JY - JStar) + (JY - JStar).transpose * JStar := by
          have hTransposeSub :
              JY.transpose - JStar.transpose = (JY - JStar).transpose := by
            ext i j
            simp [sub_eq_add_neg]
          rw [hTransposeSub]
    _ = (J[r](y)).transpose * (J[r](y) - J[r](xStar)) +
          (J[r](y) - J[r](xStar)).transpose * J[r](xStar) := by
          simp [JY, JStar]

/-- Helper for Chapter07 Theorem 7.2.3: the normal matrix perturbation from `xStar` to `y` is
controlled by the Jacobian Lipschitz constant and the uniform Jacobian norm bound. -/
private theorem gaussNewtonNormalMatrix_perturbationBound
    (D : Set Point) (r : Point → Residual) (xStar : Point) (α γ : ℝ)
    (hxStar : xStar ∈ D)
    (hJLipschitz :
      ∀ x ∈ D, ∀ y ∈ D,
        ‖(Matrix.toEuclideanLin
            (J[r](x) - J[r](y))).toContinuousLinearMap‖ ≤
          γ * ‖x - y‖)
    (hJBound :
      ∀ x : Point, x ∈ D →
        ‖(Matrix.toEuclideanLin (J[r](x))).toContinuousLinearMap‖ ≤ α)
    (hγ_nonneg : 0 ≤ γ)
    (hα_nonneg : 0 ≤ α)
    {y : Point} (hy : y ∈ D) :
    ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ ≤
      (2 * α * γ) * ‖y - xStar‖ := by
  let JY : Matrix (Fin m) (Fin n) ℝ := J[r](y)
  let JStar : Matrix (Fin m) (Fin n) ℝ := J[r](xStar)
  let Δ : Matrix (Fin m) (Fin n) ℝ := JY - JStar
  let d : ℝ := ‖y - xStar‖
  have hJY_bound :
      ‖JY‖ ≤ α := by
    have hBound := hJBound y hy
    simpa [Matrix.l2_opNorm_def, JY] using hBound
  have hJStar_bound :
      ‖JStar‖ ≤ α := by
    have hBound := hJBound xStar hxStar
    simpa [Matrix.l2_opNorm_def, JStar] using hBound
  have hΔ_bound :
      ‖Δ‖ ≤ γ * d := by
    have hLip := hJLipschitz y hy xStar hxStar
    simpa [Matrix.l2_opNorm_def, Δ, d] using hLip
  have hJYTranspose :
      ‖JY.transpose‖ = ‖JY‖ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, JY] using
      Matrix.l2_opNorm_conjTranspose JY
  have hΔTranspose :
      ‖Δ.transpose‖ = ‖Δ‖ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Δ] using
      Matrix.l2_opNorm_conjTranspose Δ
  have hTerm1 :
      ‖JY.transpose * Δ‖ ≤ α * (γ * d) := by
    calc
      ‖JY.transpose * Δ‖ ≤ ‖JY.transpose‖ * ‖Δ‖ := by
        simpa using Matrix.l2_opNorm_mul (JY.transpose) Δ
      _ = ‖JY‖ * ‖Δ‖ := by rw [hJYTranspose]
      _ ≤ α * ‖Δ‖ := by
            exact mul_le_mul_of_nonneg_right hJY_bound (norm_nonneg _)
      _ ≤ α * (γ * d) := by
            exact mul_le_mul_of_nonneg_left hΔ_bound hα_nonneg
  have hTerm2 :
      ‖Δ.transpose * JStar‖ ≤ (γ * d) * α := by
    calc
      ‖Δ.transpose * JStar‖ ≤ ‖Δ.transpose‖ * ‖JStar‖ := by
        simpa using Matrix.l2_opNorm_mul (Δ.transpose) JStar
      _ = ‖Δ‖ * ‖JStar‖ := by rw [hΔTranspose]
      _ ≤ (γ * d) * ‖JStar‖ := by
            exact mul_le_mul_of_nonneg_right hΔ_bound (norm_nonneg _)
      _ ≤ (γ * d) * α := by
            exact mul_le_mul_of_nonneg_left hJStar_bound (by positivity)
  -- Route correction: consume the standalone split lemma so the estimate is pure norm arithmetic.
  calc
    ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖
        = ‖JY.transpose * Δ + Δ.transpose * JStar‖ := by
            simpa [JY, JStar, Δ] using
              congrArg norm
                (gaussNewtonNormalMatrix_difference_split (r := r) (xStar := xStar) (y := y))
    _ ≤ ‖JY.transpose * Δ‖ + ‖Δ.transpose * JStar‖ := norm_add_le _ _
    _ ≤ α * (γ * d) + (γ * d) * α := by
          exact add_le_add hTerm1 hTerm2
    _ = (2 * α * γ) * d := by
          ring

/-- Helper for Chapter07 Theorem 7.2.3: the explicit inverse Gauss-Newton update rewrites its
error as the inverse normal matrix applied to the normal-equation residual. -/
private theorem gaussNewtonInverseAction_sub_apply
    (A : Matrix (Fin n) (Fin n) ℝ)
    (u w : Point)
    (hA : IsUnit A) :
    Matrix.toEuclideanLin (A⁻¹) (Matrix.toEuclideanLin A u - w) =
      u - Matrix.toEuclideanLin (A⁻¹) w := by
  letI := hA.invertible
  -- Route correction: pay the CLM-to-`toEuclideanLin` cancellation cost once in this rewrite
  -- helper, then reuse it in the update-error theorem and later consumer estimates.
  calc
    Matrix.toEuclideanLin (A⁻¹) (Matrix.toEuclideanLin A u - w)
        = Matrix.toEuclideanLin (A⁻¹)
            ((((Matrix.toEuclideanCLM :
                Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) u) - w) := by
              rfl
    _ = Matrix.toEuclideanLin (A⁻¹)
          (((Matrix.toEuclideanCLM :
              Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) A) u) -
        Matrix.toEuclideanLin (A⁻¹) w := by
          exact (Matrix.toEuclideanLin (A⁻¹)).map_sub _ _
    _ = u - Matrix.toEuclideanLin (A⁻¹) w := by
          rw [inverseToEuclideanLin_apply_cancel (A := A) hA u]

/-- Helper for Chapter07 Theorem 7.2.3: the explicit inverse Gauss-Newton update rewrites its
error as the inverse normal matrix applied to the normal-equation residual. -/
private theorem gaussNewtonUpdateError_eq_inverseStepResidual
    (r : Point → Residual) (xStar y : Point)
    (hAy : IsUnit (gaussNewtonNormalMatrix r y)) :
    let A : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r y
    y - Matrix.toEuclideanLin (A⁻¹) (g[r](y)) - xStar =
      Matrix.toEuclideanLin (A⁻¹)
        (Matrix.toEuclideanLin A (y - xStar) - g[r](y)) := by
  let A : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r y
  -- Route correction: reuse the dedicated subtraction-form inverse-action bridge instead of
  -- replaying the longer CLM cancellation from Theorem 7.2.2.
  calc
    y - Matrix.toEuclideanLin (A⁻¹) (g[r](y)) - xStar
        = (y - xStar) - Matrix.toEuclideanLin (A⁻¹) (g[r](y)) := by
            abel_nf
    _ = Matrix.toEuclideanLin (A⁻¹)
          (Matrix.toEuclideanLin A (y - xStar) - g[r](y)) := by
            symm
            exact gaussNewtonInverseAction_sub_apply
              (A := A) (u := y - xStar) (w := g[r](y)) hAy

/-- Helper for Chapter07 Theorem 7.2.3: the radius hypothesis absorbs the quadratic term in the
source one-step estimate into the linear contraction coefficient. -/
private theorem gaussNewtonQuadraticAbsorber
    (lam σ α γ c d : ℝ)
    (hd_nonneg : 0 ≤ d)
    (hlam_pos : 0 < lam)
    (hα_nonneg : 0 ≤ α)
    (hγ_nonneg : 0 ≤ γ)
    (hc_lower : 1 < c)
    (hd_le : d ≤ (lam - c * σ) / (c * α * γ + 1)) :
    (c * α * γ / (2 * lam)) * d ^ (2 : ℕ) ≤
      ((lam - c * σ) / (2 * lam)) * d := by
  have hc_pos : 0 < c := lt_trans zero_lt_one hc_lower
  have hcoeff_nonneg : 0 ≤ c * α * γ := by
    positivity
  have hden_pos : 0 < c * α * γ + 1 := by
    positivity
  have hscaled :
      d * (c * α * γ + 1) ≤ lam - c * σ := by
    exact (le_div_iff₀ hden_pos).mp hd_le
  have hcoeff_le :
      c * α * γ * d ≤ d * (c * α * γ + 1) := by
    have htmp :
        d * (c * α * γ) ≤ d * (c * α * γ + 1) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith) hd_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
  have hmain :
      c * α * γ * d ≤ lam - c * σ := by
    exact le_trans hcoeff_le hscaled
  -- Convert the scalar absorber inequality into the final `(7.2.19)` coefficient form.
  have hscale_nonneg : 0 ≤ d / (2 * lam) := by
    positivity
  have hscaled_final :
      (c * α * γ * d) * (d / (2 * lam)) ≤
        (lam - c * σ) * (d / (2 * lam)) := by
    exact mul_le_mul_of_nonneg_right hmain hscale_nonneg
  simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled_final

/-- Helper for Chapter07 Theorem 7.2.3: once the current normal matrix is invertible with
`‖A(y)⁻¹‖ ≤ c / lam`, the explicit Gauss-Newton step satisfies the source one-step estimates
`(7.2.18)` and `(7.2.19)` on the working ball. -/
private theorem gaussNewtonInverseStep_estimates
    (D : Set Point) (r : Point → Residual) (xStar : Point)
    (lam σ α γ c ε : ℝ)
    (hOpen : IsOpen D)
    (hConvex : Convex ℝ D)
    (hxStar : xStar ∈ D)
    (hResidualC2 : ContDiffOn ℝ 2 r D)
    (hJBound :
      ∀ x : Point, x ∈ D →
        ‖(Matrix.toEuclideanLin (J[r](x))).toContinuousLinearMap‖ ≤ α)
    (hStationary : g[r](xStar) = 0)
    (hResidualLinearization :
      ∀ x : Point, x ∈ D →
        ‖Matrix.toEuclideanLin
            ((J[r](x) - J[r](xStar))ᵀ) (r xStar)‖ ≤
          σ * ‖x - xStar‖)
    (hJLipschitz :
      ∀ x ∈ D, ∀ y ∈ D,
        ‖(Matrix.toEuclideanLin
            (J[r](x) - J[r](y))).toContinuousLinearMap‖ ≤
          γ * ‖x - y‖)
    (hγ_nonneg : 0 ≤ γ)
    (hlam_pos : 0 < lam)
    (hc_lower : 1 < c)
    (hGapRadius :
      ε ≤ (lam - c * σ) / (c * α * γ + 1))
    {y : Point}
    (hyD : y ∈ D)
    (hyBall : y ∈ Metric.ball xStar ε)
    (hAy : IsUnit (gaussNewtonNormalMatrix r y))
    (hInvNorm : ‖(gaussNewtonNormalMatrix r y)⁻¹‖ ≤ c / lam) :
    let yNext :=
      y - Matrix.toEuclideanLin ((gaussNewtonNormalMatrix r y)⁻¹) (g[r](y))
    ‖yNext - xStar‖ ≤
        (c * σ / lam) * ‖y - xStar‖ +
          (c * α * γ / (2 * lam)) * ‖y - xStar‖ ^ (2 : ℕ) ∧
      ‖yNext - xStar‖ ≤
        ((c * σ + lam) / (2 * lam)) * ‖y - xStar‖ := by
  let A : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r y
  let JY : Matrix (Fin m) (Fin n) ℝ := J[r](y)
  let JStar : Matrix (Fin m) (Fin n) ℝ := J[r](xStar)
  let yNext :=
    y - Matrix.toEuclideanLin ((gaussNewtonNormalMatrix r y)⁻¹) (g[r](y))
  let remainder : Residual :=
    r xStar - r y - Matrix.toEuclideanLin JY (xStar - y)
  have hc_pos : 0 < c := lt_trans zero_lt_one hc_lower
  have hα_nonneg : 0 ≤ α := by
    have hBound := hJBound xStar hxStar
    nlinarith [norm_nonneg ((Matrix.toEuclideanLin (J[r](xStar))).toContinuousLinearMap)]
  have hyNorm_lt : ‖y - xStar‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hyBall
  have hyNorm_le : ‖y - xStar‖ ≤ ε := le_of_lt hyNorm_lt
  have hGap :
      ‖y - xStar‖ ≤ (lam - c * σ) / (c * α * γ + 1) := by
    exact le_trans hyNorm_le hGapRadius
  have hLinearTerm :
      ‖Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar)‖ ≤
        σ * ‖y - xStar‖ := by
    simpa [JY, JStar] using hResidualLinearization y hyD
  have hRemainder :
      ‖remainder‖ ≤ (γ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
    simpa [JY, remainder] using
      residualQuadraticRemainderBound D r xStar γ hOpen hConvex hResidualC2
        hJLipschitz hγ_nonneg hxStar y hyD
  have hJTransposeNorm :
      ‖JY.transpose‖ = ‖JY‖ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, JY] using
      Matrix.l2_opNorm_conjTranspose JY
  have hJTransposeBound :
      ‖JY.transpose‖ ≤ α := by
    have hBound := hJBound y hyD
    simpa [Matrix.l2_opNorm_def, JY, hJTransposeNorm] using hBound
  have hRemainderImage :
      ‖Matrix.toEuclideanLin JY.transpose remainder‖ ≤
        α * ((γ / 2) * ‖y - xStar‖ ^ (2 : ℕ)) := by
    calc
      ‖Matrix.toEuclideanLin JY.transpose remainder‖
          ≤ ‖JY.transpose‖ * ‖remainder‖ := norm_toEuclideanLin_apply_le _ _
      _ ≤ α * ‖remainder‖ := by
            exact mul_le_mul_of_nonneg_right hJTransposeBound (norm_nonneg _)
      _ ≤ α * ((γ / 2) * ‖y - xStar‖ ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hRemainder hα_nonneg
  have hRemainder_expand :
      Matrix.toEuclideanLin JY.transpose remainder =
        Matrix.toEuclideanLin JY.transpose (r xStar) - g[r](y) +
          Matrix.toEuclideanLin A (y - xStar) := by
    have hAlt :
        remainder = r xStar - r y + Matrix.toEuclideanLin JY (y - xStar) := by
      dsimp [remainder]
      rw [show xStar - y = -(y - xStar) by abel_nf, map_neg]
      abel_nf
    -- Rewrite the Taylor remainder into the source bracket used by the one-step estimate.
    calc
      Matrix.toEuclideanLin JY.transpose remainder
          = Matrix.toEuclideanLin JY.transpose
              (r xStar - r y + Matrix.toEuclideanLin JY (y - xStar)) := by
                rw [hAlt]
      _ = Matrix.toEuclideanLin JY.transpose (r xStar - r y) +
            Matrix.toEuclideanLin JY.transpose (Matrix.toEuclideanLin JY (y - xStar)) := by
              rw [LinearMap.map_add]
      _ = (Matrix.toEuclideanLin JY.transpose (r xStar) -
            Matrix.toEuclideanLin JY.transpose (r y)) +
            Matrix.toEuclideanLin JY.transpose (Matrix.toEuclideanLin JY (y - xStar)) := by
              rw [LinearMap.map_sub]
      _ = Matrix.toEuclideanLin JY.transpose (r xStar) - g[r](y) +
            Matrix.toEuclideanLin A (y - xStar) := by
              rw [toEuclideanLin_mul_apply]
              simp [A, JY, leastSquaresGradient, gaussNewtonNormalMatrix_eq]
  have hStationary_split :
      -Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
          Matrix.toEuclideanLin JY.transpose (r xStar) =
        0 := by
    have hSplit :
        Matrix.toEuclideanLin JY.transpose (r xStar) =
          Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
            Matrix.toEuclideanLin JStar.transpose (r xStar) := by
      have hMat :
          JY.transpose = ((JY - JStar)ᵀ) + JStar.transpose := by
        ext i j
        simp [JY, JStar, sub_eq_add_neg]
      calc
        Matrix.toEuclideanLin JY.transpose (r xStar)
            = Matrix.toEuclideanLin (((JY - JStar)ᵀ) + JStar.transpose) (r xStar) := by
                rw [hMat]
        _ = Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
              Matrix.toEuclideanLin JStar.transpose (r xStar) := by
              rw [toEuclideanLin_add_apply]
    calc
      -Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
          Matrix.toEuclideanLin JY.transpose (r xStar)
          = -Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
              (Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
                Matrix.toEuclideanLin JStar.transpose (r xStar)) := by
                  rw [hSplit]
      _ = Matrix.toEuclideanLin JStar.transpose (r xStar) := by
            abel_nf
      _ = g[r](xStar) := by
            rfl
      _ = 0 := hStationary
  have hBracket :
      -Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
          Matrix.toEuclideanLin JY.transpose remainder =
        Matrix.toEuclideanLin A (y - xStar) - g[r](y) := by
    -- Combine the stationary part and the quadratic Taylor remainder into the source bracket.
    calc
      -Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
          Matrix.toEuclideanLin JY.transpose remainder
          = -Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
              (Matrix.toEuclideanLin JY.transpose (r xStar) - g[r](y) +
                Matrix.toEuclideanLin A (y - xStar)) := by
                  rw [hRemainder_expand]
      _ = (-Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
            Matrix.toEuclideanLin JY.transpose (r xStar)) +
            (-g[r](y) + Matrix.toEuclideanLin A (y - xStar)) := by
            abel_nf
      _ = Matrix.toEuclideanLin A (y - xStar) - g[r](y) := by
            rw [hStationary_split]
            abel_nf
  have hBracketNorm :
      ‖Matrix.toEuclideanLin A (y - xStar) - g[r](y)‖ ≤
        σ * ‖y - xStar‖ + (α * γ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
    calc
      ‖Matrix.toEuclideanLin A (y - xStar) - g[r](y)‖
          = ‖-Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar) +
              Matrix.toEuclideanLin JY.transpose remainder‖ := by
                rw [hBracket]
      _ ≤ ‖-Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar)‖ +
            ‖Matrix.toEuclideanLin JY.transpose remainder‖ := norm_add_le _ _
      _ = ‖Matrix.toEuclideanLin ((JY - JStar)ᵀ) (r xStar)‖ +
            ‖Matrix.toEuclideanLin JY.transpose remainder‖ := by
            rw [norm_neg]
      _ ≤ σ * ‖y - xStar‖ +
            α * ((γ / 2) * ‖y - xStar‖ ^ (2 : ℕ)) := by
              exact add_le_add hLinearTerm hRemainderImage
      _ = σ * ‖y - xStar‖ + (α * γ / 2) * ‖y - xStar‖ ^ (2 : ℕ) := by
            ring
  have hFirst :
      ‖yNext - xStar‖ ≤
        (c * σ / lam) * ‖y - xStar‖ +
          (c * α * γ / (2 * lam)) * ‖y - xStar‖ ^ (2 : ℕ) := by
    -- Rewrite the explicit update first, then consume the source bracket bounds termwise.
    calc
      ‖yNext - xStar‖
          = ‖Matrix.toEuclideanLin (A⁻¹)
              (Matrix.toEuclideanLin A (y - xStar) - g[r](y))‖ := by
                rw [gaussNewtonUpdateError_eq_inverseStepResidual
                  (r := r) (xStar := xStar) (y := y) hAy]
      _ ≤ ‖A⁻¹‖ * ‖Matrix.toEuclideanLin A (y - xStar) - g[r](y)‖ := by
            exact norm_toEuclideanLin_apply_le _ _
      _ ≤ (c / lam) *
            (σ * ‖y - xStar‖ + (α * γ / 2) * ‖y - xStar‖ ^ (2 : ℕ)) := by
            exact mul_le_mul hInvNorm hBracketNorm (norm_nonneg _) (by positivity)
      _ = (c * σ / lam) * ‖y - xStar‖ +
            (c * α * γ / (2 * lam)) * ‖y - xStar‖ ^ (2 : ℕ) := by
            ring
  have hSecond :
      ‖yNext - xStar‖ ≤
        ((c * σ + lam) / (2 * lam)) * ‖y - xStar‖ := by
    calc
      ‖yNext - xStar‖
          ≤ (c * σ / lam) * ‖y - xStar‖ +
              (c * α * γ / (2 * lam)) * ‖y - xStar‖ ^ (2 : ℕ) := hFirst
      _ ≤ (c * σ / lam) * ‖y - xStar‖ +
            ((lam - c * σ) / (2 * lam)) * ‖y - xStar‖ := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left
                  (gaussNewtonQuadraticAbsorber lam σ α γ c ‖y - xStar‖
                    (norm_nonneg _) hlam_pos hα_nonneg hγ_nonneg hc_lower hGap)
                  ((c * σ / lam) * ‖y - xStar‖)
      _ = ((c * σ + lam) / (2 * lam)) * ‖y - xStar‖ := by
            ring
  exact ⟨hFirst, hSecond⟩

/-- Helper for Chapter07 Theorem 7.2.3: on a sufficiently small ball inside `D`, the Gauss-Newton
normal matrices stay invertible and their inverse norms are bounded by `c / lam`. -/
private theorem normalMatrixInverseControlNearStar
    (D : Set Point) (r : Point → Residual) (xStar : Point) (lam α γ c : ℝ)
    (hOpen : IsOpen D)
    (hxStar : xStar ∈ D)
    (hJLipschitz :
      ∀ x ∈ D, ∀ y ∈ D,
        ‖(Matrix.toEuclideanLin
            (J[r](x) - J[r](y))).toContinuousLinearMap‖ ≤
          γ * ‖x - y‖)
    (hJBound :
      ∀ x : Point, x ∈ D →
        ‖(Matrix.toEuclideanLin (J[r](x))).toContinuousLinearMap‖ ≤ α)
    (hSmallest :
      IsLeast (spectrum ℝ (gaussNewtonNormalMatrix r xStar)) lam)
    (hγ_nonneg : 0 ≤ γ)
    (hα_nonneg : 0 ≤ α)
    (hlam_pos : 0 < lam)
    (hc_lower : 1 < c) :
    ∃ ε1 > 0, ∀ y : Point, y ∈ Metric.ball xStar ε1 →
        y ∈ D ∧ IsUnit (gaussNewtonNormalMatrix r y) ∧
        ‖(gaussNewtonNormalMatrix r y)⁻¹‖ ≤ c / lam := by
  let τ : ℝ := lam * (c - 1) / c
  have hc_pos : 0 < c := lt_trans zero_lt_one hc_lower
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    positivity
  rcases Metric.mem_nhds_iff.mp (hOpen.mem_nhds hxStar) with ⟨εD, hεD_pos, hεD_ball⟩
  let εPert : ℝ := τ / (2 * α * γ + 1)
  let ε1 : ℝ := min εD εPert
  have hεPert_pos : 0 < εPert := by
    dsimp [εPert]
    positivity
  have hε1_pos : 0 < ε1 := by
    exact lt_min hεD_pos hεPert_pos
  refine ⟨ε1, hε1_pos, ?_⟩
  intro y hyBall
  have hyD : y ∈ D := by
    exact hεD_ball (Metric.ball_subset_ball (min_le_left _ _) hyBall)
  have hyNorm_lt : ‖y - xStar‖ < ε1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hyBall
  have hyNorm_le : ‖y - xStar‖ ≤ ε1 := le_of_lt hyNorm_lt
  have hPerturb :
      ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ ≤ τ := by
    calc
      ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖
          ≤ (2 * α * γ) * ‖y - xStar‖ := by
            exact gaussNewtonNormalMatrix_perturbationBound D r xStar α γ hxStar
              hJLipschitz hJBound hγ_nonneg hα_nonneg hyD
      _ ≤ (2 * α * γ) * ε1 := by
            gcongr
      _ ≤ (2 * α * γ) * εPert := by
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ ≤ τ := by
            have hcoeff_le : 2 * α * γ ≤ 2 * α * γ + 1 := by
              nlinarith
            have hmul :
                (2 * α * γ) * εPert ≤ (2 * α * γ + 1) * εPert := by
              exact mul_le_mul_of_nonneg_right hcoeff_le (le_of_lt hεPert_pos)
            have hscale :
                (2 * α * γ + 1) * εPert = τ := by
              dsimp [εPert]
              field_simp
            exact le_trans hmul (by simpa [hscale])
  have hLower :
      ∀ u : Point,
        (lam / c) * ‖u‖ ^ (2 : ℕ) ≤
          inner ℝ (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) u) u := by
    intro u
    have hRootLower :=
      gaussNewtonNormalMatrix_rootQuadraticLower r xStar lam hSmallest hlam_pos u
    have hPerturbInner :
        -‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ * ‖u‖ ^ (2 : ℕ) ≤
          inner ℝ
            (Matrix.toEuclideanLin
              (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u) u := by
      have hAbs :
          |inner ℝ
              (Matrix.toEuclideanLin
                (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u) u|
            ≤ ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ *
                ‖u‖ ^ (2 : ℕ) := by
        calc
          |inner ℝ
              (Matrix.toEuclideanLin
                (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u) u|
              ≤ ‖Matrix.toEuclideanLin
                    (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u‖ * ‖u‖ := by
                  exact abs_real_inner_le_norm _ _
          _ ≤ (‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ * ‖u‖) * ‖u‖ := by
                gcongr
                exact norm_toEuclideanLin_apply_le _ _
          _ = ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ *
                ‖u‖ ^ (2 : ℕ) := by
                ring
      simpa [neg_mul] using neg_le_of_abs_le hAbs
    have hInnerSplit :
        inner ℝ (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) u) u =
          inner ℝ (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r xStar) u) u +
            inner ℝ
              (Matrix.toEuclideanLin
                (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u) u := by
      have hSplitAction :
          Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) u =
            Matrix.toEuclideanLin (gaussNewtonNormalMatrix r xStar) u +
              Matrix.toEuclideanLin
                (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u := by
        calc
          Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) u
              = Matrix.toEuclideanLin
                  (gaussNewtonNormalMatrix r xStar +
                    (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar)) u := by
                      congr 1
                      ext i j
                      simp [sub_eq_add_neg]
          _ = Matrix.toEuclideanLin (gaussNewtonNormalMatrix r xStar) u +
                Matrix.toEuclideanLin
                  (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u := by
                    rw [toEuclideanLin_add_apply]
      rw [hSplitAction, inner_add_left]
    have hCoeff :
        lam / c ≤ lam - ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖ := by
      have hτ_eq : τ = lam - lam / c := by
        dsimp [τ]
        field_simp [hc_pos.ne']
      rw [hτ_eq] at hPerturb
      nlinarith
    have hCoeffMul :
        (lam / c) * ‖u‖ ^ (2 : ℕ) ≤
          (lam - ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖) *
            ‖u‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hCoeff (by positivity)
    calc
      (lam / c) * ‖u‖ ^ (2 : ℕ)
          ≤ (lam - ‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖) *
              ‖u‖ ^ (2 : ℕ) := hCoeffMul
      _ = lam * ‖u‖ ^ (2 : ℕ) +
            (-‖gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar‖) *
              ‖u‖ ^ (2 : ℕ) := by
            ring
      _ ≤ inner ℝ (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r xStar) u) u +
            inner ℝ
              (Matrix.toEuclideanLin
                (gaussNewtonNormalMatrix r y - gaussNewtonNormalMatrix r xStar) u) u := by
            linarith
      _ = inner ℝ (Matrix.toEuclideanLin (gaussNewtonNormalMatrix r y) u) u := by
            rw [hInnerSplit]
  have hUnitAndBound :=
    isUnit_and_inv_norm_le_of_quadratic_lower
      (A := gaussNewtonNormalMatrix r y) (μ := lam / c)
      (by positivity) hLower
  have hInvRewrite : 1 / (lam / c) = c / lam := by
    field_simp [hc_pos.ne', hlam_pos.ne']
  refine ⟨hyD, hUnitAndBound.1, ?_⟩
  simpa [hInvRewrite] using hUnitAndBound.2

/-- Helper for Chapter07 Theorem 7.2.3: the explicit inverse Gauss-Newton step solves the
canonical normal equation whenever the current normal matrix is invertible. -/
private theorem gaussNewtonExplicitStep_solvesNormalEquation
    (r : Point → Residual) (y : Point)
    (hAy : IsUnit (gaussNewtonNormalMatrix r y)) :
    solvesGaussNewtonNormalEquation r y
      (y - Matrix.toEuclideanLin ((gaussNewtonNormalMatrix r y)⁻¹) (g[r](y))) := by
  let A : Matrix (Fin n) (Fin n) ℝ := gaussNewtonNormalMatrix r y
  letI := hAy.invertible
  -- Route correction: keep this helper as a pure inverse-cancellation adapter for the main proof.
  rw [solvesGaussNewtonNormalEquation_iff]
  calc
    Matrix.toEuclideanLin A
        ((y - Matrix.toEuclideanLin (A⁻¹) (g[r](y))) - y)
        = Matrix.toEuclideanLin A (-Matrix.toEuclideanLin (A⁻¹) (g[r](y))) := by
            abel_nf
    _ = -Matrix.toEuclideanLin A (Matrix.toEuclideanLin (A⁻¹) (g[r](y))) := by
          rw [map_neg]
    _ = -Matrix.toEuclideanLin (A * A⁻¹) (g[r](y)) := by
          rw [toEuclideanLin_mul_apply]
    _ = -g[r](y) := by
          simpa [A, Matrix.mul_inv_of_invertible]

/-- Chapter07 Theorem 7.2.3: under the source assumptions on the open convex set `D`, the
residual map `r` is `C²` on `D`, the Jacobian `J(x)` satisfies `(7.2.16)` and `(7.2.17)`, the
stationarity condition is `g(xStar) = 0`, the smallest-eigenvalue hypothesis is imposed on
`gaussNewtonNormalMatrix r xStar`, and the gap hypotheses `0 ≤ σ`, `1 < c`, and
`c * σ < lam` hold. Then there exists a radius `ε > 0` such that every
`x0 ∈ Metric.ball xStar ε` admits a Gauss-Newton iterate family `x_k` staying in `D`, solving
the canonical normal equation at each step, converging linearly to `xStar` in the canonical
sense `HasLinearConvergenceTo x xStar`, satisfying the source estimates `(7.2.18)` and
`(7.2.19)`, and strictly decreasing the error norm whenever the current iterate is not already
the fixed point `xStar`. -/
theorem gaussNewtonLocalConvergence_of_smallestEigenvalueGap
    (D : Set Point) (r : Point → Residual) (xStar : Point) (lam σ α γ c : ℝ)
    (hOpen : IsOpen D)
    (hConvex : Convex ℝ D)
    (hxStar : xStar ∈ D)
    (hResidualC2 : ContDiffOn ℝ 2 r D)
    (hJLipschitz :
      ∀ x ∈ D, ∀ y ∈ D,
        ‖(Matrix.toEuclideanLin
            (J[r](x) - J[r](y))).toContinuousLinearMap‖ ≤
          γ * ‖x - y‖)
    (hJBound :
      ∀ x : Point, x ∈ D →
        ‖(Matrix.toEuclideanLin (J[r](x))).toContinuousLinearMap‖ ≤ α)
    (hσ_nonneg : 0 ≤ σ)
    (hStationary : g[r](xStar) = 0)
    (hSmallest :
      IsLeast (spectrum ℝ (gaussNewtonNormalMatrix r xStar)) lam)
    (hResidualLinearization :
      ∀ x : Point, x ∈ D →
        ‖Matrix.toEuclideanLin
            ((J[r](x) - J[r](xStar))ᵀ) (r xStar)‖ ≤
          σ * ‖x - xStar‖)
    (hc_lower : 1 < c)
    (hc_upper : c * σ < lam) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x0 : Point, x0 ∈ Metric.ball xStar ε →
        ∃ x : ℕ → Point,
          x 0 = x0 ∧
            (∀ k : ℕ, x k ∈ D) ∧
            (∀ k : ℕ, solvesGaussNewtonNormalEquation r (x k) (x (k + 1))) ∧
            HasLinearConvergenceTo x xStar ∧
            (∀ k : ℕ,
              ‖x (k + 1) - xStar‖ ≤
                (c * σ / lam) * ‖x k - xStar‖ +
                  (c * α * γ / (2 * lam)) * ‖x k - xStar‖ ^ (2 : ℕ)) ∧
            (∀ k : ℕ,
              ‖x (k + 1) - xStar‖ ≤
                ((c * σ + lam) / (2 * lam)) * ‖x k - xStar‖) ∧
            ∀ k : ℕ, x k ≠ xStar → ‖x (k + 1) - xStar‖ < ‖x k - xStar‖ := by
  classical
  by_cases hne : Nonempty (Fin n)
  · letI : Nonempty (Fin n) := hne
    have hc_pos : 0 < c := lt_trans zero_lt_one hc_lower
    have hlam_pos : 0 < lam := by
      nlinarith
    have hα_nonneg : 0 ≤ α := by
      have hBound := hJBound xStar hxStar
      nlinarith [norm_nonneg ((Matrix.toEuclideanLin (J[r](xStar))).toContinuousLinearMap)]
    have hγ_nonneg : 0 ≤ γ := by
      rcases Metric.mem_nhds_iff.mp (hOpen.mem_nhds hxStar) with ⟨ρ, hρ_pos, hρ_ball⟩
      obtain ⟨i⟩ := hne
      let e : Point := EuclideanSpace.basisFun (Fin n) ℝ i
      let y : Point := xStar + (ρ / 2) • e
      have he_norm : ‖e‖ = 1 := by
        dsimp [e]
        simpa using (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
      have hyNorm : ‖y - xStar‖ = ρ / 2 := by
        calc
          ‖y - xStar‖ = ‖(ρ / 2) • e‖ := by
            dsimp [y]
            congr 1
            abel_nf
          _ = |ρ / 2| * ‖e‖ := norm_smul _ _
          _ = ρ / 2 := by
            rw [he_norm, abs_of_pos (by positivity)]
            simp
      have hyBall : y ∈ Metric.ball xStar ρ := by
        simpa [Metric.mem_ball, dist_eq_norm, hyNorm] using half_lt_self hρ_pos
      have hyD : y ∈ D := hρ_ball hyBall
      have hyNormPos : 0 < ‖y - xStar‖ := by
        rw [hyNorm]
        positivity
      have hLip := hJLipschitz y hyD xStar hxStar
      have hprod_nonneg : 0 ≤ γ * ‖y - xStar‖ := by
        exact le_trans (norm_nonneg _) hLip
      nlinarith
    rcases normalMatrixInverseControlNearStar D r xStar lam α γ c hOpen hxStar
        hJLipschitz hJBound hSmallest hγ_nonneg hα_nonneg hlam_pos hc_lower with
      ⟨εInv, hεInv_pos, hInvControl⟩
    let εGap : ℝ := (lam - c * σ) / (c * α * γ + 1)
    let ε : ℝ := min εInv εGap
    have hεGap_pos : 0 < εGap := by
      dsimp [εGap]
      have hnum_pos : 0 < lam - c * σ := by
        nlinarith
      positivity
    have hε_pos : 0 < ε := by
      exact lt_min hεInv_pos hεGap_pos
    let q : ℝ := (c * σ + lam) / (2 * lam)
    have hq_pos : 0 < q := by
      dsimp [q]
      positivity
    have hq_lt_one : q < 1 := by
      have hnum_lt : c * σ + lam < 2 * lam := by
        nlinarith
      dsimp [q]
      have hnum_lt' : c * σ + lam < 1 * (2 * lam) := by
        simpa using hnum_lt
      exact (div_lt_iff₀ (by positivity : 0 < 2 * lam)).2 hnum_lt'
    refine ⟨ε, hε_pos, ?_⟩
    intro x0 hx0
    let x : ℕ → Point :=
      Nat.rec x0 fun _ xk ↦
        xk - Matrix.toEuclideanLin ((gaussNewtonNormalMatrix r xk)⁻¹) (g[r](xk))
    have hx_zero : x 0 = x0 := by
      rfl
    have hx_succ :
        ∀ k : ℕ,
          x (k + 1) =
            x k - Matrix.toEuclideanLin ((gaussNewtonNormalMatrix r (x k))⁻¹) (g[r](x k)) := by
      intro k
      simp [x]
    have hBall : ∀ k : ℕ, x k ∈ Metric.ball xStar ε := by
      intro k
      induction k with
      | zero =>
          simpa [x] using hx0
      | succ k hk =>
          have hkInvBall : x k ∈ Metric.ball xStar εInv := by
            exact Metric.ball_subset_ball (min_le_left _ _) hk
          have hkData := hInvControl (x k) hkInvBall
          have hkStep :=
            gaussNewtonInverseStep_estimates D r xStar lam σ α γ c ε
              hOpen hConvex hxStar hResidualC2 hJBound hStationary
              hResidualLinearization hJLipschitz hγ_nonneg hlam_pos hc_lower
              (min_le_right _ _) hkData.1 hk hkData.2.1 hkData.2.2
          have hkNextNorm :
              ‖x (k + 1) - xStar‖ ≤ q * ‖x k - xStar‖ := by
            simpa [x, q] using hkStep.2
          have hkNormLt : ‖x k - xStar‖ < ε := by
            simpa [Metric.mem_ball, dist_eq_norm] using hk
          have hkNextLt : q * ‖x k - xStar‖ < ε := by
            nlinarith [hkNormLt, norm_nonneg (x k - xStar), hq_pos, hq_lt_one]
          simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt hkNextNorm hkNextLt
    have hD : ∀ k : ℕ, x k ∈ D := by
      intro k
      exact (hInvControl (x k) (Metric.ball_subset_ball (min_le_left _ _) (hBall k))).1
    have hStep :
        ∀ k : ℕ, solvesGaussNewtonNormalEquation r (x k) (x (k + 1)) := by
      intro k
      have hkData := hInvControl (x k) (Metric.ball_subset_ball (min_le_left _ _) (hBall k))
      simpa [hx_succ k] using gaussNewtonExplicitStep_solvesNormalEquation r (x k) hkData.2.1
    have hBound1 :
        ∀ k : ℕ,
          ‖x (k + 1) - xStar‖ ≤
            (c * σ / lam) * ‖x k - xStar‖ +
              (c * α * γ / (2 * lam)) * ‖x k - xStar‖ ^ (2 : ℕ) := by
      intro k
      have hkData := hInvControl (x k) (Metric.ball_subset_ball (min_le_left _ _) (hBall k))
      simpa [hx_succ k] using
        (gaussNewtonInverseStep_estimates D r xStar lam σ α γ c ε
          hOpen hConvex hxStar hResidualC2 hJBound hStationary
          hResidualLinearization hJLipschitz hγ_nonneg hlam_pos hc_lower
          (min_le_right _ _) hkData.1 (hBall k) hkData.2.1 hkData.2.2).1
    have hBound2 :
        ∀ k : ℕ,
          ‖x (k + 1) - xStar‖ ≤
            q * ‖x k - xStar‖ := by
      intro k
      have hkData := hInvControl (x k) (Metric.ball_subset_ball (min_le_left _ _) (hBall k))
      simpa [hx_succ k, q] using
        (gaussNewtonInverseStep_estimates D r xStar lam σ α γ c ε
          hOpen hConvex hxStar hResidualC2 hJBound hStationary
          hResidualLinearization hJLipschitz hγ_nonneg hlam_pos hc_lower
          (min_le_right _ _) hkData.1 (hBall k) hkData.2.1 hkData.2.2).2
    have hTendsto : Tendsto x atTop (nhds xStar) := by
      exact tendsto_of_error_contraction (le_of_lt hq_pos) hq_lt_one hBound2
    have hLinear : HasLinearConvergenceTo x xStar := by
      refine ⟨hTendsto, ?_⟩
      exact ⟨q, ⟨hq_pos, hq_lt_one⟩, hBound2⟩
    have hStrict :
        ∀ k : ℕ, x k ≠ xStar → ‖x (k + 1) - xStar‖ < ‖x k - xStar‖ := by
      intro k hk_ne
      have hkNormPos : 0 < ‖x k - xStar‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hk_ne)
      have hqMulLt : q * ‖x k - xStar‖ < ‖x k - xStar‖ := by
        nlinarith
      exact lt_of_le_of_lt (hBound2 k) hqMulLt
    refine ⟨x, hx_zero, hD, hStep, hLinear, hBound1, ?_, hStrict⟩
    intro k
    simpa [q] using hBound2 k
  · letI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
    refine ⟨1, by norm_num, ?_⟩
    intro x0 _hx0
    have hx0_eq : x0 = xStar := Subsingleton.elim _ _
    refine ⟨fun _ : ℕ ↦ xStar, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hx0_eq]
    · intro k
      simpa using hxStar
    · intro k
      -- In the zero-dimensional branch the orbit is constant, so the normal equation is trivial.
      rw [solvesGaussNewtonNormalEquation_iff, hStationary]
      simp
    · refine ⟨tendsto_const_nhds, ?_⟩
      refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
      intro k
      simp
    · intro k
      simp
    · intro k
      simp
    · intro k hk_ne
      exact (hk_ne rfl).elim

end
