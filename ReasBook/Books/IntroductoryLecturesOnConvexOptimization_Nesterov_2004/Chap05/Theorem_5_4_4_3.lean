/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped RealSymmetricMatrixSpace
open scoped BigOperators Gradient HessianLocalNorm MatrixOrder

local notation "Mat" n => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" n => 𝕊^n

-- Proof sketch: for `X ∈ int(𝕊ⁿ₊)` and a symmetric direction `Δ`, conjugate by `X^(-1 / 2)` to
-- reduce the first three directional derivatives of `X ↦ -log det X` to sums of eigenvalue
-- powers of `Q = X^(-1 / 2) Δ X^(-1 / 2)`. Then the barrier-parameter bound with `ν = n`
-- follows from Cauchy--Schwarz, and the self-concordance inequality follows from the estimate
-- `|∑ λᵢ^3| ≤ (∑ λᵢ^2)^(3 / 2)`.
/-- Helper for Theorem 5.4.4.3: a `C²` scalar field on a real Hilbert space has a differentiable
gradient at the base point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- A `C²` scalar field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.4.4.3: the strict cone `𝕊ⁿ₊₊ = int(𝕊ⁿ₊)` is convex. -/
private theorem strictPositiveSemidefiniteCone_convex
    (n : ℕ) :
    Convex ℝ (𝕊^n₊₊ : Set (SymmMat n)) := by
  -- Rewrite the strict cone as the interior of the PSD cone and use convexity of interiors.
  simpa [strictPositiveSemidefiniteCone_eq_interior] using
    (Convex.interior (positiveSemidefiniteCone_convex n))

/-- Helper for Theorem 5.4.4.3: tracing the Hermitian functional calculus of a symmetric matrix
applies the scalar function to the ordered eigenvalues and sums the result. -/
private theorem trace_cfc_eq_sum_map_eigenvalues
    {n : ℕ} (Q : SymmMat n) (f : ℝ → ℝ) :
    Matrix.trace ((isHermitian Q).cfc f) = ∑ i : Fin n, f (eigenvalues Q i) := by
  let hQ : (Q : Mat n).IsHermitian := isHermitian Q
  -- Rewrite the functional calculus into diagonal form in the orthonormal eigenbasis.
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp]

/-- Helper for Theorem 5.4.4.3: the trace of a symmetric square is the sum of the squared
eigenvalues. -/
private theorem trace_square_eq_sum_eigenvalue_squares
    {n : ℕ} (Q : SymmMat n) :
    Matrix.trace (((Q : Mat n) ^ (2 : ℕ))) =
      ∑ i : Fin n, (eigenvalues Q i) ^ (2 : ℕ) := by
  -- View the square as the continuous functional calculus of `x ↦ x²`.
  calc
    Matrix.trace (((Q : Mat n) ^ (2 : ℕ)))
        = Matrix.trace (cfc (fun x : ℝ ↦ x ^ (2 : ℕ)) (Q : Mat n)) := by
            congr 1
            symm
            simpa using
              (cfc_pow_id (R := ℝ) (a := (Q : Mat n)) 2
                (ha := (isHermitian Q : IsSelfAdjoint (Q : Mat n))))
    _ = Matrix.trace ((isHermitian Q).cfc (fun x : ℝ ↦ x ^ (2 : ℕ))) := by
          rw [(isHermitian Q).cfc_eq]
    _ = ∑ i : Fin n, (eigenvalues Q i) ^ (2 : ℕ) :=
          trace_cfc_eq_sum_map_eigenvalues Q (fun x : ℝ ↦ x ^ (2 : ℕ))

/-- Helper for Theorem 5.4.4.3: the trace of a symmetric cube is the sum of the cubed
eigenvalues. -/
private theorem trace_cube_eq_sum_eigenvalue_cubes
    {n : ℕ} (Q : SymmMat n) :
    Matrix.trace (cube Q : Mat n) =
      ∑ i : Fin n, (eigenvalues Q i) ^ (3 : ℕ) := by
  -- The cube is again a polynomial functional calculus of the Hermitian matrix `Q`.
  calc
    Matrix.trace (cube Q : Mat n)
        = Matrix.trace (((Q : Mat n) ^ (3 : ℕ))) := by simp
    _ = Matrix.trace (cfc (fun x : ℝ ↦ x ^ (3 : ℕ)) (Q : Mat n)) := by
          congr 1
          symm
          simpa using
            (cfc_pow_id (R := ℝ) (a := (Q : Mat n)) 3
              (ha := (isHermitian Q : IsSelfAdjoint (Q : Mat n))))
    _ = Matrix.trace ((isHermitian Q).cfc (fun x : ℝ ↦ x ^ (3 : ℕ))) := by
          rw [(isHermitian Q).cfc_eq]
    _ = ∑ i : Fin n, (eigenvalues Q i) ^ (3 : ℕ) :=
          trace_cfc_eq_sum_map_eigenvalues Q (fun x : ℝ ↦ x ^ (3 : ℕ))

/-- Helper for Theorem 5.4.4.3: the scalar cubic trace estimate is bounded by the `ℓ₂` norm to the
third power. -/
private theorem sum_cubes_le_sqrt_sum_sq_pow_three
    {n : ℕ} (mu : Fin n → ℝ) :
    |∑ i : Fin n, mu i ^ (3 : ℕ)| ≤
      (Real.sqrt (∑ i : Fin n, mu i ^ (2 : ℕ))) ^ (3 : ℕ) := by
  let s : ℝ := ∑ i : Fin n, mu i ^ (2 : ℕ)
  have hs_nonneg : 0 ≤ s := by
    -- The controlling square sum is nonnegative termwise.
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (mu i)
  have hcoord_le : ∀ i : Fin n, |mu i| ≤ Real.sqrt s := by
    intro i
    -- Each coordinate square is bounded by the total square sum.
    apply Real.abs_le_sqrt
    have hsingle :
        mu i ^ (2 : ℕ) ≤ ∑ j : Fin n, mu j ^ (2 : ℕ) := by
      simpa using
        (Finset.single_le_sum
          (fun j _ ↦ sq_nonneg (mu j))
          (Finset.mem_univ i))
    simpa [s] using hsingle
  have hterm :
      ∀ i : Fin n, |mu i ^ (3 : ℕ)| ≤ Real.sqrt s * (mu i ^ (2 : ℕ)) := by
    intro i
    have hi := hcoord_le i
    have hsq_nonneg : 0 ≤ mu i ^ (2 : ℕ) := sq_nonneg (mu i)
    have hsqrt_nonneg : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    calc
      |mu i ^ (3 : ℕ)| = |mu i| * (mu i ^ (2 : ℕ)) := by
        rw [abs_pow, pow_succ', sq_abs]
      _ ≤ Real.sqrt s * (mu i ^ (2 : ℕ)) := by
        exact mul_le_mul hi le_rfl hsq_nonneg hsqrt_nonneg
  -- Bound the absolute cubic sum by summing the pointwise `sqrt(s) * μᵢ²` majorants.
  calc
    |∑ i : Fin n, mu i ^ (3 : ℕ)| ≤ ∑ i : Fin n, |mu i ^ (3 : ℕ)| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin n ↦ mu i ^ (3 : ℕ)))
    _ ≤ ∑ i : Fin n, Real.sqrt s * (mu i ^ (2 : ℕ)) := by
      exact Finset.sum_le_sum fun i _ ↦ hterm i
    _ = Real.sqrt s * ∑ i : Fin n, mu i ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
    _ = Real.sqrt s * s := by simp [s]
    _ = Real.sqrt s * (Real.sqrt s) ^ (2 : ℕ) := by
      congr 1
      simpa [pow_two] using (Real.sq_sqrt hs_nonneg).symm
    _ = (Real.sqrt s) ^ (3 : ℕ) := by
      ring
    _ = (Real.sqrt (∑ i : Fin n, mu i ^ (2 : ℕ))) ^ (3 : ℕ) := by
      simp [s]

/-- Helper for Theorem 5.4.4.3: summing the pointwise estimate `-2 t - t² ≤ 1` yields the
barrier-parameter scalar bound. -/
private theorem sum_neg_two_mul_sub_sq_le_card
    {n : ℕ} (mu : Fin n → ℝ) :
    -2 * ∑ i : Fin n, mu i - ∑ i : Fin n, mu i ^ (2 : ℕ) ≤ n := by
  have hpointwise : ∀ i : Fin n, -2 * mu i - mu i ^ (2 : ℕ) ≤ (1 : ℝ) := by
    intro i
    have hsq : 0 ≤ (mu i + 1) ^ (2 : ℕ) := sq_nonneg (mu i + 1)
    nlinarith
  have hsum :
      ∑ i : Fin n, (-2 * mu i - mu i ^ (2 : ℕ)) ≤ ∑ _i : Fin n, (1 : ℝ) := by
    exact Finset.sum_le_sum fun i _ ↦ hpointwise i
  have hrewrite :
      ∑ i : Fin n, (-2 * mu i - mu i ^ (2 : ℕ)) =
        -2 * ∑ i : Fin n, mu i - ∑ i : Fin n, mu i ^ (2 : ℕ) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  -- Collapse the constant sum to `n`.
  rw [← hrewrite]
  simpa using hsum

/-- Helper for Theorem 5.4.4.3: the determinant alternating map is continuous on row tuples. -/
private theorem detRowAlternating_continuous
    (n : ℕ) :
    Continuous (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ) := by
  -- Rewrite the alternating-map owner through the usual matrix determinant.
  simpa [Matrix.det] using
    (Continuous.matrix_det (A := fun M : Mat n ↦ M) continuous_id)

/-- Helper for Theorem 5.4.4.3: continuity gives the determinant alternating map a global norm
bound. -/
private theorem detRowAlternating_exists_bound
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m : Mat n, ‖Matrix.detRowAlternating m‖ ≤ C * ∏ i : Fin n, ‖m i‖ := by
  -- Apply the general boundedness theorem for continuous alternating maps.
  exact AlternatingMap.exists_bound_of_continuous
    (f := (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ))
    (detRowAlternating_continuous n)

/-- Helper for Theorem 5.4.4.3: the determinant as a continuous alternating map on matrix rows. -/
private def detContinuousAlternating
    (n : ℕ) :
    (Fin n → ℝ) [⋀^(Fin n)]→L[ℝ] ℝ :=
  let C : ℝ := Classical.choose (detRowAlternating_exists_bound n)
  AlternatingMap.mkContinuous
    (f := (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ))
    C
    ((Classical.choose_spec (detRowAlternating_exists_bound n)).2)

/-- Helper for Theorem 5.4.4.3: a matrix determines its entry function
`(i, j) ↦ A i j` as a linear map to the coordinate space. -/
private def matrixEntryLinearMap
    (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ((Fin n × Fin n) → ℝ) where
  toFun := fun A p ↦ A p.1 p.2
  map_add' := by
    intro A B
    ext p
    rfl
  map_smul' := by
    intro c A
    ext p
    rfl

/-- Helper for Theorem 5.4.4.3: evaluating the determinant polynomial of
`Matrix.mvPolynomialX` at the entries of `A` recovers `Matrix.det A`. -/
@[simp] private theorem eval_det_mvPolynomialX
    {n : ℕ} (A : Mat n) :
    MvPolynomial.eval (matrixEntryLinearMap n A)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ)) =
      Matrix.det A := by
  have h :=
    congrArg Matrix.det
      (Matrix.mvPolynomialX_mapMatrix_eval (A := A) (m := Fin n) (R := ℝ))
  calc
    MvPolynomial.eval (matrixEntryLinearMap n A)
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ))
      = Matrix.det
          ((MvPolynomial.eval (matrixEntryLinearMap n A)).mapMatrix
            (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ)) := by
              exact RingHom.map_det
                (MvPolynomial.eval (matrixEntryLinearMap n A))
                (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ)
    _ = Matrix.det A := h

/-- Helper for Theorem 5.4.4.3: determinant is `C³` on the full symmetric-matrix carrier. -/
private theorem symm_det_contDiff
    (n : ℕ) :
    ContDiff ℝ 3 (fun X : SymmMat n ↦ ((X : Mat n)).det) := by
  -- Factor the determinant through the continuous alternating-map owner on the ambient row space,
  -- then restrict it to the symmetric-matrix submodule.
  let p : MvPolynomial (Fin n × Fin n) ℝ :=
    Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ)
  have hdetEval :
      ContDiff ℝ 3 (fun A : Mat n ↦ MvPolynomial.eval (matrixEntryLinearMap n A) p) := by
    have hanalytic :
        AnalyticOnNhd ℝ
          (fun A : Mat n ↦ MvPolynomial.eval (matrixEntryLinearMap n A) p)
          Set.univ :=
      AnalyticOnNhd.eval_linearMap (f := matrixEntryLinearMap n) p
    exact hanalytic.contDiff
  have hdet : ContDiff ℝ 3 (fun A : Mat n ↦ Matrix.det A) := by
    simpa [p] using hdetEval
  have hsub :
      ContDiff ℝ 3 (fun Y : SymmMat n ↦ ((Submodule.subtypeₗᵢ (𝕊^n)) Y : Mat n)) := by
    simpa using (Submodule.subtypeₗᵢ (𝕊^n)).contDiff
  simpa using hdet.comp hsub

/-- Helper for Theorem 5.4.4.3: the ambient log-determinant barrier is `C³` on the strict cone. -/
private theorem logDetBarrierAmbient_contDiffOn_strict_cone
    (n : ℕ) :
    ContDiffOn ℝ 3 (logDetBarrierAmbient n) (𝕊^n₊₊ : Set (SymmMat n)) := by
  intro X hX
  have hdet : ContDiffAt ℝ 3 (fun Y : SymmMat n ↦ ((Y : Mat n)).det) X :=
    (symm_det_contDiff n).contDiffAt
  have hdet_ne : ((X : Mat n)).det ≠ 0 :=
    (strictPositiveSemidefiniteCone_posDef ⟨X, hX⟩).det_pos.ne'
  -- Strict-cone determinant positivity keeps the `log` composition away from its singularity.
  simpa [logDetBarrierAmbient] using ((hdet.log hdet_ne).neg.contDiffWithinAt)

/-- Helper for Theorem 5.4.4.3: the intrinsic square of `X^{-1/2}` is `X^{-1}`. -/
private theorem sandwich_sqrtInv_one_eq_inv
    {n : ℕ} (X : 𝕊^n₊₊) :
    RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) (1 : SymmMat n) =
      StrictPositiveSemidefiniteCone.inv X := by
  have hinv_nonneg :
      0 ≤ ((((X : SymmMat n) : Mat n)⁻¹) : Mat n) := by
    exact (Matrix.PosDef.inv (strictPositiveSemidefiniteCone_posDef X)).posSemidef.nonneg
  apply Subtype.ext
  -- Rewrite both symmetric-carrier terms into ambient matrices and use `√A * √A = A`.
  simp [RealSymmetricMatrixSpace.sandwich]
  simpa [pow_two] using
    (CFC.sqrt_mul_sqrt_self ((((X : SymmMat n) : Mat n)⁻¹)) (ha := hinv_nonneg))

/-- Helper for Theorem 5.4.4.3: after normalizing by `X^{-1/2}`, the first three directional
derivatives of `-log det` become sums of powers of the eigenvalues of the sandwich matrix. -/
private theorem normalized_logdet_directional_formulas
    {n : ℕ} (X : 𝕊^n₊₊) (Δ : SymmMat n) :
    let Q : SymmMat n :=
      RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) Δ
    lineDeriv ℝ (logDetBarrierAmbient n) X Δ =
        -∑ i : Fin n, RealSymmetricMatrixSpace.eigenvalues Q i ∧
      secondDirectionalDerivative (logDetBarrierAmbient n) X Δ =
        ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) ∧
      thirdDirectionalDerivative (logDetBarrierAmbient n) X Δ =
        -2 * ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (3 : ℕ) := by
  let Q : SymmMat n :=
    RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) Δ
  have hQtrace :
      Matrix.trace (Q : Mat n) =
        ∑ i : Fin n, RealSymmetricMatrixSpace.eigenvalues Q i := by
    simpa using (isHermitian Q).trace_eq_sum_eigenvalues
  have hline_trace :
      lineDeriv ℝ (logDetBarrierAmbient n) X Δ = -Matrix.trace (Q : Mat n) := by
    -- Route correction: use the existing Frobenius-owner formula and only bridge
    -- `sqrtInv^2 = inv` through the intrinsic sandwich square.
    calc
      lineDeriv ℝ (logDetBarrierAmbient n) X Δ =
          ⟪-StrictPositiveSemidefiniteCone.inv X, Δ⟫_F := by
            simpa using logDetBarrier_lineDeriv_eq_frobeniusInner n X Δ
      _ = -⟪Δ, RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X)
            (1 : SymmMat n)⟫_F := by
            change inner ℝ (-StrictPositiveSemidefiniteCone.inv X) Δ =
              -inner ℝ Δ
                (RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X)
                  (1 : SymmMat n))
            rw [sandwich_sqrtInv_one_eq_inv X, real_inner_comm]
            simp
      _ = -Matrix.trace (Q : Mat n) := by
            congr 1
            simpa [Q] using
              (frobenius_trace_identity_for_real_symmetric_matrices
                Δ (StrictPositiveSemidefiniteCone.sqrtInv X)).1
  have hsecond_trace :
      secondDirectionalDerivative (logDetBarrierAmbient n) X Δ =
        Matrix.trace (((Q : Mat n) ^ (2 : ℕ))) := by
    -- The second directional derivative is already owned by the Chapter 5 trace-square lemma.
    simpa [Q] using logDetBarrier_secondDirectional_eq_trace_sq n X Δ
  have hthird_trace :
      thirdDirectionalDerivative (logDetBarrierAmbient n) X Δ =
        -2 * Matrix.trace (RealSymmetricMatrixSpace.cube Q : Mat n) := by
    -- The third directional derivative is already owned by the Chapter 5 trace-cube lemma.
    simpa [Q] using logDetBarrier_thirdDirectional_eq_trace_cube n X Δ
  dsimp [Q]
  constructor
  · calc
      lineDeriv ℝ (logDetBarrierAmbient n) X Δ
          = -Matrix.trace (Q : Mat n) := hline_trace
      _ = -∑ i : Fin n, RealSymmetricMatrixSpace.eigenvalues Q i := by
            rw [hQtrace]
  constructor
  · calc
      secondDirectionalDerivative (logDetBarrierAmbient n) X Δ
          = Matrix.trace (((Q : Mat n) ^ (2 : ℕ))) := hsecond_trace
      _ = ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) :=
            trace_square_eq_sum_eigenvalue_squares Q
  · calc
      thirdDirectionalDerivative (logDetBarrierAmbient n) X Δ
          = -2 * Matrix.trace (RealSymmetricMatrixSpace.cube Q : Mat n) := hthird_trace
      _ = -2 * ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (3 : ℕ) := by
            rw [trace_cube_eq_sum_eigenvalue_cubes Q]

/-- Helper for Theorem 5.4.4.3: the Hessian quadratic form is the sum of squared eigenvalues of
the normalized sandwich matrix. -/
private theorem normalized_logdet_hessian_quadratic_form
    {n : ℕ} (X : 𝕊^n₊₊) (Δ : SymmMat n) :
    let Q : SymmMat n :=
      RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) Δ
    inner ℝ Δ (hessian (logDetBarrierAmbient n) X Δ) =
      ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
  let Q : SymmMat n :=
    RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) Δ
  have hdetAt : ContDiffAt ℝ 3 (fun Y : SymmMat n ↦ ((Y : Mat n)).det) (X : SymmMat n) :=
    (symm_det_contDiff n).contDiffAt
  have hdet_ne : ((X : SymmMat n) : Mat n).det ≠ 0 :=
    (strictPositiveSemidefiniteCone_posDef X).det_pos.ne'
  have hcontAt : ContDiffAt ℝ 3 (logDetBarrierAmbient n) (X : SymmMat n) := by
    simpa [logDetBarrierAmbient] using ((hdetAt.log hdet_ne).neg)
  have hdiff := hcontAt.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad :=
    differentiableAt_gradient_of_contDiffAt_two
      (hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hdir := normalized_logdet_directional_formulas X Δ
  -- Rewrite the Chapter 5 second directional derivative to the Hessian quadratic form and then
  -- substitute the normalized spectral formula.
  calc
    inner ℝ Δ (hessian (logDetBarrierAmbient n) X Δ)
        = secondDirectionalDerivative (logDetBarrierAmbient n) X Δ := by
            symm
            exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad
    _ = ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
          simpa [Q] using hdir.2.1

/-- Helper for Theorem 5.4.4.3: the barrier-parameter expression is the normalized scalar sum
`-2 ∑ μᵢ - ∑ μᵢ²` from the source proof. -/
private theorem normalized_logdet_barrier_parameter_expression
    {n : ℕ} (X : 𝕊^n₊₊) (Δ : SymmMat n) :
    let Q : SymmMat n :=
      RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) Δ
    2 * inner ℝ (∇ (logDetBarrierAmbient n) X) Δ -
        inner ℝ Δ (hessian (logDetBarrierAmbient n) X Δ) =
      -2 * ∑ i : Fin n, RealSymmetricMatrixSpace.eigenvalues Q i -
        ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
  let Q : SymmMat n :=
    RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv X) Δ
  have hdetAt : ContDiffAt ℝ 3 (fun Y : SymmMat n ↦ ((Y : Mat n)).det) (X : SymmMat n) :=
    (symm_det_contDiff n).contDiffAt
  have hdet_ne : ((X : SymmMat n) : Mat n).det ≠ 0 :=
    (strictPositiveSemidefiniteCone_posDef X).det_pos.ne'
  have hcontAt : ContDiffAt ℝ 3 (logDetBarrierAmbient n) (X : SymmMat n) := by
    simpa [logDetBarrierAmbient] using ((hdetAt.log hdet_ne).neg)
  have hdiff := hcontAt.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hline := hdiff.lineDeriv_eq_fderiv (v := Δ)
  have hgradpair := inner_gradient_left (y := Δ) hdiff
  have hpair := hline.trans hgradpair.symm
  have hdir := normalized_logdet_directional_formulas X Δ
  have hquad := normalized_logdet_hessian_quadratic_form X Δ
  -- Substitute the normalized first- and second-derivative formulas and simplify the scalar side.
  calc
    2 * inner ℝ (∇ (logDetBarrierAmbient n) X) Δ -
        inner ℝ Δ (hessian (logDetBarrierAmbient n) X Δ)
        = 2 * lineDeriv ℝ (logDetBarrierAmbient n) X Δ -
            ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
              rw [← hpair, hquad]
    _ = -2 * ∑ i : Fin n, RealSymmetricMatrixSpace.eigenvalues Q i -
          ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
            rw [hdir.1]
            ring

/-- Helper for Theorem 5.4.4.3: freeze the source strict cone as a set before switching to the
ambient Frobenius topology. -/
private def strictPositiveSemidefiniteConeSet (n : ℕ) : Set (SymmMat n) :=
  (𝕊^n₊₊ : Set (SymmMat n))

/-- Helper for Theorem 5.4.4.3: a positive-definite symmetric matrix dominates a positive scalar
multiple of the identity. -/
private theorem posDefExistsScalarLowerBound
    {n : ℕ} {X : SymmMat n} (hX : (X : Mat n).PosDef) :
    ∃ r : ℝ, 0 < r ∧ r • (1 : Mat n) ≤ (X : Mat n) := by
  by_cases hnontriv : Nontrivial (Mat n)
  · letI : Nontrivial (Mat n) := hnontriv
    -- Move strict positivity of the spectrum to a matrix-order lower bound by a scalar identity.
    have hstrict : IsStrictlyPositive (X : Mat n) := hX.isStrictlyPositive
    have hself : IsSelfAdjoint (X : Mat n) := by
      simpa [Matrix.IsHermitian] using RealSymmetricMatrixSpace.isHermitian X
    obtain ⟨r, hr, hrX⟩ :=
      (CFC.exists_pos_algebraMap_le_iff (a := (X : Mat n)) hself).2
        (fun x hx ↦ hstrict.spectrum_pos hx)
    exact ⟨r, hr, by simpa [Algebra.algebraMap_eq_smul_one] using hrX⟩
  · haveI : Subsingleton (Mat n) := not_nontrivial_iff_subsingleton.mp hnontriv
    have hone : (1 : Mat n) = 0 := Subsingleton.elim _ _
    have hzero : (X : Mat n) = 0 := Subsingleton.elim _ _
    refine ⟨1, zero_lt_one, ?_⟩
    simp [hone, hzero]

/-- Helper for Theorem 5.4.4.3: the trace of `A Aᵀ` is the sum of the squared entries of `A`. -/
private theorem trace_mul_transpose_eq_sum_squares
    {n : ℕ} (A : Mat n) :
    Matrix.trace (A * Aᵀ) = ∑ i : Fin n, ∑ j : Fin n, A i j ^ (2 : ℕ) := by
  -- Rewrite the trace through vectorization, then swap the two finite sums.
  rw [Matrix.trace_mul_comm, ← Matrix.vec_dotProduct_vec A A]
  simp [Matrix.vec, dotProduct, pow_two, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- Helper for Theorem 5.4.4.3: the chapter's ambient square-matrix norm is the Frobenius norm. -/
private theorem ambientMatrixNorm_eq_frobeniusNorm
    {n : ℕ} (A : Mat n) :
    @norm (Mat n) (Matrix.toMatrixNormedAddCommGroup (1 : Mat n) PosDef.one).toNorm A =
      @norm (Mat n) Matrix.frobeniusNormedAddCommGroup.toNorm A := by
  calc
    @norm (Mat n) (Matrix.toMatrixNormedAddCommGroup (1 : Mat n) PosDef.one).toNorm A
        = Real.sqrt (Matrix.trace (A * Aᵀ)) := by
            -- Expand the identity-induced ambient norm into its trace formula.
            rw [show @norm (Mat n) (Matrix.toMatrixNormedAddCommGroup (1 : Mat n) PosDef.one).toNorm A =
                Real.sqrt (inner ℝ A A) by
                  exact norm_eq_sqrt_real_inner A]
            change Real.sqrt (Matrix.trace (A * (1 : Mat n) * Aᵀ)) =
              Real.sqrt (Matrix.trace (A * Aᵀ))
            simp
    _ = Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ (2 : ℕ)) := by
          -- Replace the trace of `A Aᵀ` by the sum of squared entries.
          rw [trace_mul_transpose_eq_sum_squares]
    _ = @norm (Mat n) Matrix.frobeniusNormedAddCommGroup.toNorm A := by
          -- The Frobenius owner has exactly the same sum-of-squares norm formula.
          symm
          simpa [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def A)

/-- Helper for Theorem 5.4.4.3: matrix action on Euclidean space is bounded by the Frobenius
matrix norm times the Euclidean vector norm. -/
private theorem matrixToEuclideanLin_le_frobeniusNorm
    {n : ℕ} (A : Mat n) (u : EuclideanSpace ℝ (Fin n)) :
    ‖A.toEuclideanLin u‖ ≤ ‖A‖ * ‖u‖ := by
  letI : NormedAddCommGroup (Mat n) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin 1) ℝ) := Matrix.frobeniusNormedAddCommGroup
  have hcol : ‖Matrix.replicateCol (Fin 1) u.ofLp‖ = ‖u‖ := by
    -- Collapse the one-column Frobenius norm back to the Euclidean norm of the vector.
    calc
      ‖Matrix.replicateCol (Fin 1) u.ofLp‖ = ‖WithLp.toLp 2 u.ofLp‖ :=
        Matrix.frobenius_norm_replicateCol (ι := Fin 1) (v := u.ofLp)
      _ = ‖u‖ := by
        simp
  -- Normalize the Euclidean action to a one-column matrix product.
  calc
    ‖A.toEuclideanLin u‖ = ‖Matrix.replicateCol (Fin 1) (A *ᵥ u.ofLp)‖ := by
      change ‖WithLp.toLp 2 (A *ᵥ u.ofLp)‖ =
        ‖Matrix.replicateCol (Fin 1) (A *ᵥ u.ofLp)‖
      symm
      exact Matrix.frobenius_norm_replicateCol (ι := Fin 1) (v := A *ᵥ u.ofLp)
    _ = ‖A * Matrix.replicateCol (Fin 1) u.ofLp‖ := by
      rw [Matrix.replicateCol_mulVec (ι := Fin 1)]
    -- Apply Frobenius submultiplicativity, then collapse the one-column norm back to `‖u‖`.
    _ ≤ @norm (Mat n) Matrix.frobeniusNormedAddCommGroup.toNorm A *
          ‖Matrix.replicateCol (Fin 1) u.ofLp‖ := by
            exact Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) u.ofLp)
    _ = @norm (Mat n) (Matrix.toMatrixNormedAddCommGroup (1 : Mat n) PosDef.one).toNorm A *
          ‖Matrix.replicateCol (Fin 1) u.ofLp‖ := by
            rw [← ambientMatrixNorm_eq_frobeniusNorm A]
    _ = @norm (Mat n) (Matrix.toMatrixNormedAddCommGroup (1 : Mat n) PosDef.one).toNorm A * ‖u‖ := by
          rw [hcol]

/-- Helper for Theorem 5.4.4.3: the strict cone `𝕊ⁿ₊₊` is open for the Frobenius metric on the
symmetric-matrix carrier. -/
private theorem strictPositiveSemidefiniteCone_isOpen
    (n : ℕ) :
    @IsOpen (SymmMat n)
      (((Subtype.pseudoMetricSpace : PseudoMetricSpace (SymmMat n)).toUniformSpace).toTopologicalSpace)
      (strictPositiveSemidefiniteConeSet n) := by
  letI : PseudoMetricSpace (SymmMat n) := Subtype.pseudoMetricSpace
  letI : TopologicalSpace (SymmMat n) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  refine (Metric.isOpen_iff (α := SymmMat n) (s := strictPositiveSemidefiniteConeSet n)).2 ?_
  intro X hX
  obtain ⟨r, hr, hrX⟩ :=
    posDefExistsScalarLowerBound (X := X)
      (strictPositiveSemidefiniteCone_posDef ⟨X, by simpa [strictPositiveSemidefiniteConeSet] using hX⟩)
  refine ⟨r, hr, ?_⟩
  intro Y hY
  let Δ : Mat n := (Y : Mat n) - (X : Mat n)
  let S : SymmMat n := X - r • (1 : SymmMat n)
  have hYXdist : dist Y X < r := by
    simpa [Metric.mem_ball] using hY
  have hYXnorm : ‖Y - X‖ < r := by
    simpa [dist_eq_norm] using hYXdist
  have hΔnorm : ‖Δ‖ < r := by
    simpa [Δ] using hYXnorm
  have hS_psd : ((S : SymmMat n) : Mat n).PosSemidef := by
    have hslack_nonneg : 0 ≤ (X : Mat n) - r • (1 : Mat n) := sub_nonneg.mpr hrX
    simpa [S] using (Matrix.nonneg_iff_posSemidef).mp hslack_nonneg
  have hS_mem : S ∈ (𝕊^n₊ : Set (SymmMat n)) := by
    rw [mem_positiveSemidefiniteCone_iff]
    simpa using hS_psd
  -- Show that every point in the radius-`r` ball remains positive definite.
  have hY_posDef : ((Y : SymmMat n) : Mat n).PosDef := by
    rw [matrix_posDef_iff_forall_inner_pos]
    intro u hu
    have hΔmulVec : ‖Δ.toEuclideanLin u‖ ≤ ‖Δ‖ * ‖u‖ := by
      -- Route correction: keep the estimate in the Frobenius norm world via a one-column rewrite.
      exact matrixToEuclideanLin_le_frobeniusNorm Δ u
    have hΔquad_abs : |inner ℝ (Δ.toEuclideanLin u) u| ≤ ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by
      calc
        |inner ℝ (Δ.toEuclideanLin u) u| ≤ ‖Δ.toEuclideanLin u‖ * ‖u‖ := by
          exact abs_real_inner_le_norm _ _
        _ ≤ (‖Δ‖ * ‖u‖) * ‖u‖ := by
          gcongr
        _ = ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by
          ring
    have hΔquad : -(‖Δ‖ * ‖u‖ ^ (2 : ℕ)) ≤ inner ℝ (Δ.toEuclideanLin u) u :=
      neg_le_of_abs_le hΔquad_abs
    have hSquad : 0 ≤ inner ℝ (((S : SymmMat n) : Mat n).toEuclideanLin u) u := by
      exact (mem_positiveSemidefiniteCone_iff_inner_nonneg (X := S)).1 hS_mem u
    have hu_sq : 0 < ‖u‖ ^ (2 : ℕ) := by
      have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
      nlinarith
    have hrΔ : 0 < r - ‖Δ‖ := by
      linarith
    have hsplit :
        ((Y : SymmMat n) : Mat n).toEuclideanLin u =
          r • u + (((S : SymmMat n) : Mat n).toEuclideanLin u + Δ.toEuclideanLin u) := by
      simp [Δ, S, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      0 < (r - ‖Δ‖) * ‖u‖ ^ (2 : ℕ) := by positivity
      _ = r * ‖u‖ ^ (2 : ℕ) - ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by ring
      _ ≤ r * ‖u‖ ^ (2 : ℕ) +
            (inner ℝ (((S : SymmMat n) : Mat n).toEuclideanLin u) u +
              inner ℝ (Δ.toEuclideanLin u) u) := by
              nlinarith
      _ = inner ℝ (r • u + (((S : SymmMat n) : Mat n).toEuclideanLin u + Δ.toEuclideanLin u)) u := by
            simp [inner_add_left, real_inner_smul_left]
      _ = inner ℝ (((Y : SymmMat n) : Mat n).toEuclideanLin u) u := by
            rw [hsplit]
  simpa [strictPositiveSemidefiniteConeSet] using mem_strictPositiveSemidefiniteCone_of_posDef hY_posDef

/-- Theorem 5.4.4.3: the log-determinant function `X ↦ -log det X` is an `n`-self-concordant
barrier on the interior of the positive-semidefinite cone `𝕊ⁿ₊`. -/
theorem negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone
    (n : ℕ) :
    IsSelfConcordantBarrierOnWith
      (𝕊^n₊₊ : Set (SymmMat n))
      n
      (logDetBarrierAmbient n) := by
  let dom : Set (SymmMat n) := strictPositiveSemidefiniteConeSet n
  have hdom_convex : Convex ℝ dom := by
    -- Work directly on the strict-cone set to avoid any topology-instance transport.
    simpa [dom, strictPositiveSemidefiniteConeSet] using strictPositiveSemidefiniteCone_convex n
  have hdom_open :
      @IsOpen (SymmMat n)
        (((Subtype.pseudoMetricSpace : PseudoMetricSpace (SymmMat n)).toUniformSpace).toTopologicalSpace)
        dom := by
    simpa [dom] using strictPositiveSemidefiniteCone_isOpen n
  refine
    { toIsStandardSelfConcordantOn := ?_
      barrier_parameter_bound := ?_ }
  · refine
      { isOpen_domain := ?_
        contDiffOn := ?_
        convexOn := ?_
        third_deriv_bound := ?_ }
    · change
        @IsOpen (SymmMat n)
          (((Subtype.pseudoMetricSpace : PseudoMetricSpace (SymmMat n)).toUniformSpace).toTopologicalSpace)
          dom
      exact hdom_open
    · change ContDiffOn ℝ 3 (logDetBarrierAmbient n) dom
      simpa [dom, strictPositiveSemidefiniteConeSet] using logDetBarrierAmbient_contDiffOn_strict_cone n
    · have hF_C2 : ContDiffOn ℝ 2 (logDetBarrierAmbient n) dom := by
        -- Lower the regularity level from `C³` to `C²` on the same strict-cone domain.
        simpa [dom, strictPositiveSemidefiniteConeSet] using
          (logDetBarrierAmbient_contDiffOn_strict_cone n).of_le (by norm_num)
      -- Convexity reduces to nonnegativity of the normalized Hessian quadratic form.
      change ConvexOn ℝ dom (logDetBarrierAmbient n)
      refine (convexOn_iff_hessian_quadratic_form_nonneg hdom_open hdom_convex hF_C2).2 ?_
      intro X hX Δ
      let Xpos : 𝕊^n₊₊ := ⟨X, by simpa [dom, strictPositiveSemidefiniteConeSet] using hX⟩
      have hquad :
          inner ℝ Δ (hessian (logDetBarrierAmbient n) X Δ) =
            ∑ i : Fin n,
              (RealSymmetricMatrixSpace.eigenvalues
                (RealSymmetricMatrixSpace.sandwich
                  (StrictPositiveSemidefiniteCone.sqrtInv Xpos) Δ) i) ^ (2 : ℕ) := by
        simpa [Xpos] using normalized_logdet_hessian_quadratic_form Xpos Δ
      -- Route correction: prove convexity from the normalized Hessian square-sum, not by
      -- unfolding the determinant barrier directly.
      rw [real_inner_comm, hquad]
      exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    · intro X hX Δ
      let Xpos : 𝕊^n₊₊ := ⟨X, by simpa [dom, strictPositiveSemidefiniteConeSet] using hX⟩
      let Q : SymmMat n :=
        RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv Xpos) Δ
      have hdir := normalized_logdet_directional_formulas Xpos Δ
      have hquad := normalized_logdet_hessian_quadratic_form Xpos Δ
      dsimp [Q] at hdir hquad
      have hsum_nonneg :
          0 ≤ ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
        exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
      have hnorm :
          ‖Δ‖[logDetBarrierAmbient n; X] =
            Real.sqrt (∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ)) := by
        -- Expand the local norm and substitute the normalized Hessian square-sum.
        rw [hessianLocalNorm_def]
        simpa [Xpos] using congrArg Real.sqrt hquad
      -- The cubic derivative becomes `-2 * ∑ μᵢ³`; the source scalar estimate closes it.
      calc
        |thirdDirectionalDerivative (logDetBarrierAmbient n) X Δ|
            = |(-2 : ℝ) *
                ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (3 : ℕ)| := by
                  simpa [Xpos] using congrArg abs hdir.2.2
        _ = 2 * |∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (3 : ℕ)| := by
              rw [abs_mul]
              norm_num
        _ ≤ 2 * (Real.sqrt
              (∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ))) ^ (3 : ℕ) := by
                exact mul_le_mul_of_nonneg_left
                  (sum_cubes_le_sqrt_sum_sq_pow_three
                    (mu := fun i : Fin n ↦ RealSymmetricMatrixSpace.eigenvalues Q i))
                  (by norm_num)
        _ = 2 * ‖Δ‖[logDetBarrierAmbient n; X] ^ (3 : ℕ) := by
              rw [hnorm]
        _ = 2 * (1 : ℝ) * ‖Δ‖[logDetBarrierAmbient n; X] ^ (3 : ℕ) := by
              ring
  · intro X hX Δ
    let Xpos : 𝕊^n₊₊ := ⟨X, hX⟩
    let Q : SymmMat n :=
      RealSymmetricMatrixSpace.sandwich (StrictPositiveSemidefiniteCone.sqrtInv Xpos) Δ
    have hbarrier := normalized_logdet_barrier_parameter_expression Xpos Δ
    dsimp [Q] at hbarrier
    -- Reduce the barrier-parameter field to the scalar estimate `-2 ∑ μᵢ - ∑ μᵢ² ≤ n`.
    calc
      2 * inner ℝ (∇ (logDetBarrierAmbient n) X) Δ -
          inner ℝ Δ (hessian (logDetBarrierAmbient n) X Δ)
          = -2 * ∑ i : Fin n, RealSymmetricMatrixSpace.eigenvalues Q i -
              ∑ i : Fin n, (RealSymmetricMatrixSpace.eigenvalues Q i) ^ (2 : ℕ) := by
                simpa [Xpos] using hbarrier
      _ ≤ n := by
            simpa using
              (sum_neg_two_mul_sub_sq_le_card
                (mu := fun i : Fin n ↦ RealSymmetricMatrixSpace.eigenvalues Q i))

end
