/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import Mathlib
public import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_5.MatrixFamily
public import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_5.ConditionNumber
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Order.Monotone.Basic

open Matrix

noncomputable section

public section

variable {m n : ℕ}

/-- Helper for Chapter07 Theorem 7.3.5: the source damping matrix
`diag (diag (Jᵀ * J))` is positive semidefinite. -/
lemma sourceDampingMatrix_posSemidef
    (J : JacobianMatrix m n) :
    (levenbergMarquardtSourceDampingMatrix J).PosSemidef := by
  -- The Gram matrix `Jᵀ * J` is positive semidefinite, so its diagonal entries are nonnegative.
  have hDiag :
      0 ≤ fun i : Fin n ↦ (Jᵀ * J) i i := by
    intro i
    exact (Matrix.posSemidef_conjTranspose_mul_self J).diag_nonneg
  -- A diagonal matrix with nonnegative diagonal is positive semidefinite.
  simpa [levenbergMarquardtSourceDampingMatrix] using Matrix.PosSemidef.diagonal hDiag

/-- Helper for Chapter07 Theorem 7.3.5: the diagonal entries of the regularized source family are
exactly `(1 + μ)` times the diagonal entries of the damping matrix. -/
lemma sourceRegularizedDiagonalEntry_eq
    (J : JacobianMatrix m n) (μ : ℝ) (i : Fin n) :
    (sourceLevenbergMarquardtRegularizedNormalMatrix J μ) i i =
      (1 + μ) * (levenbergMarquardtSourceDampingMatrix J) i i := by
  -- On the diagonal, both `Jᵀ * J` and the source damping matrix contribute the same entry.
  simp [sourceLevenbergMarquardtRegularizedNormalMatrix_eq, levenbergMarquardtSourceDampingMatrix]
  ring

/-- Helper for Chapter07 Theorem 7.3.5: the source family
`J(x)ᵀ * J(x) + μ • diag (diag (J(x)ᵀ * J(x)))` is Hermitian for every damping parameter
`μ`. -/
theorem sourceLevenbergMarquardtRegularizedNormalMatrix_isHermitian
    (J : JacobianMatrix m n) (μ : ℝ) :
    (sourceLevenbergMarquardtRegularizedNormalMatrix J μ).IsHermitian := by
  -- Unfold the source family once, then combine Hermitian closure for the Gram and diagonal terms.
  rw [sourceLevenbergMarquardtRegularizedNormalMatrix_eq]
  exact
    (Matrix.isHermitian_conjTranspose_mul_self J).add
      ((Matrix.isHermitian_diagonal _).smul (IsSelfAdjoint.all μ))

/-- Helper for Chapter07 Theorem 7.3.5: in the orthonormal eigenbasis of a Hermitian matrix, the
transported Euclidean action is diagonal. -/
lemma hermitianReprToEuclideanLin_eq_eigenvalueMul
    {A : MatrixN n} (hA : A.IsHermitian) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((hA.eigenvectorBasis.repr (A.toEuclideanLin u)).ofLp i) =
      hA.eigenvalues i * ((hA.eigenvectorBasis.repr u).ofLp i) := by
  -- This is the matrix-form spectral theorem written in coordinates.
  simpa [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
    Matrix.IsHermitian.eigenvalues₀] using
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis_apply_self_apply
      finrank_euclideanSpace u ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- Helper for Chapter07 Theorem 7.3.5: the quadratic form of a Hermitian matrix is the weighted
sum of its ordered eigenvalues with weights given by squared eigenbasis coordinates. -/
lemma hermitianQuadratic_eq_sumEigenvaluesMulSq
    {A : MatrixN n} (hA : A.IsHermitian) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A.toEuclideanLin u) u =
      ∑ i : Fin n, hA.eigenvalues i * ((hA.eigenvectorBasis.repr u).ofLp i) ^ 2 := by
  let b := hA.eigenvectorBasis
  -- Parseval reduces the quadratic form to diagonal spectral coordinates.
  calc
    inner ℝ (A.toEuclideanLin u) u =
        ∑ i : Fin n, inner ℝ (A.toEuclideanLin u) (b i) * inner ℝ (b i) u := by
          simpa using (OrthonormalBasis.sum_inner_mul_inner b (A.toEuclideanLin u) u).symm
    _ = ∑ i : Fin n, ((b.repr (A.toEuclideanLin u)).ofLp i) * ((b.repr u).ofLp i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [real_inner_comm, ← b.repr_apply_apply (A.toEuclideanLin u) i, b.repr_apply_apply u i]
    _ = ∑ i : Fin n, (hA.eigenvalues i * ((b.repr u).ofLp i)) * ((b.repr u).ofLp i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hermitianReprToEuclideanLin_eq_eigenvalueMul hA u i]
    _ = ∑ i : Fin n, hA.eigenvalues i * ((b.repr u).ofLp i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring

/-- Helper for Chapter07 Theorem 7.3.5: the squared Euclidean norm is the sum of squared
coordinates in any orthonormal basis. -/
lemma euclideanNormSq_eq_sumSqCoords
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖u‖ ^ 2 = ∑ i : Fin n, ((b.repr u).ofLp i) ^ 2 := by
  -- Parseval with the same vector twice gives the coordinate norm formula.
  calc
    ‖u‖ ^ 2 = inner ℝ u u := by
      rw [real_inner_self_eq_norm_sq]
    _ = ∑ i : Fin n, inner ℝ u (b i) * inner ℝ (b i) u := by
      simpa using (OrthonormalBasis.sum_inner_mul_inner b u u).symm
    _ = ∑ i : Fin n, ((b.repr u).ofLp i) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [real_inner_comm, ← b.repr_apply_apply u i, b.repr_apply_apply u i]
      ring

/-- Helper for Chapter07 Theorem 7.3.5: evaluating a Hermitian matrix on one of its orthonormal
eigenvectors returns the corresponding ordered eigenvalue. -/
lemma eigenvectorInner_eq_orderedEigenvalue
    {A : MatrixN n} (hA : A.IsHermitian) (i : Fin n) :
    inner ℝ (A.toEuclideanLin (hA.eigenvectorBasis i)) (hA.eigenvectorBasis i) =
      hA.eigenvalues i := by
  -- Translate the matrix quadratic form to `xᵀ A x` and then apply the eigenvector formula.
  calc
    inner ℝ (A.toEuclideanLin (hA.eigenvectorBasis i)) (hA.eigenvectorBasis i) =
        (hA.eigenvectorBasis i).ofLp ⬝ᵥ A *ᵥ (hA.eigenvectorBasis i).ofLp := by
          rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
          simpa [real_inner_comm] using
            Matrix.inner_toEuclideanCLM A (hA.eigenvectorBasis i) (hA.eigenvectorBasis i)
    _ = hA.eigenvalues i := by
          simpa using (hA.eigenvalues_eq i).symm

/-- Helper for Chapter07 Theorem 7.3.5: the source condition number of `(7.3.27)`, interpreted
as the ordinary spectral condition number on the positive-definite branch and as `⊤` when the
regularized normal matrix is singular. This avoids exposing a source-unstated
positive-definiteness witness in the public theorem statement. -/
def sourceLevenbergMarquardtExtendedConditionNumber
    (J : JacobianMatrix m n) (hn : 0 < n) (μ : Set.Ioi (0 : ℝ)) : WithTop ℝ := by
  classical
  exact
    if hμ : (sourceLevenbergMarquardtRegularizedNormalMatrix J μ.1).PosDef then
      posDefSpectralConditionNumber hμ hn
    else
      ⊤

/-- Helper for Chapter07 Theorem 7.3.5: increasing the damping parameter adds only a nonnegative
multiple of the source damping matrix. -/
lemma sourceRegularizedNormalMatrix_eq_add_damping
    (J : JacobianMatrix m n) (μ₁ μ₂ : ℝ) :
    sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂ =
      sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁ +
        (μ₂ - μ₁) • levenbergMarquardtSourceDampingMatrix J := by
  -- Compare entries directly so the matrix algebra stays in the stable source spelling.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [sourceLevenbergMarquardtRegularizedNormalMatrix_eq,
      levenbergMarquardtSourceDampingMatrix]
    ring
  · simp [sourceLevenbergMarquardtRegularizedNormalMatrix_eq,
      levenbergMarquardtSourceDampingMatrix, hij]

/-- Helper for Chapter07 Theorem 7.3.5: positive definiteness persists when the positive damping
parameter increases. -/
lemma sourceRegularizedNormalMatrix_posDef_of_le
    (J : JacobianMatrix m n) {μ₁ μ₂ : ℝ} (hμ : μ₁ ≤ μ₂)
    (hPos : (sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁).PosDef) :
    (sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂).PosDef := by
  have hδ : 0 ≤ μ₂ - μ₁ := sub_nonneg.mpr hμ
  have hPert :
      ((μ₂ - μ₁) • levenbergMarquardtSourceDampingMatrix J).PosSemidef := by
    simpa using (sourceDampingMatrix_posSemidef J).smul hδ
  -- Rewrite the larger matrix as the smaller one plus a PSD perturbation.
  rw [sourceRegularizedNormalMatrix_eq_add_damping]
  exact Matrix.PosDef.add_posSemidef hPos hPert

/-- Helper for Chapter07 Theorem 7.3.5: every ordered Hermitian eigenvalue lies between the owner
endpoints used in the condition-number API. -/
lemma orderedHermitianEndpointBounds
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) (i : Fin n) :
    smallestHermitianEigenvalue hA hn ≤ hA.eigenvalues i ∧
      hA.eigenvalues i ≤ largestHermitianEigenvalue hA hn := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
  let j : Fin (Fintype.card (Fin n)) := e.symm i
  have hEigenvalue :
      hA.eigenvalues i = hA.eigenvalues₀ j := by
    -- Unfold the public eigenvalue owner only once so the endpoint bounds
    -- stay in the `eigenvalues₀` spelling.
    simp [Matrix.IsHermitian.eigenvalues, e, j]
  constructor
  · -- The transported index `j` is below the last entry, so antitonicity gives the lower bound.
    rw [hEigenvalue, smallestHermitianEigenvalue_eq]
    have hj_last :
        j ≤ (⟨n - 1, by simpa using Nat.sub_lt hn (Nat.succ_pos 0)⟩ :
          Fin (Fintype.card (Fin n))) := by
      rw [Fin.le_iff_val_le_val]
      exact Nat.le_pred_of_lt (by simpa using j.isLt)
    exact
      hA.eigenvalues₀_antitone hj_last
  · -- The same antitonicity bound from the first entry gives the upper endpoint control.
    rw [hEigenvalue, largestHermitianEigenvalue_eq]
    have hzero_le : (⟨0, by simpa using hn⟩ : Fin (Fintype.card (Fin n))) ≤ j := by
      rw [Fin.le_iff_val_le_val]
      simp
    exact
      (hA.eigenvalues₀_antitone hzero_le)

/-- Helper for Chapter07 Theorem 7.3.5: every nonzero Hermitian Rayleigh quotient lies between
the ordered spectral endpoints. -/
lemma hermitianRayleigh_mem_Icc_endpoints
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) :
    smallestHermitianEigenvalue hA hn ≤ inner ℝ (A.toEuclideanLin u) u / ‖u‖ ^ 2 ∧
      inner ℝ (A.toEuclideanLin u) u / ‖u‖ ^ 2 ≤ largestHermitianEigenvalue hA hn := by
  let b := hA.eigenvectorBasis
  have hNorm :
      ‖u‖ ^ 2 = ∑ i : Fin n, ((b.repr u).ofLp i) ^ 2 := euclideanNormSq_eq_sumSqCoords b u
  have hQuad :
      inner ℝ (A.toEuclideanLin u) u =
        ∑ i : Fin n, hA.eigenvalues i * ((b.repr u).ofLp i) ^ 2 :=
    hermitianQuadratic_eq_sumEigenvaluesMulSq hA u
  have hNormPos : 0 < ‖u‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hu) 2
  have hLowerScaled :
      smallestHermitianEigenvalue hA hn * ‖u‖ ^ 2 ≤ inner ℝ (A.toEuclideanLin u) u := by
    -- Bound each eigenvalue term below by the smallest endpoint.
    calc
      smallestHermitianEigenvalue hA hn * ‖u‖ ^ 2 =
          ∑ i : Fin n, smallestHermitianEigenvalue hA hn * ((b.repr u).ofLp i) ^ 2 := by
            rw [hNorm, Finset.mul_sum]
      _ ≤ ∑ i : Fin n, hA.eigenvalues i * ((b.repr u).ofLp i) ^ 2 := by
            exact Finset.sum_le_sum fun i _ => by
              have hBound := (orderedHermitianEndpointBounds hA hn i).1
              nlinarith [hBound, sq_nonneg ((b.repr u).ofLp i)]
      _ = inner ℝ (A.toEuclideanLin u) u := hQuad.symm
  have hUpperScaled :
      inner ℝ (A.toEuclideanLin u) u ≤ largestHermitianEigenvalue hA hn * ‖u‖ ^ 2 := by
    -- The same termwise comparison bounds the Rayleigh quotient above by the top endpoint.
    calc
      inner ℝ (A.toEuclideanLin u) u =
          ∑ i : Fin n, hA.eigenvalues i * ((b.repr u).ofLp i) ^ 2 := hQuad
      _ ≤ ∑ i : Fin n, largestHermitianEigenvalue hA hn * ((b.repr u).ofLp i) ^ 2 := by
            exact Finset.sum_le_sum fun i _ => by
              have hBound := (orderedHermitianEndpointBounds hA hn i).2
              nlinarith [hBound, sq_nonneg ((b.repr u).ofLp i)]
      _ = largestHermitianEigenvalue hA hn * ‖u‖ ^ 2 := by
            rw [hNorm, Finset.mul_sum]
  constructor
  · -- Clear the positive denominator to recover the lower Rayleigh bound.
    exact (le_div_iff₀ hNormPos).2 (by simpa [mul_comm] using hLowerScaled)
  · -- Clear the same denominator for the upper Rayleigh bound.
    exact (div_le_iff₀ hNormPos).2 (by simpa [mul_comm] using hUpperScaled)

/-- Helper for Chapter07 Theorem 7.3.5: evaluating a quadratic form on a standard basis vector
reads off the corresponding diagonal entry. -/
lemma diagonalEntry_eq_inner_basisFun
    {A : MatrixN n} (i : Fin n) :
    inner ℝ (A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℝ i))
      (EuclideanSpace.basisFun (Fin n) ℝ i) = A i i := by
  -- The standard basis vector kills every off-diagonal term in `uᵀAu`.
  rw [real_inner_comm, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  simpa [Matrix.dotProduct_mulVec, EuclideanSpace.basisFun_apply] using
    Matrix.inner_toEuclideanCLM A
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Helper for Chapter07 Theorem 7.3.5: the quadratic form of a diagonal matrix is the weighted
sum of the squared coordinates. -/
lemma diagonalQuadratic_eq_sumDiagonalMulSq
    (d : Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u =
      ∑ i : Fin n, d i * (u.ofLp i) ^ 2 := by
  -- Expanding the diagonal action leaves only the coordinate-wise weights.
  calc
    inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u =
        inner ℝ u ((Matrix.diagonal d).toEuclideanLin u) := by
          rw [real_inner_comm]
    _ = u.ofLp ⬝ᵥ (Matrix.diagonal d *ᵥ u.ofLp) := by
          rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
          simpa using Matrix.inner_toEuclideanCLM (Matrix.diagonal d) u u
    _ = (u.ofLp ᵥ* Matrix.diagonal d) ⬝ᵥ u.ofLp := by
          rw [Matrix.dotProduct_mulVec]
    _ = ∑ i : Fin n, (u.ofLp i * d i) * u.ofLp i := by
          simp [Matrix.vecMul_diagonal, dotProduct]
    _ = ∑ i : Fin n, d i * (u.ofLp i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring

/-- Helper for Chapter07 Theorem 7.3.5: pointwise bounds on diagonal entries induce the
corresponding quadratic-form bounds. -/
lemma diagonalQuadratic_bounds_of_entry_bounds
    (d : Fin n → ℝ) (α β : ℝ)
    (hdb : ∀ i, α ≤ d i ∧ d i ≤ β)
    (u : EuclideanSpace ℝ (Fin n)) :
    α * ‖u‖ ^ 2 ≤ inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u ∧
      inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u ≤ β * ‖u‖ ^ 2 := by
  have hNorm :
      ‖u‖ ^ 2 = ∑ i : Fin n, (u.ofLp i) ^ 2 := by
    -- In the standard orthonormal basis, the Euclidean norm is the sum of squared coordinates.
    simpa [EuclideanSpace.basisFun_repr] using
      euclideanNormSq_eq_sumSqCoords (EuclideanSpace.basisFun (Fin n) ℝ) u
  have hQuad :
      inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u =
        ∑ i : Fin n, d i * (u.ofLp i) ^ 2 :=
    diagonalQuadratic_eq_sumDiagonalMulSq d u
  constructor
  · -- Compare the diagonal quadratic form with the lower entry bound term-by-term.
    calc
      α * ‖u‖ ^ 2 = ∑ i : Fin n, α * (u.ofLp i) ^ 2 := by
        rw [hNorm, Finset.mul_sum]
      _ ≤ ∑ i : Fin n, d i * (u.ofLp i) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          rcases hdb i with ⟨hLower, _⟩
          nlinarith [sq_nonneg (u.ofLp i)]
      _ = inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u := hQuad.symm
  · -- The same coordinate-wise comparison gives the upper quadratic-form bound.
    calc
      inner ℝ ((Matrix.diagonal d).toEuclideanLin u) u =
          ∑ i : Fin n, d i * (u.ofLp i) ^ 2 := hQuad
      _ ≤ ∑ i : Fin n, β * (u.ofLp i) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          rcases hdb i with ⟨_, hUpper⟩
          nlinarith [sq_nonneg (u.ofLp i)]
      _ = β * ‖u‖ ^ 2 := by
        rw [hNorm, Finset.mul_sum]

/-- Helper for Chapter07 Theorem 7.3.5: once a regularized source matrix is positive definite,
the source damping quadratic form is squeezed between the rescaled spectral endpoints of that
regularized matrix. -/
lemma sourceDampingQuadratic_bounds_of_posDefRegularized
    (J : JacobianMatrix m n) {μ : ℝ}
    (hM : (sourceLevenbergMarquardtRegularizedNormalMatrix J μ).PosDef)
    (hn : 0 < n) (hOne : 0 < 1 + μ)
    (u : EuclideanSpace ℝ (Fin n)) :
    smallestHermitianEigenvalue hM.1 hn / (1 + μ) * ‖u‖ ^ 2 ≤
        inner ℝ ((levenbergMarquardtSourceDampingMatrix J).toEuclideanLin u) u ∧
      inner ℝ ((levenbergMarquardtSourceDampingMatrix J).toEuclideanLin u) u ≤
        largestHermitianEigenvalue hM.1 hn / (1 + μ) * ‖u‖ ^ 2 := by
  have hEntryBounds :
      ∀ i : Fin n,
        smallestHermitianEigenvalue hM.1 hn / (1 + μ) ≤ (Jᵀ * J) i i ∧
          (Jᵀ * J) i i ≤ largestHermitianEigenvalue hM.1 hn / (1 + μ) := by
    intro i
    let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i
    have he_ne : e ≠ 0 := by
      -- A standard basis vector is nonzero.
      dsimp [e]
      exact (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.ne_zero i
    have hLowerRay :=
      (hermitianRayleigh_mem_Icc_endpoints hM.1 hn e he_ne).1
    have hUpperRay :=
      (hermitianRayleigh_mem_Icc_endpoints hM.1 hn e he_ne).2
    have hDiag :
        inner ℝ ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ).toEuclideanLin e) e =
          (1 + μ) * (Jᵀ * J) i i := by
      -- On a basis vector, the regularized quadratic form collapses to the corresponding diagonal.
      rw [diagonalEntry_eq_inner_basisFun]
      simpa [levenbergMarquardtSourceDampingMatrix] using sourceRegularizedDiagonalEntry_eq J μ i
    have hLowerScaled :
        smallestHermitianEigenvalue hM.1 hn ≤ (1 + μ) * (Jᵀ * J) i i := by
      -- The least eigenvalue bounds every basis-vector Rayleigh quotient from below.
      have hNormE : ‖e‖ ^ 2 = 1 := by
        simp [e]
      rw [hDiag, hNormE, div_one] at hLowerRay
      exact hLowerRay
    have hUpperScaled :
        (1 + μ) * (Jᵀ * J) i i ≤ largestHermitianEigenvalue hM.1 hn := by
      -- The greatest eigenvalue bounds every basis-vector Rayleigh quotient from above.
      have hNormE : ‖e‖ ^ 2 = 1 := by
        simp [e]
      rw [hDiag, hNormE, div_one] at hUpperRay
      exact hUpperRay
    constructor
    · -- Divide the lower basis-vector bound by the positive factor `1 + μ`.
      exact (div_le_iff₀ hOne).2 (by simpa [mul_comm] using hLowerScaled)
    · -- Divide the upper basis-vector bound by the same positive factor.
      exact (le_div_iff₀ hOne).2 (by simpa [mul_comm] using hUpperScaled)
  -- Upgrade the coordinate bounds on the diagonal entries to the full quadratic form.
  simpa [levenbergMarquardtSourceDampingMatrix] using
    diagonalQuadratic_bounds_of_entry_bounds
      (d := fun i : Fin n ↦ (Jᵀ * J) i i)
      (smallestHermitianEigenvalue hM.1 hn / (1 + μ))
      (largestHermitianEigenvalue hM.1 hn / (1 + μ))
      hEntryBounds u

/-- Helper for Chapter07 Theorem 7.3.5: the top endpoint is realized by the corresponding public
eigenvalue entry. -/
lemma largestHermitianEigenvalue_eq_publicEigenvalue
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) :
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
      Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
    let iTop : Fin n := e ⟨0, by simpa using hn⟩
    hA.eigenvalues iTop = largestHermitianEigenvalue hA hn := by
  -- Route correction: after repairing the owner to `eigenvalues₀`, recover the matching public
  -- eigenvalue only through the inverse index witness, not through any order transport claim.
  simp [Matrix.IsHermitian.eigenvalues, largestHermitianEigenvalue]

/-- Helper for Chapter07 Theorem 7.3.5: the bottom endpoint is realized by the corresponding
public eigenvalue entry. -/
lemma smallestHermitianEigenvalue_eq_publicEigenvalue
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) :
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
      Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
    let iBot : Fin n :=
      e ⟨n - 1, by simpa using Nat.sub_lt hn (Nat.succ_pos 0)⟩
    hA.eigenvalues iBot = smallestHermitianEigenvalue hA hn := by
  -- The bottom endpoint is recovered by the same inverse-index witness at the last ordered slot.
  simp [Matrix.IsHermitian.eigenvalues, smallestHermitianEigenvalue]

/-- Helper for Chapter07 Theorem 7.3.5: positive definiteness forces the repaired smallest
Hermitian endpoint to be positive. -/
lemma smallestHermitianEigenvalue_pos
    {A : MatrixN n} (hPos : A.PosDef) (hn : 0 < n) :
    0 < smallestHermitianEigenvalue hPos.1 hn := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
  let iBot : Fin n := e ⟨n - 1, by simpa using Nat.sub_lt hn (Nat.succ_pos 0)⟩
  -- Rewrite the smallest endpoint to the matching public eigenvalue and use positivity there.
  have hEigenvalue : hPos.1.eigenvalues iBot = smallestHermitianEigenvalue hPos.1 hn := by
    simpa [e, iBot] using smallestHermitianEigenvalue_eq_publicEigenvalue hPos.1 hn
  rw [← hEigenvalue]
  exact hPos.eigenvalues_pos iBot

/-- Helper for Chapter07 Theorem 7.3.5: positive definiteness also makes the repaired largest
Hermitian endpoint positive. -/
lemma largestHermitianEigenvalue_pos
    {A : MatrixN n} (hPos : A.PosDef) (hn : 0 < n) :
    0 < largestHermitianEigenvalue hPos.1 hn := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
  let iTop : Fin n := e ⟨0, by simpa using hn⟩
  -- Use the public eigenvalue positivity at the transported top index.
  have hEigenvalue : hPos.1.eigenvalues iTop = largestHermitianEigenvalue hPos.1 hn := by
    simpa [e, iTop] using largestHermitianEigenvalue_eq_publicEigenvalue hPos.1 hn
  rw [← hEigenvalue]
  exact hPos.eigenvalues_pos iTop

/-- Helper for Chapter07 Theorem 7.3.5: increasing the source damping parameter splits the
regularized quadratic form into the old quadratic form plus the damping contribution. -/
lemma sourceRegularizedQuadratic_eq_add_damping
    (J : JacobianMatrix m n) (μ₁ μ₂ : ℝ)
    (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂).toEuclideanLin u) u =
      inner ℝ ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁).toEuclideanLin u) u +
        (μ₂ - μ₁) * inner ℝ ((levenbergMarquardtSourceDampingMatrix J).toEuclideanLin u) u := by
  -- Rewrite the larger matrix as the smaller one plus the extra damping, then expand linearity of
  -- the quadratic form once.
  rw [sourceRegularizedNormalMatrix_eq_add_damping (J := J) (μ₁ := μ₁) (μ₂ := μ₂)]
  simp [inner_add_left, real_inner_smul_left]

/-- Helper for Chapter07 Theorem 7.3.5: if both regularized source matrices are positive definite
and `μ₁ ≤ μ₂`, then the repaired spectral endpoints scale by the common source factor
`(1 + μ₂) / (1 + μ₁)`. -/
lemma regularizedEndpointScaleBounds_of_le
    (J : JacobianMatrix m n) (hn : 0 < n)
    {μ₁ μ₂ : Set.Ioi (0 : ℝ)} (hμ : μ₁ ≤ μ₂)
    (hPos₁ : (sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁.1).PosDef) :
    let hPos₂ := sourceRegularizedNormalMatrix_posDef_of_le J hμ hPos₁
    let c : ℝ := (1 + μ₂.1) / (1 + μ₁.1)
    largestHermitianEigenvalue hPos₂.1 hn ≤ c * largestHermitianEigenvalue hPos₁.1 hn ∧
      c * smallestHermitianEigenvalue hPos₁.1 hn ≤ smallestHermitianEigenvalue hPos₂.1 hn := by
  let hPos₂ := sourceRegularizedNormalMatrix_posDef_of_le J hμ hPos₁
  let δ : ℝ := μ₂.1 - μ₁.1
  let c : ℝ := (1 + μ₂.1) / (1 + μ₁.1)
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (α := Fin (Fintype.card (Fin n))) (β := Fin n) (by simp)
  let iTop : Fin n := e ⟨0, by simpa using hn⟩
  let iBot : Fin n :=
    e ⟨n - 1, by simpa using Nat.sub_lt hn (Nat.succ_pos 0)⟩
  let uTop : EuclideanSpace ℝ (Fin n) := hPos₂.1.eigenvectorBasis iTop
  let uBot : EuclideanSpace ℝ (Fin n) := hPos₂.1.eigenvectorBasis iBot
  have hδ : 0 ≤ δ := by
    exact sub_nonneg.mpr hμ
  have hOne₁ : 0 < 1 + μ₁.1 := by
    have hμ₁ : (0 : ℝ) < μ₁.1 := μ₁.2
    nlinarith
  have hNormTop : ‖uTop‖ ^ 2 = 1 := by
    -- The extremal eigenvectors come from an orthonormal basis, hence have unit norm.
    have hNorm : ‖uTop‖ = 1 := by
      dsimp [uTop]
      exact hPos₂.1.eigenvectorBasis.norm_eq_one iTop
    nlinarith [hNorm]
  have hNormBot : ‖uBot‖ ^ 2 = 1 := by
    -- The same unit-norm fact holds for the bottom eigenvector.
    have hNorm : ‖uBot‖ = 1 := by
      dsimp [uBot]
      exact hPos₂.1.eigenvectorBasis.norm_eq_one iBot
    nlinarith [hNorm]
  have huTop_ne : uTop ≠ 0 := by
    -- Orthonormal basis vectors are nonzero.
    simpa [uTop] using hPos₂.1.eigenvectorBasis.orthonormal.ne_zero iTop
  have huBot_ne : uBot ≠ 0 := by
    -- The bottom eigenvector is also nonzero for the same reason.
    simpa [uBot] using hPos₂.1.eigenvectorBasis.orthonormal.ne_zero iBot
  have hTopEq :
      inner ℝ
          ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂.1).toEuclideanLin uTop) uTop =
        largestHermitianEigenvalue hPos₂.1 hn := by
    -- Evaluate the larger matrix on its top eigenvector and rewrite to the repaired endpoint.
    calc
      inner ℝ
          ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂.1).toEuclideanLin uTop) uTop =
        hPos₂.1.eigenvalues iTop := by
          simpa [uTop] using eigenvectorInner_eq_orderedEigenvalue hPos₂.1 iTop
      _ = largestHermitianEigenvalue hPos₂.1 hn := by
          simpa [iTop] using largestHermitianEigenvalue_eq_publicEigenvalue hPos₂.1 hn
  have hBotEq :
      inner ℝ
          ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂.1).toEuclideanLin uBot) uBot =
        smallestHermitianEigenvalue hPos₂.1 hn := by
    -- The same endpoint rewrite identifies the smaller matrix value on the bottom eigenvector.
    calc
      inner ℝ
          ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂.1).toEuclideanLin uBot) uBot =
        hPos₂.1.eigenvalues iBot := by
          simpa [uBot] using eigenvectorInner_eq_orderedEigenvalue hPos₂.1 iBot
      _ = smallestHermitianEigenvalue hPos₂.1 hn := by
          simpa [iBot] using smallestHermitianEigenvalue_eq_publicEigenvalue hPos₂.1 hn
  have hRayTop :
      inner ℝ
          ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁.1).toEuclideanLin uTop) uTop ≤
        largestHermitianEigenvalue hPos₁.1 hn := by
    -- Evaluate the smaller matrix Rayleigh quotient on the larger matrix's top eigenvector.
    have hTop := (hermitianRayleigh_mem_Icc_endpoints hPos₁.1 hn uTop huTop_ne).2
    rw [hNormTop, div_one] at hTop
    exact hTop
  have hRayBot :
      smallestHermitianEigenvalue hPos₁.1 hn ≤
        inner ℝ
          ((sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁.1).toEuclideanLin uBot) uBot := by
    -- The smaller matrix's bottom endpoint also bounds the larger matrix's bottom eigenvector.
    have hBot := (hermitianRayleigh_mem_Icc_endpoints hPos₁.1 hn uBot huBot_ne).1
    rw [hNormBot, div_one] at hBot
    exact hBot
  have hDTop :
      inner ℝ ((levenbergMarquardtSourceDampingMatrix J).toEuclideanLin uTop) uTop ≤
        largestHermitianEigenvalue hPos₁.1 hn / (1 + μ₁.1) := by
    -- Apply the source damping quadratic bound to the top eigenvector and use its unit norm.
    have hTop :=
      (sourceDampingQuadratic_bounds_of_posDefRegularized J hPos₁ hn hOne₁ uTop).2
    simpa [hNormTop] using hTop
  have hDBot :
      smallestHermitianEigenvalue hPos₁.1 hn / (1 + μ₁.1) ≤
        inner ℝ ((levenbergMarquardtSourceDampingMatrix J).toEuclideanLin uBot) uBot := by
    -- The same damping bound supplies the lower endpoint control on the bottom eigenvector.
    have hBot :=
      (sourceDampingQuadratic_bounds_of_posDefRegularized J hPos₁ hn hOne₁ uBot).1
    simpa [hNormBot] using hBot
  have hScaleTop :
      largestHermitianEigenvalue hPos₂.1 hn ≤
        largestHermitianEigenvalue hPos₁.1 hn +
          δ * (largestHermitianEigenvalue hPos₁.1 hn / (1 + μ₁.1)) := by
    -- Split the larger quadratic form into the old quadratic form plus the damping perturbation.
    rw [← hTopEq, sourceRegularizedQuadratic_eq_add_damping]
    exact add_le_add hRayTop (mul_le_mul_of_nonneg_left hDTop hδ)
  have hScaleBot :
      smallestHermitianEigenvalue hPos₁.1 hn +
          δ * (smallestHermitianEigenvalue hPos₁.1 hn / (1 + μ₁.1)) ≤
        smallestHermitianEigenvalue hPos₂.1 hn := by
    -- The lower endpoint gains the same nonnegative damping contribution.
    rw [← hBotEq, sourceRegularizedQuadratic_eq_add_damping]
    exact add_le_add hRayBot (mul_le_mul_of_nonneg_left hDBot hδ)
  have hTopRewrite :
      largestHermitianEigenvalue hPos₁.1 hn +
          δ * (largestHermitianEigenvalue hPos₁.1 hn / (1 + μ₁.1)) =
        c * largestHermitianEigenvalue hPos₁.1 hn := by
    -- Convert the additive source scaling factor to the common ratio `(1 + μ₂) / (1 + μ₁)`.
    unfold c δ
    field_simp [ne_of_gt hOne₁]
    ring_nf
  have hBotRewrite :
      smallestHermitianEigenvalue hPos₁.1 hn +
          δ * (smallestHermitianEigenvalue hPos₁.1 hn / (1 + μ₁.1)) =
        c * smallestHermitianEigenvalue hPos₁.1 hn := by
    -- The same scalar identity rewrites the lower endpoint scaling factor.
    unfold c δ
    field_simp [ne_of_gt hOne₁]
    ring_nf
  constructor
  · -- Rewrite the additive upper bound into the common multiplicative scale factor.
    rw [← hTopRewrite]
    exact hScaleTop
  · -- Rewrite the additive lower bound into the same common scale factor.
    rw [← hBotRewrite]
    exact hScaleBot

/-- Helper for Chapter07 Theorem 7.3.5: if two positive denominators share the same positive scale
comparison, then the corresponding ratios are ordered the same way. -/
lemma ratio_le_ratio_of_commonScale
    {a₁ a₂ b₁ b₂ c : ℝ}
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (ha : a₂ ≤ c * a₁) (hb : c * b₁ ≤ b₂) :
    a₂ / b₂ ≤ a₁ / b₁ := by
  have hb₁_nonneg : 0 ≤ b₁ := le_of_lt hb₁
  -- Clear the positive denominators and compare the cross products using the shared scale factor.
  refine (div_le_div_iff₀ hb₂ hb₁).2 ?_
  have hLeft : a₂ * b₁ ≤ (c * a₁) * b₁ := by
    exact mul_le_mul_of_nonneg_right ha hb₁_nonneg
  have hRight : (c * a₁) * b₁ ≤ a₁ * b₂ := by
    have hScaled := mul_le_mul_of_nonneg_left hb ha₁
    simpa [mul_assoc, mul_left_comm, mul_comm] using hScaled
  exact le_trans hLeft hRight

/-- Chapter07 Theorem 7.3.5: for `(7.3.27)` with the source damping matrix
`D(x) = diag (diag (J(x)ᵀ * J(x)))`, the spectral condition number of
`J(x)ᵀ * J(x) + μ • D(x)` is a non-increasing function of `μ` for positive damping
parameters `μ`; in the singular case, this source-facing condition-number owner takes value
`⊤`, so no separate positive-definiteness witness is exposed in the theorem statement. -/
theorem levenbergMarquardtConditionNumber_antitone
    (J : JacobianMatrix m n)
    (hn : 0 < n) :
    Antitone
      (sourceLevenbergMarquardtExtendedConditionNumber J hn) := by
  intro μ₁ μ₂ hμ
  by_cases hPos₁ :
      (sourceLevenbergMarquardtRegularizedNormalMatrix J μ₁.1).PosDef
  · -- Route correction: instead of unfolding endpoint owners again, reuse the Chapter 1 Rayleigh
    -- endpoint bounds together with the source damping comparison and one scalar endgame.
    have hPos₂ :
        (sourceLevenbergMarquardtRegularizedNormalMatrix J μ₂.1).PosDef :=
      sourceRegularizedNormalMatrix_posDef_of_le J hμ hPos₁
    have hOne₁ : 0 < 1 + μ₁.1 := by
      nlinarith [show 0 < μ₁.1 from μ₁.2]
    have hOne₂ : 0 < 1 + μ₂.1 := by
      nlinarith [show 0 < μ₂.1 from μ₂.2]
    have hSmall₁ :
        0 < smallestHermitianEigenvalue hPos₁.1 hn :=
      smallestHermitianEigenvalue_pos hPos₁ hn
    have hSmall₂ :
        0 < smallestHermitianEigenvalue hPos₂.1 hn :=
      smallestHermitianEigenvalue_pos hPos₂ hn
    have hLarge₁ :
        0 ≤ largestHermitianEigenvalue hPos₁.1 hn := by
      exact le_of_lt (largestHermitianEigenvalue_pos hPos₁ hn)
    have hScale :=
      regularizedEndpointScaleBounds_of_le J hn hμ hPos₁
    have hRatio :
        posDefSpectralConditionNumber hPos₂ hn ≤ posDefSpectralConditionNumber hPos₁ hn := by
      -- The endpoint scaling bounds have the same positive factor, so the ratio decreases.
      simpa [posDefSpectralConditionNumber_eq, hermitianSpectralConditionNumber_eq] using
        ratio_le_ratio_of_commonScale hLarge₁ hSmall₁ hSmall₂ hScale.1 hScale.2
    -- On the positive-definite branch, the source-facing owner is exactly the repaired spectral
    -- condition number.
    have hRatioTop :
        (posDefSpectralConditionNumber hPos₂ hn : WithTop ℝ) ≤
          (posDefSpectralConditionNumber hPos₁ hn : WithTop ℝ) := by
      exact_mod_cast hRatio
    rw [sourceLevenbergMarquardtExtendedConditionNumber, dif_pos hPos₂]
    rw [sourceLevenbergMarquardtExtendedConditionNumber, dif_pos hPos₁]
    exact hRatioTop
  · -- When the smaller-parameter matrix is not positive definite, the target value is `⊤`.
    have hPos₁' :
        ¬(Jᵀ * J + μ₁.1 • Matrix.diagonal (fun i : Fin n ↦ (Jᵀ * J) i i)).PosDef := by
      simpa [sourceLevenbergMarquardtRegularizedNormalMatrix_eq] using hPos₁
    have hμ₁_top :
        sourceLevenbergMarquardtExtendedConditionNumber J hn μ₁ = (⊤ : WithTop ℝ) := by
      simp [sourceLevenbergMarquardtExtendedConditionNumber,
        sourceLevenbergMarquardtRegularizedNormalMatrix_eq,
        hPos₁']
    rw [hμ₁_top]
    exact le_top

end
