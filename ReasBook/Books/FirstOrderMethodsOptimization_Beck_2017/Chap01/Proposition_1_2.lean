/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Spectrum

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Matrix.Norms.L2Operator

section

variable {m n : ℕ}

theorem transpose_mul_self_isHermitian (A : Matrix (Fin m) (Fin n) ℝ) :
    (A.transpose * A).IsHermitian := by
  simpa using Matrix.isHermitian_conjTranspose_mul_self A

/-- The ordered eigenvalue function of the Gram matrix `Aᵀ A`, listed in weakly decreasing order.
This is the matrix-side companion to the Gram-operator spectrum of `A.toEuclideanLin† ∘ A`. -/
noncomputable def transpose_mul_self_eigenvalue_function
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin n → ℝ :=
  fun i ↦ (transpose_mul_self_isHermitian A).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- The `i`-th coordinate of `transpose_mul_self_eigenvalue_function A` is the `i`-th ordered
eigenvalue of the Gram matrix `Aᵀ A`. -/
@[simp] theorem transpose_mul_self_eigenvalue_function_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    transpose_mul_self_eigenvalue_function A i =
      (transpose_mul_self_isHermitian A).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) := by
  rfl

/-- Helper for Proposition 1.2: on a positive real finite-dimensional endomorphism, the operator
norm is the largest eigenvalue in the decreasing eigenvalue list. -/
private theorem positiveOperatorNormEqTopEigenvalueReal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {S : E →ₗ[ℝ] E} {k : ℕ} (hn : Module.finrank ℝ E = k) (hk : 0 < k)
    (hS : S.IsPositive) :
    ‖S.toContinuousLinearMap‖ = hS.isSymmetric.eigenvalues hn ⟨0, hk⟩ := by
  have hS_nonneg : ∀ x : E, 0 ≤ S.toContinuousLinearMap.rayleighQuotient x := by
    intro x
    by_cases hx : x = 0
    · simp [ContinuousLinearMap.rayleighQuotient, hx]
    · rw [ContinuousLinearMap.rayleighQuotient]
      exact div_nonneg (hS.inner_nonneg_left x) (sq_nonneg ‖x‖)
  have hbdd_all :
      BddAbove (Set.range fun x : E ↦ S.toContinuousLinearMap.rayleighQuotient x) := by
    refine ⟨‖S.toContinuousLinearMap‖, ?_⟩
    rintro y ⟨x, rfl⟩
    exact le_trans
      (by
        simpa [abs_of_nonneg (hS_nonneg x)] using
          S.toContinuousLinearMap.rayleighQuotient_le_norm x)
      le_rfl
  have hbdd_nonzero :
      BddAbove
        (Set.range fun x : {x : E // x ≠ 0} ↦ S.toContinuousLinearMap.rayleighQuotient x) :=
    hbdd_all.mono <| by
      rintro y ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (hn ▸ hk)
  letI : Nonempty {x : E // x ≠ 0} := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨⟨x, hx⟩⟩
  have hiSup_nonzero_nonneg :
      0 ≤ ⨆ x : {x : E // x ≠ 0}, S.toContinuousLinearMap.rayleighQuotient x := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact le_trans (hS_nonneg x) (le_ciSup hbdd_nonzero ⟨x, hx⟩)
  have hsup_eq : (⨆ x : E, S.toContinuousLinearMap.rayleighQuotient x) =
      ⨆ x : {x : E // x ≠ 0}, S.toContinuousLinearMap.rayleighQuotient x := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro x
      by_cases hx : x = 0
      · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
        exact hiSup_nonzero_nonneg
      · exact le_ciSup hbdd_nonzero ⟨x, hx⟩
    · refine ciSup_le ?_
      intro x
      exact le_ciSup hbdd_all x.1
  have hnorm_eq_sup :
      ‖S.toContinuousLinearMap‖ = ⨆ x : E, S.toContinuousLinearMap.rayleighQuotient x := by
    -- Positivity removes the absolute value from the Rayleigh-quotient norm formula.
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hS.isSymmetric]
    congr with x
    exact abs_of_nonneg (hS_nonneg x)
  have hM_eig :
      Module.End.HasEigenvalue S
        (⨆ x : {x : E // x ≠ 0}, S.toContinuousLinearMap.rayleighQuotient x) := by
    -- The maximal Rayleigh quotient is itself an eigenvalue of the symmetric operator.
    simpa [ContinuousLinearMap.rayleighQuotient] using
      (LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional (T := S) hS.isSymmetric)
  obtain ⟨j, hj⟩ := hS.isSymmetric.exists_eigenvalues_eq hn hM_eig
  rw [hnorm_eq_sup, hsup_eq]
  apply le_antisymm
  · -- The decreasing spectral ordering bounds every eigenvalue by the first entry.
    rw [← hj]
    exact (hS.isSymmetric.eigenvalues_antitone hn)
      (show (⟨0, hk⟩ : Fin k) ≤ j by exact Nat.zero_le _)
  · let i0 : Fin k := ⟨0, hk⟩
    have hi0_ne : hS.isSymmetric.eigenvectorBasis hn i0 ≠ 0 := by
      intro hzero
      have hnorm : ‖hS.isSymmetric.eigenvectorBasis hn i0‖ = 1 :=
        OrthonormalBasis.norm_eq_one _ _
      simp [hzero] at hnorm
    have hray :
        S.toContinuousLinearMap.rayleighQuotient (hS.isSymmetric.eigenvectorBasis hn i0) =
          hS.isSymmetric.eigenvalues hn i0 := by
      -- Evaluate the Rayleigh quotient on a unit eigenvector for the top eigenvalue.
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
      change
        RCLike.re
            (inner ℝ (S (hS.isSymmetric.eigenvectorBasis hn i0))
              (hS.isSymmetric.eigenvectorBasis hn i0)) /
          ‖hS.isSymmetric.eigenvectorBasis hn i0‖ ^ 2 = hS.isSymmetric.eigenvalues hn i0
      rw [hS.isSymmetric.apply_eigenvectorBasis hn i0, inner_smul_left,
        OrthonormalBasis.norm_eq_one]
      simp
    rw [← hray]
    exact le_ciSup hbdd_nonzero ⟨hS.isSymmetric.eigenvectorBasis hn i0, hi0_ne⟩

/-- Helper for Proposition 1.2: the operator norm of a real finite-dimensional linear map equals
its first singular value. -/
private theorem realOperatorNormEqFirstSingularValue
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) :
    ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  by_cases hk : 0 < Module.finrank ℝ E
  · let k : ℕ := Module.finrank ℝ E
    have hn : Module.finrank ℝ E = k := rfl
    have hgram :=
      positiveOperatorNormEqTopEigenvalueReal hn hk
        (LinearMap.isPositive_adjoint_comp_self T)
    have hnorm_sq : ‖T.toContinuousLinearMap‖ ^ 2 =
        (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn ⟨0, hk⟩ := by
      -- Compare `‖T‖²` with the top Gram eigenvalue.
      calc
        ‖T.toContinuousLinearMap‖ ^ 2 = ‖(LinearMap.adjoint T ∘ₗ T).toContinuousLinearMap‖ := by
          simpa [pow_two] using
            (ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap).symm
        _ = (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn ⟨0, hk⟩ := hgram
    have hsq : ‖T.toContinuousLinearMap‖ ^ 2 = T.singularValues 0 ^ 2 := by
      -- The squared singular values are the ordered eigenvalues of `T†T`.
      exact hnorm_sq.trans (LinearMap.sq_singularValues_fin T hn ⟨0, hk⟩).symm
    have hnorm_nonneg : 0 ≤ ‖T.toContinuousLinearMap‖ := norm_nonneg _
    have hσ_nonneg : 0 ≤ T.singularValues 0 := T.singularValues_nonneg 0
    -- Both sides are nonnegative, so the square equality upgrades to equality.
    exact le_antisymm
      (by nlinarith [hsq])
      (by nlinarith [hsq])
  · have hfinrank : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hk
    have hzero : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hfinrank
    have hT : T = 0 := by
      -- A linear map out of the zero-dimensional space is zero.
      ext x
      simp [hzero x]
    rw [hT]
    simp

-- Proof sketch: use the canonical `Matrix.Norms.L2Operator` norm, identify it with the operator
-- norm of `A.toEuclideanLin`, then apply the singular-value description
-- `T.singularValues 0 = √(eigenvalue₀(T†T))` together with
-- `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`.
/-- Proposition 1.2 (`source-facing`; `core/canonical` owner: `LinearMap.singularValues`;
`bridge/view`: `Matrix.Norms.L2Operator`): for a real matrix equipped with the Euclidean induced
operator norm, the norm equals its largest singular value. -/
theorem l2_induced_matrix_norm_eq_max_singular_value
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = A.toEuclideanLin.singularValues 0 := by
  -- Rewrite the matrix norm through `toEuclideanLin` and apply the linear-map singular-value
  -- formula.
  simpa [Matrix.l2_opNorm_def] using
    (realOperatorNormEqFirstSingularValue A.toEuclideanLin)

/-- Canonical singular-value/Gram-spectrum bridge (`bridge/view`): the square of the `i`-th
singular value of `A` equals the `i`-th ordered eigenvalue of the Gram matrix `Aᵀ A`. -/
theorem sq_singular_value_eq_transpose_mul_self_eigenvalue_function
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    A.toEuclideanLin.singularValues i ^ 2 = transpose_mul_self_eigenvalue_function A i := by
  have hadj : LinearMap.adjoint A.toEuclideanLin = A.transpose.toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A)).symm
  have hcomp :
      LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin =
        (A.transpose * A).toEuclideanLin := by
    -- Normalize the Gram operator of `A.toEuclideanLin` to the matrix-side Gram matrix `Aᵀ A`.
    ext x j
    have hmul :
        (A.transpose * A).toEuclideanLin x =
          A.transpose.toEuclideanLin (A.toEuclideanLin x) := by
      simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
        (Matrix.toLin_mul_apply
          (v₁ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis)
          (v₃ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
          (A := A.transpose) (B := A) x)
    rw [LinearMap.comp_apply, hadj]
    exact congrArg (fun y => y.ofLp j) hmul.symm
  -- After the Gram rewrite, `sq_singularValues_fin` is exactly the matrix-side eigenvalue claim.
  simpa [transpose_mul_self_eigenvalue_function_apply, Matrix.IsHermitian.eigenvalues₀, hcomp] using
    (LinearMap.sq_singularValues_fin (T := A.toEuclideanLin) (hn := finrank_euclideanSpace)
      (i := Fin.cast (Fintype.card_fin n).symm i))

/-- Companion bridge for Proposition 1.2 (`bridge/view`): the largest singular value of a real
matrix is the square root of the largest eigenvalue of the Gram matrix `Aᵀ A`. Since the
eigenvalues are listed in decreasing order, `⟨0, hn⟩` selects the largest one. -/
theorem max_singular_value_eq_sqrt_max_gram_eigenvalue
    (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    A.toEuclideanLin.singularValues 0 =
      Real.sqrt (transpose_mul_self_eigenvalue_function A ⟨0, hn⟩) := by
  rw [← sq_eq_sq₀ (A.toEuclideanLin.singularValues_nonneg 0) (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt]
  · exact sq_singular_value_eq_transpose_mul_self_eigenvalue_function A ⟨0, hn⟩
  · rw [← sq_singular_value_eq_transpose_mul_self_eigenvalue_function A ⟨0, hn⟩]
    positivity

/-- Companion reformulation of Proposition 1.2 in Gram-matrix eigenvalue form. -/
theorem l2_induced_matrix_norm_eq_sqrt_max_gram_eigenvalue
    (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    ‖A‖ = Real.sqrt (transpose_mul_self_eigenvalue_function A ⟨0, hn⟩) := by
  exact (l2_induced_matrix_norm_eq_max_singular_value A).trans
    (max_singular_value_eq_sqrt_max_gram_eigenvalue A hn)

end
