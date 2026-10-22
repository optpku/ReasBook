/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

open scoped Matrix.Norms.L2Operator MatrixOrder

/- Proposition 6.13 lies in the Euclidean matrix operator-norm / Gram-spectrum domain.

Primary domain:
- real matrices equipped with the Euclidean induced operator norm.

Sampled owner-style declarations:
- `Matrix.greatestEigenvalue` and the notation `λ_max(H)` in `Chap04/Definition_4_1_6`, the
  project owner for the largest real spectral value;
- mathlib's scoped `Matrix.Norms.L2Operator` norm `‖A‖`, the canonical Euclidean operator norm on
  matrices;
- the Gram matrix expression `Aᵀ * A`, whose largest eigenvalue controls the Euclidean operator
  norm.

Best owner abstraction:
- source-facing: the Euclidean operator norm of a real matrix;
- core/canonical: the ambient `Matrix.Norms.L2Operator` norm together with `λ_max`;
- bridge/view: the equivalent `sSup (spectrum ℝ (Aᵀ * A))` formulation used downstream.
-/

-- Proof sketch: square the Euclidean operator norm, rewrite `‖A x‖^2` as the Rayleigh quotient
-- `xᵀ (Aᵀ * A) x`, identify its maximum over the unit sphere with `λ_max(Aᵀ * A)`, and then take
-- square roots.
/-- Helper for Proposition 6.13: the Gram matrix `Aᵀ * A` is nonnegative in the matrix order. -/
lemma transpose_mul_self_nonneg
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ (Aᵀ * A : Matrix (Fin n) (Fin n) ℝ) := by
  -- Convert the standard positive-semidefinite Gram-matrix fact into the matrix-order inequality.
  rw [Matrix.nonneg_iff_posSemidef]
  simpa using Matrix.posSemidef_conjTranspose_mul_self A

/-- Helper for Proposition 6.13: the Gram matrix norm is the square of the Euclidean operator
norm. -/
lemma norm_transpose_mul_self_eq_sq_l2OperatorNorm
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(Aᵀ * A : Matrix (Fin n) (Fin n) ℝ)‖ = ‖A‖ ^ (2 : ℕ) := by
  -- Rewrite the conjugate-transpose formula from mathlib in the real setting and package the
  -- product as a square.
  calc
    ‖(Aᵀ * A : Matrix (Fin n) (Fin n) ℝ)‖ = ‖A‖ * ‖A‖ := by
      simpa using Matrix.l2_opNorm_conjTranspose_mul_self A
    _ = ‖A‖ ^ (2 : ℕ) := by ring

/-- Helper for Proposition 6.13: every real spectral value of a nonnegative matrix is bounded above
by the operator norm. -/
lemma le_norm_of_mem_spectrum_of_nonneg
    {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : 0 ≤ G)
    {x : ℝ} (hx : x ∈ spectrum ℝ G) :
    x ≤ ‖G‖ := by
  -- Nonnegative matrices have nonnegative real spectral values, so the spectral norm bound on
  -- `|x|` becomes a direct order bound on `x`.
  have hx_nonneg : 0 ≤ x := spectrum_nonneg_of_nonneg hG hx
  have hx_le_norm : ‖x‖ ≤ ‖G‖ := spectrum.norm_le_norm_of_mem hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg] using hx_le_norm

/-- Helper for Proposition 6.13: a nonnegative real square matrix contains its operator norm in
its real spectrum. -/
lemma matrixNorm_mem_spectrum_of_nonneg
    {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : 0 ≤ G) :
    ‖G‖ ∈ spectrum ℝ G := by
  let T : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ) G
  have hG_selfAdjoint : IsSelfAdjoint G := IsSelfAdjoint.of_nonneg hG
  have hT_selfAdjoint : IsSelfAdjoint T := by
    -- Convert matrix nonnegativity to self-adjointness of the Euclidean operator representing `G`.
    have hT_symm : (Matrix.toEuclideanLin G).IsSymmetric :=
      (Matrix.isSymmetric_toEuclideanLin_iff (A := G)).2 hG_selfAdjoint.isHermitian
    have hT_linear : IsSelfAdjoint (Matrix.toEuclideanLin G) :=
      (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp hT_symm
    simpa [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (LinearMap.isSelfAdjoint_toContinuousLinearMap_iff (T := Matrix.toEuclideanLin G)).2
        hT_linear
  have hrad_eq : spectralRadius ℝ G = ‖G‖₊ := by
    -- Compare the matrix spectral radius with the Euclidean operator spectral radius, then use the
    -- self-adjoint operator formula on `T`.
    calc
      spectralRadius ℝ G = spectralRadius ℝ T := by
        unfold spectralRadius
        rw [ContinuousLinearMap.spectrum_eq]
        simp [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.spectrum_toEuclideanLin]
      _ = ‖T‖₊ := ContinuousLinearMap.spectralRadius_eq_nnnorm (T := T) hT_selfAdjoint
      _ = ‖G‖₊ := by
        simpa [T] using (Matrix.cstar_nnnorm_def G).symm
  have hspec_nonempty : (spectrum ℝ G).Nonempty := by
    refine ⟨hG_selfAdjoint.isHermitian.eigenvalues 0, ?_⟩
    exact hG_selfAdjoint.isHermitian.eigenvalues_mem_spectrum_real 0
  have hspec :
      (spectralRadius ℝ G).toReal ∈ spectrum ℝ G :=
    Real.spectralRadius_mem_spectrum (a := G) hspec_nonempty
      (SpectrumRestricts.nnreal_of_nonneg hG)
  -- The nonnegative spectral-radius point is exactly the matrix norm after the previous rewrite.
  simpa [hrad_eq] using hspec

/-- Helper for Proposition 6.13: a nonnegative real square matrix has its norm as the greatest
point of its real spectrum. -/
lemma isGreatest_spectrum_norm_of_nonneg
    {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : 0 ≤ G) :
    IsGreatest (spectrum ℝ G) ‖G‖ := by
  refine ⟨?_, ?_⟩
  · -- The matrix-side helper packages the canonical norm-membership fact with no transport.
    exact matrixNorm_mem_spectrum_of_nonneg G hG
  · intro x hx
    -- The upper bound is the closed spectral estimate recorded in the previous helper.
    exact le_norm_of_mem_spectrum_of_nonneg G hG hx

/-- Proposition 6.13: for a real matrix `A`, the operator norm induced by the Euclidean norms on
`ℝ^n` and `ℝ^m` is the square root of the largest eigenvalue of the Gram matrix `Aᵀ * A`. -/
theorem l2OperatorNorm_eq_sqrt_greatestEigenvalue_transpose_mul_self
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (λ_max((Aᵀ * A : Matrix (Fin n) (Fin n) ℝ))) := by
  cases n with
  | zero =>
      have hA0 : A = 0 := Subsingleton.elim _ _
      subst hA0
      -- In the zero-dimensional domain, every matrix is zero and the formula collapses to `0 = 0`.
      simp [Matrix.greatestEigenvalue]
  | succ n =>
      let G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Aᵀ * A
      have hG : 0 ≤ G := by
        -- The Gram matrix is nonnegative, so the nonnegative-spectrum helper applies.
        simpa [G] using transpose_mul_self_nonneg A
      have hgreatest : IsGreatest (spectrum ℝ G) ‖G‖ := by
        -- Route correction: use the direct nonnegative-spectrum API on the Gram matrix instead of
        -- transporting through `Matrix.toEuclideanLin`.
        exact isGreatest_spectrum_norm_of_nonneg G hG
      have hGnorm : ‖G‖ = ‖A‖ ^ (2 : ℕ) := by
        -- The Gram-matrix norm is exactly the squared Euclidean operator norm.
        simpa [G] using norm_transpose_mul_self_eq_sq_l2OperatorNorm A
      -- Route correction: package the spectral maximum first, then rewrite `λ_max` by its owner
      -- definition to keep the main proof as a short square-root calculation.
      calc
        ‖A‖ = Real.sqrt (‖A‖ ^ (2 : ℕ)) := by
          -- Taking the square root of the norm square returns the nonnegative operator norm.
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg A)]
        _ = Real.sqrt (‖G‖) := by
          -- Rewrite through the norm identity for the Gram matrix before replacing the spectral
          -- supremum.
          rw [hGnorm.symm]
        _ = Real.sqrt (sSup (spectrum ℝ G)) := by
          -- The spectral helper identifies the Gram-matrix norm with the top point of the
          -- spectrum.
          rw [← hgreatest.csSup_eq]
        _ = Real.sqrt (λ_max((Aᵀ * A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))) := by
          -- Finish by unfolding the chapter owner `λ_max`.
          simp [G, Matrix.greatestEigenvalue]

-- Proof sketch: unfold `λ_max` in the main theorem as the supremum of the real spectrum of the
-- Gram matrix `Aᵀ * A`.
/-- Rewriting the Euclidean operator norm formula through the definition
`λ_max(H) = sSup (spectrum ℝ H)` recovers the spectrum-supremum form used elsewhere in the
chapter. -/
theorem l2OperatorNorm_eq_sqrt_sSup_spectrum_transpose_mul_self
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (sSup (spectrum ℝ (Aᵀ * A))) := by
  -- This is exactly the main theorem after unfolding the project owner `λ_max`.
  simpa [Matrix.greatestEigenvalue] using
    l2OperatorNorm_eq_sqrt_greatestEigenvalue_transpose_mul_self A

end
