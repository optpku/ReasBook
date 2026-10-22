/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.Subspace
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_19

-- The helper prefix for Lemma 7.3 lives in this support file so the signed-projector attainer
-- theorem elaborates once here and the source-facing theorem file can import the stabilized API.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped BigOperators MatrixOrder SupportFunction RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Lemma 7.3: the Frobenius norm squared of a symmetric matrix is the sum of the
squares of its ordered eigenvalues. -/
theorem frobenius_norm_sq_eq_sum_eigenvalues_sq
    (X : SymmMat) :
    ‖X‖ ^ (2 : ℕ) = ∑ i : Fin n, (eigenvalues X i) ^ (2 : ℕ) := by
  let e := (isHermitian X).eigenvectorUnitary
  have hX : (X : Mat).IsHermitian := isHermitian X
  have hnorm_trace : ‖X‖ ^ (2 : ℕ) = Matrix.trace ((X : Mat) * (X : Mat)) := by
    -- Rewrite the Frobenius norm square as the Frobenius self-pairing, then expand that pairing
    -- as the ambient trace of `Xᵀ X`.
    calc
      ‖X‖ ^ (2 : ℕ) = inner ℝ X X := by
        simp
      _ = ⟪X, X⟫_F := rfl
      _ = Matrix.trace (((X : Mat)ᵀ) * (X : Mat)) := by
        rw [RealSymmetricMatrixSpace.frobeniusInner_def]
      _ = Matrix.trace ((X : Mat) * (X : Mat)) := by
        simp [show ((X : Mat)ᵀ) = (X : Mat) by simpa [Matrix.IsSymm] using (isSymm X).eq]
  have hdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star e)) (X : Mat) =
        Matrix.diagonal (eigenvalues X) := by
    -- Diagonalize `X` in its orthonormal eigenbasis.
    simpa using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hsq_diag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star e)) ((X : Mat) * (X : Mat)) =
        Matrix.diagonal (fun i : Fin n ↦ (eigenvalues X i) ^ (2 : ℕ)) := by
    -- After conjugating by the eigenbasis, `X²` becomes the diagonal matrix of squared
    -- eigenvalues.
    calc
      ((Unitary.conjStarAlgAut ℝ Mat) (star e)) ((X : Mat) * (X : Mat)) =
          (((Unitary.conjStarAlgAut ℝ Mat) (star e)) (X : Mat)) *
            (((Unitary.conjStarAlgAut ℝ Mat) (star e)) (X : Mat)) := by
            simpa using
              map_mul ((Unitary.conjStarAlgAut ℝ Mat) (star e)) (X : Mat) (X : Mat)
      _ = Matrix.diagonal (eigenvalues X) * Matrix.diagonal (eigenvalues X) := by
            rw [hdiag]
      _ = Matrix.diagonal (fun i : Fin n ↦ (eigenvalues X i) ^ (2 : ℕ)) := by
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [pow_two]
            · simp [hij]
  -- Trace is invariant under conjugation, so the diagonal form computes the same Frobenius norm.
  calc
    ‖X‖ ^ (2 : ℕ) = Matrix.trace ((X : Mat) * (X : Mat)) := hnorm_trace
    _ = Matrix.trace (((Unitary.conjStarAlgAut ℝ Mat) (star e)) ((X : Mat) * (X : Mat))) := by
          symm
          exact Matrix.trace_map ((Unitary.conjStarAlgAut ℝ Mat) (star e)) ((X : Mat) * (X : Mat))
    _ = Matrix.trace (Matrix.diagonal (fun i : Fin n ↦ (eigenvalues X i) ^ (2 : ℕ))) := by
          rw [hsq_diag]
    _ = ∑ i : Fin n, (eigenvalues X i) ^ (2 : ℕ) := by
          simp

/-- Helper for Lemma 7.3: tracing the Hermitian functional calculus of a symmetric matrix applies
the scalar function to the ordered eigenvalues and sums the result. -/
theorem trace_cfc_eq_sum_map_eigenvalues
    (X : SymmMat) (f : ℝ → ℝ) :
    Matrix.trace ((isHermitian X).cfc f) = ∑ i : Fin n, f (eigenvalues X i) := by
  let hX : (X : Mat).IsHermitian := isHermitian X
  -- Rewrite the matrix functional calculus into the diagonal eigenbasis model.
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  -- Cycling the trace exposes the unitary cancellation and leaves the diagonal eigenvalue term.
  have hunitary :
      star (hX.eigenvectorUnitary : Mat) * (hX.eigenvectorUnitary : Mat) = (1 : Mat) := by
    simpa using hX.eigenvectorUnitary.star_mul_self
  rw [show star (hX.eigenvectorUnitary : Mat) * (hX.eigenvectorUnitary : Mat) = (1 : Mat)
      by exact hunitary, one_mul, Matrix.trace_diagonal]
  simpa [Function.comp]

/-- Helper for Lemma 7.3: the trace of the source-facing matrix absolute value is the `ℓ₁` sum
of the ordered eigenvalues. -/
theorem trace_abs_eq_eigenvalue_l1
    (U : SymmMat) :
    Matrix.trace (((|U| : SymmMat) : Mat)) = ∑ i : Fin n, |eigenvalues U i| := by
  -- Route correction: rewrite the ambient `cfc abs` formula immediately into the source-facing
  -- absolute-value owner, so later proofs can stay in the textbook `|U|` language.
  have hself : IsSelfAdjoint (U : Mat) := by
    -- Convert the symmetric-matrix Hermitian structure into the ambient star-self-adjointness
    -- hypothesis required by `CFC.abs_eq_cfc_norm`.
    simpa [Matrix.isHermitian_iff_isSelfAdjoint] using isHermitian U
  rw [RealSymmetricMatrixSpace.coe_abs,
    CFC.abs_eq_cfc_norm (U : Mat) (ha := hself),
    (isHermitian U).cfc_eq]
  simpa using trace_cfc_eq_sum_map_eigenvalues (n := n) U (fun x : ℝ ↦ ‖x‖)

/-- Helper for Lemma 7.3: the positive part of a symmetric matrix is again a symmetric matrix. -/
private theorem posPart_mem_symm
    (U : SymmMat) :
    (((U : Mat)⁺ : Mat)) ∈ 𝕊^n := by
  -- Positive semidefinite matrices are Hermitian, hence symmetric over `ℝ`.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg (U : Mat))).isHermitian

/-- Helper for Lemma 7.3: the negative part of a symmetric matrix is again a symmetric matrix. -/
private theorem negPart_mem_symm
    (U : SymmMat) :
    (((U : Mat)⁻ : Mat)) ∈ 𝕊^n := by
  -- The same Hermitian-to-symmetric bridge packages the negative part back into `𝕊^n`.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg (U : Mat))).isHermitian

/-- Helper for Lemma 7.3: the positive and negative parts of `U` give the source-faithful
positive-semidefinite split, and their traces add up to `trace |U|`. -/
theorem pos_neg_parts_trace_abs_decomposition
    (U : SymmMat) :
    ∃ P N : SymmMat,
      (P : Mat).PosSemidef ∧ (N : Mat).PosSemidef ∧ U = P - N ∧
      Matrix.trace (P : Mat) + Matrix.trace (N : Mat) =
        Matrix.trace (((|U| : SymmMat) : Mat)) := by
  let P : SymmMat := ⟨(U : Mat)⁺, posPart_mem_symm (n := n) U⟩
  let N : SymmMat := ⟨(U : Mat)⁻, negPart_mem_symm (n := n) U⟩
  have hself : IsSelfAdjoint (U : Mat) := by
    -- The CFC positive/negative-part identities are stated for self-adjoint matrices.
    simpa [Matrix.isHermitian_iff_isSelfAdjoint] using isHermitian U
  have hPpsd : (P : Mat).PosSemidef := by
    -- The positive part is positive semidefinite by construction.
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg (U : Mat))
  have hNpsd : (N : Mat).PosSemidef := by
    -- The negative part is positive semidefinite as well.
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg (U : Mat))
  have hsub : U = P - N := by
    -- The Jordan decomposition `U = U⁺ - U⁻` becomes the desired split in `𝕊^n`.
    ext i j
    simpa [P, N] using congrArg (fun M : Mat => M i j)
      (CFC.posPart_sub_negPart (U : Mat) (ha := hself)).symm
  have htrace :
      Matrix.trace (P : Mat) + Matrix.trace (N : Mat) =
        Matrix.trace (((|U| : SymmMat) : Mat)) := by
    -- The textbook identity `|U| = U⁺ + U⁻` transfers directly to the trace budget.
    calc
      Matrix.trace (P : Mat) + Matrix.trace (N : Mat)
          = Matrix.trace ((P : Mat) + (N : Mat)) := by
              rw [Matrix.trace_add]
      _ = Matrix.trace (((|U| : SymmMat) : Mat)) := by
            simpa [P, N, RealSymmetricMatrixSpace.coe_abs] using
              congrArg Matrix.trace (CFC.posPart_add_negPart (U : Mat) (ha := hself))
  exact ⟨P, N, hPpsd, hNpsd, hsub, htrace⟩

/-- Helper for Lemma 7.3: every point of `Q₂` admits a positive-semidefinite split whose total
trace budget is at most `1`. -/
theorem exists_psd_trace_split_of_mem_spectral_eigenvalue_l1_unit_ball
    {U : SymmMat} (hU : U ∈ spectral_eigenvalue_l1_unit_ball n) :
    ∃ P N : SymmMat,
      (P : Mat).PosSemidef ∧ (N : Mat).PosSemidef ∧ U = P - N ∧
      Matrix.trace (P : Mat) + Matrix.trace (N : Mat) ≤ 1 := by
  rw [mem_spectral_eigenvalue_l1_unit_ball_iff] at hU
  rcases pos_neg_parts_trace_abs_decomposition (n := n) U with
    ⟨P, N, hP, hN, hsub, htrace⟩
  refine ⟨P, N, hP, hN, hsub, ?_⟩
  -- The split from the positive/negative parts inherits the defining `ℓ₁` trace budget of `Q₂`.
  calc
    Matrix.trace (P : Mat) + Matrix.trace (N : Mat)
        = Matrix.trace (((|U| : SymmMat) : Mat)) := htrace
    _ = ∑ i : Fin n, |eigenvalues U i| := trace_abs_eq_eigenvalue_l1 (n := n) U
    _ ≤ 1 := hU

/-- Helper for Lemma 7.3: once the source-facing matrix absolute value is dominated by a slack
matrix, the positive trace map turns that order bound into the required trace inequality. -/
theorem trace_abs_le_trace_add_of_abs_bound
    {U P N : SymmMat}
    (hbound : (((|U| : SymmMat) : Mat) ≤ (P : Mat) + (N : Mat))) :
    Matrix.trace (((|U| : SymmMat) : Mat)) ≤ Matrix.trace (P : Mat) + Matrix.trace (N : Mat) := by
  -- Route correction: isolate the trace step from the harder matrix-order step. Once `|U|` is
  -- bounded by the total PSD slack, trace monotonicity closes the source's converse budget bound.
  calc
    Matrix.trace (((|U| : SymmMat) : Mat))
        ≤ Matrix.trace ((P : Mat) + (N : Mat)) := by
            -- The ambient trace is already packaged as a positive linear map, so it preserves the
            -- matrix order on Hermitian matrices.
            exact (Matrix.tracePositiveLinearMap (Fin n) ℝ ℝ).monotone' hbound
    _ = Matrix.trace (P : Mat) + Matrix.trace (N : Mat) := by
          rw [Matrix.trace_add]

/-- Helper for Lemma 7.3: any positive-semidefinite split `U = P - N` dominates the eigenvalue
`ℓ₁` budget of `U` by the total trace budget `trace P + trace N`. -/
theorem trace_abs_le_trace_add_of_psd_split
    {U P N : SymmMat}
    (hP : (P : Mat).PosSemidef) (hN : (N : Mat).PosSemidef) (hsub : U = P - N) :
    Matrix.trace (((|U| : SymmMat) : Mat)) ≤ Matrix.trace (P : Mat) + Matrix.trace (N : Mat) := by
  let e := (isHermitian U).eigenvectorUnitary
  let A : Mat := star (e : Mat) * (P : Mat) * (e : Mat)
  let B : Mat := star (e : Mat) * (N : Mat) * (e : Mat)
  have hdiag : star (e : Mat) * (U : Mat) * (e : Mat) = Matrix.diagonal (eigenvalues U) := by
    -- Diagonalize `U` in its orthonormal eigenbasis so the split comparison reduces to scalar
    -- inequalities on diagonal entries.
    simpa [Unitary.conjStarAlgAut_apply, e] using
      (isHermitian U).conjStarAlgAut_star_eigenvectorUnitary
  have hApsd : A.PosSemidef := by
    -- Conjugating a positive-semidefinite matrix by the eigenbasis stays positive semidefinite.
    simpa [A, e] using Matrix.PosSemidef.conjTranspose_mul_mul_same hP (e : Mat)
  have hBpsd : B.PosSemidef := by
    -- The same conjugation preserves positivity for the negative slack.
    simpa [B, e] using Matrix.PosSemidef.conjTranspose_mul_mul_same hN (e : Mat)
  have hdiag_sub : Matrix.diagonal (eigenvalues U) = A - B := by
    -- Transport the split `U = P - N` into the eigenbasis of `U`.
    calc
      Matrix.diagonal (eigenvalues U) = star (e : Mat) * (U : Mat) * (e : Mat) := hdiag.symm
      _ = star (e : Mat) * (((P : Mat) - (N : Mat)) * (e : Mat)) := by
            simpa [hsub, Matrix.mul_assoc]
      _ = star (e : Mat) * ((P : Mat) * (e : Mat)) - star (e : Mat) * ((N : Mat) * (e : Mat)) := by
            rw [Matrix.sub_mul, Matrix.mul_sub]
      _ = A - B := by
            simp [A, B, Matrix.mul_assoc]
  have hdiag_entries (i : Fin n) : eigenvalues U i = A i i - B i i := by
    -- Each eigenvalue is the difference of two nonnegative diagonal entries.
    simpa [A, B] using congrArg (fun M : Mat => M i i) hdiag_sub
  have hentry_bound (i : Fin n) : |eigenvalues U i| ≤ A i i + B i i := by
    have hAi : 0 ≤ A i i := Matrix.PosSemidef.diag_nonneg hApsd
    have hBi : 0 ≤ B i i := Matrix.PosSemidef.diag_nonneg hBpsd
    -- Take absolute values entrywise and use that both conjugated slacks have nonnegative
    -- diagonal entries.
    calc
      |eigenvalues U i| = |A i i - B i i| := by
        rw [hdiag_entries i]
      _ ≤ |A i i| + |B i i| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (A i i) (-B i i)
      _ = A i i + B i i := by
        rw [abs_of_nonneg hAi, abs_of_nonneg hBi]
  have hunitary : (e : Mat) * star (e : Mat) = (1 : Mat) := by
    -- The eigenbasis matrix is unitary, so cycling the trace removes it.
    simpa [e] using
      (show ((isHermitian U).eigenvectorUnitary : Mat) *
          star (((isHermitian U).eigenvectorUnitary : Mat)) = (1 : Mat) from
        (isHermitian U).eigenvectorUnitary.mul_star_self)
  have htraceA : Matrix.trace A = Matrix.trace (P : Mat) := by
    -- Trace is invariant under the unitary conjugation defining `A`.
    simpa [A, Matrix.mul_assoc, hunitary] using
      Matrix.trace_mul_cycle (star (e : Mat)) (P : Mat) (e : Mat)
  have htraceB : Matrix.trace B = Matrix.trace (N : Mat) := by
    -- And likewise for `B`.
    simpa [B, Matrix.mul_assoc, hunitary] using
      Matrix.trace_mul_cycle (star (e : Mat)) (N : Mat) (e : Mat)
  -- Summing the scalar bounds in the eigenbasis gives the trace budget bound.
  calc
    Matrix.trace (((|U| : SymmMat) : Mat)) = ∑ i : Fin n, |eigenvalues U i| :=
      trace_abs_eq_eigenvalue_l1 (n := n) U
    _ ≤ ∑ i : Fin n, (A i i + B i i) := by
          exact Finset.sum_le_sum fun i _ ↦ hentry_bound i
    _ = Matrix.trace A + Matrix.trace B := by
          simp [Matrix.trace, Finset.sum_add_distrib]
    _ = Matrix.trace (P : Mat) + Matrix.trace (N : Mat) := by
          rw [htraceA, htraceB]

/-- Helper for Lemma 7.3: `U ∈ Q₂` exactly when it admits a positive-semidefinite split whose
total trace budget is at most `1`. -/
theorem mem_spectral_eigenvalue_l1_unit_ball_iff_exists_psd_trace_split
    (U : SymmMat) :
    U ∈ spectral_eigenvalue_l1_unit_ball n ↔
      ∃ P N : SymmMat,
        (P : Mat).PosSemidef ∧ (N : Mat).PosSemidef ∧ U = P - N ∧
        Matrix.trace (P : Mat) + Matrix.trace (N : Mat) ≤ 1 := by
  constructor
  · -- The positive/negative-part decomposition supplies the source-faithful PSD split.
    exact exists_psd_trace_split_of_mem_spectral_eigenvalue_l1_unit_ball (n := n)
  · rintro ⟨P, N, hP, hN, hsub, hbudget⟩
    rw [mem_spectral_eigenvalue_l1_unit_ball_iff]
    -- The converse direction is exactly the eigenbasis trace bound for arbitrary PSD splits.
    calc
      ∑ i : Fin n, |eigenvalues U i| = Matrix.trace (((|U| : SymmMat) : Mat)) := by
            symm
            exact trace_abs_eq_eigenvalue_l1 (n := n) U
      _ ≤ Matrix.trace (P : Mat) + Matrix.trace (N : Mat) :=
            trace_abs_le_trace_add_of_psd_split (n := n) hP hN hsub
      _ ≤ 1 := hbudget

/-- Helper for Lemma 7.3: a positive-semidefinite symmetric matrix with trace at most `1`
already lies in `Q₂`. -/
theorem mem_spectral_eigenvalue_l1_unit_ball_of_posSemidef_trace_le_one
    {P : SymmMat}
    (hP : (P : Mat).PosSemidef) (htrace : Matrix.trace (P : Mat) ≤ 1) :
    P ∈ spectral_eigenvalue_l1_unit_ball n := by
  rw [mem_spectral_eigenvalue_l1_unit_ball_iff]
  have hPnonneg : (0 : Mat) ≤ (P : Mat) := Matrix.nonneg_iff_posSemidef.mpr hP
  have habs : (((|P| : SymmMat) : Mat)) = (P : Mat) := by
    -- For positive-semidefinite matrices, the source absolute value is the matrix itself.
    rw [RealSymmetricMatrixSpace.coe_abs]
    simpa using CFC.abs_of_nonneg ((P : Mat)) (ha := hPnonneg)
  -- Rewrite the eigenvalue `ℓ₁` sum as the trace of `|P|`, then simplify with positivity.
  calc
    ∑ i : Fin n, |eigenvalues P i| = Matrix.trace (((|P| : SymmMat) : Mat)) := by
          symm
          exact trace_abs_eq_eigenvalue_l1 (n := n) P
    _ = Matrix.trace (P : Mat) := by
          rw [habs]
    _ ≤ 1 := htrace

/-- Helper for Lemma 7.3: a positive-semidefinite symmetric matrix has Frobenius norm bounded by
its trace. -/
theorem frobeniusNorm_le_trace_of_posSemidef
    {P : SymmMat}
    (hP : (P : Mat).PosSemidef) :
    ‖P‖ ≤ Matrix.trace (P : Mat) := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, eigenvalues P i := by
    exact Finset.sum_nonneg fun i _ ↦ hP.eigenvalues_nonneg i
  have hsum_sq_le :
      ∑ i : Fin n, (eigenvalues P i) ^ (2 : ℕ) ≤
        (∑ i : Fin n, eigenvalues P i) ^ (2 : ℕ) := by
    -- Every nonnegative eigenvalue is bounded by the total trace budget, so the `ℓ₂` square is
    -- controlled by the square of the `ℓ₁` sum.
    calc
      ∑ i : Fin n, (eigenvalues P i) ^ (2 : ℕ) =
          ∑ i : Fin n, eigenvalues P i * eigenvalues P i := by
            simp [pow_two]
      _ ≤ ∑ i : Fin n, eigenvalues P i * ∑ j : Fin n, eigenvalues P j := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun j _ ↦ hP.eigenvalues_nonneg j) (Finset.mem_univ i))
              (hP.eigenvalues_nonneg i)
      _ = (∑ i : Fin n, eigenvalues P i) ^ (2 : ℕ) := by
            simp [pow_two, Finset.sum_mul]
  have htrace_eq :
      Matrix.trace (P : Mat) = ∑ i : Fin n, eigenvalues P i := by
    simpa using (isHermitian P).trace_eq_sum_eigenvalues
  have hnorm_sq :
      ‖P‖ ^ (2 : ℕ) ≤ (Matrix.trace (P : Mat)) ^ (2 : ℕ) := by
    rw [frobenius_norm_sq_eq_sum_eigenvalues_sq (n := n) P, htrace_eq]
    exact hsum_sq_le
  have htrace_nonneg : 0 ≤ Matrix.trace (P : Mat) := Matrix.PosSemidef.trace_nonneg hP
  -- Taking square roots is safe because both sides are nonnegative.
  nlinarith [hnorm_sq, norm_nonneg P, htrace_nonneg]

/-- Helper for Lemma 7.3: the PSD split-budget set used to package `Q₂` as a subtraction image. -/
def psdSplitTraceBudget : Set (SymmMat × SymmMat) :=
  {z |
    (z.1 : Mat).PosSemidef ∧
      (z.2 : Mat).PosSemidef ∧
        Matrix.trace (z.1 : Mat) + Matrix.trace (z.2 : Mat) ≤ 1}

/-- Helper for Lemma 7.3: the PSD split-budget set is the intersection of the two PSD-cone
preimages and the trace-budget halfspace. -/
theorem psdSplitTraceBudget_eq_ownerInter :
    psdSplitTraceBudget (n := n) =
      (Prod.fst ⁻¹' (𝕊^n₊ : Set SymmMat)) ∩
        ((Prod.snd ⁻¹' (𝕊^n₊ : Set SymmMat)) ∩
          {z |
            Matrix.trace (z.1 : Mat) + Matrix.trace (z.2 : Mat) ≤ 1}) := by
  -- Unfold the owner membership once so later set-topology proofs can stay on the owner level.
  ext z
  simp [psdSplitTraceBudget, Set.mem_preimage, Set.mem_inter_iff,
    mem_positiveSemidefiniteCone_iff, and_left_comm, and_assoc]

/-- Helper for Lemma 7.3: the PSD split-budget set is closed. -/
theorem isClosed_psdSplitTraceBudget :
    IsClosed (psdSplitTraceBudget (n := n)) := by
  have htrace_cont : Continuous fun X : SymmMat => Matrix.trace (X : Mat) := by
    -- The trace is linear on matrices, so it stays continuous after restricting to `𝕊^n`.
    simpa using
      (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional.comp
        continuous_subtype_val
  let traceSum : SymmMat × SymmMat → ℝ :=
    fun z => Matrix.trace (z.1 : Mat) + Matrix.trace (z.2 : Mat)
  have htraceSum_cont : Continuous traceSum := by
    -- The product trace budget is the sum of the two continuous trace coordinates.
    exact (htrace_cont.comp continuous_fst).add (htrace_cont.comp continuous_snd)
  have htraceSum_closed :
      IsClosed {z | traceSum z ≤ 1} := by
    -- The trace-budget constraint is a closed halfspace in the product space.
    exact isClosed_le htraceSum_cont continuous_const
  -- Route correction: rewrite the raw set-builder into owner-level preimages before applying the
  -- closedness of `𝕊^n₊`.
  rw [psdSplitTraceBudget_eq_ownerInter (n := n)]
  exact (positiveSemidefiniteCone_isClosed n).preimage continuous_fst |>.inter
    (((positiveSemidefiniteCone_isClosed n).preimage continuous_snd).inter htraceSum_closed)

/-- Helper for Lemma 7.3: every PSD split-budget point lies in the product of the Frobenius
closed unit balls. -/
theorem psdSplitTraceBudget_subset_closedBallProd :
    psdSplitTraceBudget (n := n) ⊆
      (Metric.closedBall (0 : SymmMat) 1 ×ˢ Metric.closedBall (0 : SymmMat) 1) := by
  intro z hz
  rcases hz with ⟨hP, hN, hbudget⟩
  have htraceP_nonneg : 0 ≤ Matrix.trace (z.1 : Mat) := Matrix.PosSemidef.trace_nonneg hP
  have htraceN_nonneg : 0 ≤ Matrix.trace (z.2 : Mat) := Matrix.PosSemidef.trace_nonneg hN
  have htraceP_le : Matrix.trace (z.1 : Mat) ≤ 1 := by
    nlinarith
  have htraceN_le : Matrix.trace (z.2 : Mat) ≤ 1 := by
    nlinarith
  have hnormP : ‖z.1‖ ≤ 1 := (frobeniusNorm_le_trace_of_posSemidef (n := n) hP).trans htraceP_le
  have hnormN : ‖z.2‖ ≤ 1 := (frobeniusNorm_le_trace_of_posSemidef (n := n) hN).trans htraceN_le
  constructor
  · -- The first PSD component lies in the Frobenius unit ball via the trace bound.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnormP
  · -- The second PSD component obeys the same Frobenius bound.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnormN

/-- Helper for Lemma 7.3: `Q₂` is exactly the image of the PSD split-budget set under
subtraction. -/
theorem q2_eq_image_psdSplitTraceBudget
    :
    spectral_eigenvalue_l1_unit_ball n =
      (fun z : SymmMat × SymmMat ↦ z.1 - z.2) '' psdSplitTraceBudget (n := n) := by
  ext U
  constructor
  · intro hU
    rcases (mem_spectral_eigenvalue_l1_unit_ball_iff_exists_psd_trace_split (n := n) U).mp hU with
      ⟨P, N, hP, hN, hsub, hbudget⟩
    refine ⟨(P, N), ?_, ?_⟩
    · exact ⟨hP, hN, hbudget⟩
    · simpa [hsub]
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨hP, hN, hbudget⟩
    exact
      (mem_spectral_eigenvalue_l1_unit_ball_iff_exists_psd_trace_split (n := n) (z.1 - z.2)).2
        ⟨z.1, z.2, hP, hN, rfl, hbudget⟩

/-- Helper for Lemma 7.3: the `i`-th diagonal coordinate projector matrix. -/
private def coordinateProjectorMat
    (i : Fin n) : Mat :=
  Matrix.diagonal (Pi.single i (1 : ℝ))

/-- Helper for Lemma 7.3: the diagonal coordinate projector belongs to the symmetric carrier. -/
private theorem coordinateProjectorMat_mem_symm
    (i : Fin n) :
    coordinateProjectorMat (n := n) i ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
  ext j k
  by_cases hjk : j = k
  · subst hjk
    simp [coordinateProjectorMat]
  · simp [coordinateProjectorMat, hjk, eq_comm]

/-- Helper for Lemma 7.3: the `i`-th coordinate projector viewed inside `𝕊^n`. -/
private def coordinateProjector
    (i : Fin n) : SymmMat :=
  ⟨coordinateProjectorMat (n := n) i, coordinateProjectorMat_mem_symm (n := n) i⟩

/-- Helper for Lemma 7.3: coercing the coordinate projector back to matrices gives the canonical
single-entry diagonal matrix. -/
private theorem coordinateProjector_eq_diagonal_single
    (i : Fin n) :
    (((coordinateProjector (n := n) i : SymmMat) : Mat)) =
      Matrix.diagonal (Pi.single i (1 : ℝ)) := by
  -- The intrinsic projector was defined from this diagonal matrix, so the coercion is exact.
  rfl

/-- Helper for Lemma 7.3: the coordinate projector is positive semidefinite. -/
private theorem coordinateProjector_posSemidef
    (i : Fin n) :
    (((coordinateProjector (n := n) i : SymmMat) : Mat)).PosSemidef := by
  -- Route correction: normalize the projector coercion once, then use the diagonal PSD criterion.
  rw [coordinateProjector_eq_diagonal_single (n := n) i]
  exact Matrix.PosSemidef.diagonal <| by
    intro j
    by_cases hji : j = i
    · simp [Pi.single_apply, hji]
    · simp [Pi.single_apply, hji]

/-- Helper for Lemma 7.3: the coordinate projector has trace `1`. -/
private theorem coordinateProjector_trace_eq_one
    (i : Fin n) :
    Matrix.trace (((coordinateProjector (n := n) i : SymmMat) : Mat)) = 1 := by
  simp [coordinateProjector, coordinateProjectorMat]

/-- Helper for Lemma 7.3: tracing a diagonal matrix against the `i`-th coordinate projector picks
out the `i`-th diagonal entry. -/
private theorem trace_diagonal_mul_coordinateProjectorMat
    (f : Fin n → ℝ) (i : Fin n) :
    Matrix.trace (Matrix.diagonal f * coordinateProjectorMat (n := n) i) = f i := by
  -- The product stays diagonal, and only the `i`-th single entry survives in the trace.
  rw [coordinateProjectorMat, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

/-- Helper for Lemma 7.3: conjugating the coordinate projector by the eigenbasis of `X` stays in
the symmetric carrier. -/
private theorem eigenProjector_mem_symm
    (X : SymmMat) (i : Fin n) :
    (((isHermitian X).eigenvectorUnitary : Mat) *
        (((coordinateProjector (n := n) i : SymmMat) : Mat)) *
        star (((isHermitian X).eigenvectorUnitary : Mat))) ∈ 𝕊^n := by
  have hpsd :
      ((((isHermitian X).eigenvectorUnitary : Mat) *
          (((coordinateProjector (n := n) i : SymmMat) : Mat)) *
          star (((isHermitian X).eigenvectorUnitary : Mat))) : Mat).PosSemidef := by
    simpa using
      (coordinateProjector_posSemidef (n := n) i).mul_mul_conjTranspose_same
        (((isHermitian X).eigenvectorUnitary : Mat))
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using hpsd.isHermitian

/-- Helper for Lemma 7.3: the projector onto the `i`-th eigendirection of `X`. -/
private def eigenProjector
    (X : SymmMat) (i : Fin n) : SymmMat :=
  ⟨((isHermitian X).eigenvectorUnitary : Mat) *
      (((coordinateProjector (n := n) i : SymmMat) : Mat)) *
      star (((isHermitian X).eigenvectorUnitary : Mat)),
    eigenProjector_mem_symm (n := n) X i⟩

/-- Helper for Lemma 7.3: the eigenspace projector is positive semidefinite. -/
private theorem eigenProjector_posSemidef
    (X : SymmMat) (i : Fin n) :
    (((eigenProjector (n := n) X i : SymmMat) : Mat)).PosSemidef := by
  simpa [eigenProjector] using
    (coordinateProjector_posSemidef (n := n) i).mul_mul_conjTranspose_same
      (((isHermitian X).eigenvectorUnitary : Mat))

/-- Helper for Lemma 7.3: the eigenspace projector has unit trace. -/
private theorem eigenProjector_trace_eq_one
    (X : SymmMat) (i : Fin n) :
    Matrix.trace (((eigenProjector (n := n) X i : SymmMat) : Mat)) = 1 := by
  let e := (isHermitian X).eigenvectorUnitary
  have hstar_mul : star (e : Mat) * (e : Mat) = (1 : Mat) := by
    simpa [e] using
      (show
        star (((isHermitian X).eigenvectorUnitary : Mat)) *
            (((isHermitian X).eigenvectorUnitary : Mat)) = (1 : Mat) from
          (isHermitian X).eigenvectorUnitary.star_mul_self)
  -- Cycle the trace once to cancel the unitary change of basis.
  calc
    Matrix.trace (((eigenProjector (n := n) X i : SymmMat) : Mat))
        = Matrix.trace
            ((e : Mat) * (((coordinateProjector (n := n) i : SymmMat) : Mat)) *
              star (e : Mat)) := by
              rfl
    _ = Matrix.trace
          (star (e : Mat) * (e : Mat) *
            (((coordinateProjector (n := n) i : SymmMat) : Mat))) := by
            simpa [Matrix.mul_assoc] using
              Matrix.trace_mul_cycle
                (e : Mat)
                (((coordinateProjector (n := n) i : SymmMat) : Mat))
                (star (e : Mat))
    _ = Matrix.trace (((coordinateProjector (n := n) i : SymmMat) : Mat)) := by
          simp [Matrix.mul_assoc, hstar_mul]
    _ = 1 := coordinateProjector_trace_eq_one (n := n) i

/-- Helper for Lemma 7.3: pairing `X` with its `i`-th eigenspace projector recovers the
`i`-th eigenvalue. -/
private theorem trace_mul_eigenProjector_eq_eigenvalue
    (X : SymmMat) (i : Fin n) :
    Matrix.trace ((X : Mat) * (((eigenProjector (n := n) X i : SymmMat) : Mat))) =
      eigenvalues X i := by
  let e := (isHermitian X).eigenvectorUnitary
  have hdiag :
      star (e : Mat) * (X : Mat) * (e : Mat) = Matrix.diagonal (eigenvalues X) := by
    -- Diagonalize `X` in its orthonormal eigenbasis.
    simpa [Unitary.conjStarAlgAut_apply, e] using
      (isHermitian X).conjStarAlgAut_star_eigenvectorUnitary
  -- Cycle the trace into the eigenbasis of `X`, then evaluate the diagonal-single projector term.
  calc
    Matrix.trace ((X : Mat) * (((eigenProjector (n := n) X i : SymmMat) : Mat)))
        = Matrix.trace
            (((X : Mat) * (e : Mat)) *
              (((coordinateProjector (n := n) i : SymmMat) : Mat)) * star (e : Mat)) := by
              simp [eigenProjector, e, Matrix.mul_assoc]
    _ = Matrix.trace
          (star (e : Mat) * ((X : Mat) * (e : Mat)) *
            (((coordinateProjector (n := n) i : SymmMat) : Mat))) := by
            simpa [Matrix.mul_assoc] using
              Matrix.trace_mul_cycle
                ((X : Mat) * (e : Mat))
                (((coordinateProjector (n := n) i : SymmMat) : Mat))
                (star (e : Mat))
    _ = Matrix.trace
          ((star (e : Mat) * (X : Mat) * (e : Mat)) *
            (((coordinateProjector (n := n) i : SymmMat) : Mat))) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace
          (Matrix.diagonal (eigenvalues X) * Matrix.diagonal (Pi.single i (1 : ℝ))) := by
          rw [hdiag, coordinateProjector_eq_diagonal_single]
    _ = eigenvalues X i := by
          simpa [coordinateProjectorMat] using
            trace_diagonal_mul_coordinateProjectorMat (n := n) (eigenvalues X) i

/-- Helper for Lemma 7.3: the spectral radius gives the canonical semidefinite slacks
`ρ(X) I - X` and `ρ(X) I + X`. -/
private theorem spectralRadius_sub_add_posSemidef
    (X : SymmMat) :
    (ρ(X) • (1 : Mat) - (X : Mat)).PosSemidef ∧
      (ρ(X) • (1 : Mat) + (X : Mat)).PosSemidef := by
  let A : Mat := (X : Mat)
  have hSelfAdjoint : IsSelfAdjoint A := by
    simpa [A, Matrix.IsSelfAdjoint, Matrix.IsHermitian, Matrix.IsSymm] using
      RealSymmetricMatrixSpace.isHermitian X
  have hSpectrumEq :
      spectrum ℝ A = Set.range (RealSymmetricMatrixSpace.eigenvalues X) := by
    -- Real spectral points of a symmetric matrix are exactly its ordered eigenvalues.
    simpa [A, RealSymmetricMatrixSpace.eigenvalues] using
      (RealSymmetricMatrixSpace.isHermitian X).spectrum_real_eq_range_eigenvalues
  have hSpectrumAbsLe : ∀ x ∈ spectrum ℝ A, |x| ≤ ρ(X) := by
    intro x hx
    rw [hSpectrumEq] at hx
    rcases hx with ⟨i, rfl⟩
    rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
    exact Finite.le_ciSup (fun j : Fin n ↦ |RealSymmetricMatrixSpace.eigenvalues X j|) i
  have hLower : -(ρ(X) • (1 : Mat)) ≤ A := by
    have hLower' : algebraMap ℝ Mat (-ρ(X)) ≤ A :=
      algebraMap_le_of_le_spectrum
        (a := A) (r := -ρ(X))
        (ha := hSelfAdjoint)
        (fun x hx ↦ (abs_le.mp (hSpectrumAbsLe x hx)).1)
    simpa [A, Algebra.algebraMap_eq_smul_one] using hLower'
  have hUpper : A ≤ ρ(X) • (1 : Mat) := by
    have hUpper' : A ≤ algebraMap ℝ Mat (ρ(X)) :=
      le_algebraMap_of_spectrum_le
        (a := A) (r := ρ(X))
        (ha := hSelfAdjoint)
        (fun x hx ↦ (abs_le.mp (hSpectrumAbsLe x hx)).2)
    simpa [A, Algebra.algebraMap_eq_smul_one] using hUpper'
  constructor
  · exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hUpper)
  · have hAddNonneg : 0 ≤ ρ(X) • (1 : Mat) + A := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_nonneg.mpr hLower
    exact (Matrix.nonneg_iff_posSemidef).mp hAddNonneg

/-- Helper for Lemma 7.3: the trace pairing of two positive-semidefinite matrices is
nonnegative. -/
private theorem trace_mul_nonneg_of_posSemidef
    {A B : Mat}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  have hsqrt_symm : (CFC.sqrt A).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hsqrt_transpose : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    simpa [Matrix.IsSymm] using hsqrt_symm
  have hpsd :
      (CFC.sqrt A * B * (CFC.sqrt A)ᵀ).PosSemidef := by
    exact hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  have htrace_nonneg :
      0 ≤ Matrix.trace (CFC.sqrt A * B * (CFC.sqrt A)ᵀ) :=
    Matrix.PosSemidef.trace_nonneg hpsd
  -- Rewrite `trace (AB)` as the trace of a visibly PSD conjugate.
  calc
    0 ≤ Matrix.trace (CFC.sqrt A * B * (CFC.sqrt A)ᵀ) := htrace_nonneg
    _ = Matrix.trace (CFC.sqrt A * CFC.sqrt A * B) := by
          simpa [hsqrt_transpose, Matrix.mul_assoc] using
            Matrix.trace_mul_cycle (CFC.sqrt A) B (CFC.sqrt A)
    _ = Matrix.trace (A * B) := by
          rw [CFC.sqrt_mul_sqrt_self _ hA.nonneg]

/-- Helper for Lemma 7.3: coercing the symmetric-matrix difference to matrices gives the ambient
matrix difference. -/
@[simp] private theorem coe_sub_symmMat
    (P N : SymmMat) :
    ((P - N : SymmMat) : Mat) = (P : Mat) - (N : Mat) := by
  -- The additive structure on `𝕊^n` is inherited from the ambient matrix space.
  rfl

/-- Helper for Lemma 7.3: any PSD split representation of `U ∈ Q₂` gives the trace upper bound
`trace (XU) ≤ ρ(X)`. -/
theorem trace_pairing_le_spectralRadius_of_psdSplit
    {X U P N : SymmMat}
    (hP : (P : Mat).PosSemidef) (hN : (N : Mat).PosSemidef)
    (hsub : U = P - N)
    (hbudget : Matrix.trace (P : Mat) + Matrix.trace (N : Mat) ≤ 1) :
    Matrix.trace ((X : Mat) * (U : Mat)) ≤ ρ(X) := by
  rcases spectralRadius_sub_add_posSemidef (n := n) X with ⟨hminus, hplus⟩
  have hρ_nonneg : 0 ≤ ρ(X) := by
    -- The spectral radius is the supremum of absolute eigenvalues, hence nonnegative.
    rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
    exact Real.iSup_nonneg fun i ↦ abs_nonneg _
  have htraceScalarP :
      Matrix.trace ((ρ(X) • (1 : Mat)) * (P : Mat)) = ρ(X) * Matrix.trace (P : Mat) := by
    -- Multiplying by the scalar identity matrix scales the trace by `ρ(X)`.
    calc
      Matrix.trace ((ρ(X) • (1 : Mat)) * (P : Mat))
          = Matrix.trace (ρ(X) • ((1 : Mat) * (P : Mat))) := by
              rw [smul_mul_assoc]
      _ = ρ(X) * Matrix.trace (P : Mat) := by
            simp
  have htraceScalarN :
      Matrix.trace ((ρ(X) • (1 : Mat)) * (N : Mat)) = ρ(X) * Matrix.trace (N : Mat) := by
    -- The same scalar-trace normalization applies to the `N` slack.
    calc
      Matrix.trace ((ρ(X) • (1 : Mat)) * (N : Mat))
          = Matrix.trace (ρ(X) • ((1 : Mat) * (N : Mat))) := by
              rw [smul_mul_assoc]
      _ = ρ(X) * Matrix.trace (N : Mat) := by
            simp
  have hPineq :
      0 ≤ ρ(X) * Matrix.trace (P : Mat) - Matrix.trace ((X : Mat) * (P : Mat)) := by
    -- Positivity of `ρI - X` against `P` isolates the positive trace slack for the `P` term.
    have hnonneg :
        0 ≤ Matrix.trace ((ρ(X) • (1 : Mat) - (X : Mat)) * (P : Mat)) :=
      trace_mul_nonneg_of_posSemidef hminus hP
    rwa [sub_mul, Matrix.trace_sub, htraceScalarP] at hnonneg
  have hNineq :
      0 ≤ ρ(X) * Matrix.trace (N : Mat) + Matrix.trace ((X : Mat) * (N : Mat)) := by
    -- Positivity of `ρI + X` against `N` isolates the positive trace slack for the `N` term.
    have hnonneg :
        0 ≤ Matrix.trace ((ρ(X) • (1 : Mat) + (X : Mat)) * (N : Mat)) :=
      trace_mul_nonneg_of_posSemidef hplus hN
    rwa [add_mul, Matrix.trace_add, htraceScalarN] at hnonneg
  have htraceU :
      Matrix.trace ((X : Mat) * (U : Mat)) =
        Matrix.trace ((X : Mat) * (P : Mat)) - Matrix.trace ((X : Mat) * (N : Mat)) := by
    -- Normalize `U = P - N` at the matrix level before expanding trace linearity.
    calc
      Matrix.trace ((X : Mat) * (U : Mat))
          = Matrix.trace ((X : Mat) * ((P : Mat) - (N : Mat))) := by
              rw [hsub, coe_sub_symmMat]
      _ = Matrix.trace ((X : Mat) * (P : Mat)) - Matrix.trace ((X : Mat) * (N : Mat)) := by
            rw [Matrix.mul_sub, Matrix.trace_sub]
  -- The two nonnegative trace slacks and the trace budget now yield the required bound.
  nlinarith [hPineq, hNineq, hbudget, hρ_nonneg, htraceU]

/-- Helper for Lemma 7.3: every element of `Q₂` pairs with `X` by at most `ρ(X)`. -/
theorem trace_pairing_le_spectralRadius_of_mem_Q2
    (X : SymmMat) {U : SymmMat}
    (hU : U ∈ spectral_eigenvalue_l1_unit_ball n) :
    Matrix.trace ((X : Mat) * (U : Mat)) ≤ ρ(X) := by
  rcases (mem_spectral_eigenvalue_l1_unit_ball_iff_exists_psd_trace_split (n := n) U).mp hU with
    ⟨P, N, hP, hN, hsub, hbudget⟩
  exact trace_pairing_le_spectralRadius_of_psdSplit (n := n) hP hN hsub hbudget

/-- Helper for Lemma 7.3: when `n > 0`, one eigenvalue index maximizes the absolute eigenvalue
score on `Fin n`. -/
private theorem existsAbsEigenvalueMaximizer
    (X : SymmMat) (hn : 0 < n) :
    ∃ i : Fin n, IsMaxOn (fun j : Fin n ↦ |eigenvalues X j|) Set.univ i := by
  -- Choose a maximizing eigenvalue index on the finite set `Fin n`, then rewrite it on `Set.univ`.
  obtain ⟨i, -, hi⟩ :=
    Finset.univ.exists_max_image
      (fun j : Fin n ↦ |eigenvalues X j|)
      ⟨(⟨0, hn⟩ : Fin n), by simp⟩
  refine ⟨i, ?_⟩
  rw [isMaxOn_univ_iff]
  intro j
  exact hi j (by simp)

/-- Helper for Lemma 7.3: a maximizer of the absolute eigenvalue family realizes the spectral
radius. -/
private theorem spectralRadiusEqAbsEigenvalueOfIsMaxOn
    (X : SymmMat) {i : Fin n}
    (hi : IsMaxOn (fun j : Fin n ↦ |eigenvalues X j|) Set.univ i) :
    ρ(X) = |eigenvalues X i| := by
  have hi_le : |eigenvalues X i| ≤ ρ(X) := by
    -- Every single absolute eigenvalue lies below the supremum formula for `ρ(X)`.
    rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
    exact Finite.le_ciSup (fun j : Fin n ↦ |eigenvalues X j|) i
  have hρ_le : ρ(X) ≤ |eigenvalues X i| := by
    -- The maximizing index bounds the whole eigenvalue family from above, hence bounds the
    -- conditional supremum as well.
    rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
    letI : Nonempty (Fin n) := ⟨i⟩
    rw [isMaxOn_univ_iff] at hi
    exact ciSup_le hi
  exact le_antisymm hρ_le hi_le

/-- Helper for Lemma 7.3: a nonnegative maximizing eigenvalue is attained by its eigenspace
projector inside `Q₂`. -/
private theorem positiveEigenprojectorAttainsSpectralRadius
    (X : SymmMat) (i : Fin n)
    (hρi : ρ(X) = |eigenvalues X i|)
    (hi_nonneg : 0 ≤ eigenvalues X i) :
    eigenProjector (n := n) X i ∈ spectral_eigenvalue_l1_unit_ball n ∧
      Matrix.trace ((X : Mat) * (((eigenProjector (n := n) X i : SymmMat) : Mat))) = ρ(X) := by
  have hmem :
      eigenProjector (n := n) X i ∈ spectral_eigenvalue_l1_unit_ball n := by
    -- The eigenspace projector is PSD and has trace exactly `1`, so it satisfies the `Q₂`
    -- budget directly.
    refine mem_spectral_eigenvalue_l1_unit_ball_of_posSemidef_trace_le_one
      (n := n)
      (eigenProjector_posSemidef (n := n) X i) ?_
    simpa [eigenProjector_trace_eq_one (n := n) X i]
  refine ⟨hmem, ?_⟩
  -- Evaluate the trace pairing on the eigenspace projector and rewrite through the chosen
  -- nonnegative eigenvalue.
  calc
    Matrix.trace ((X : Mat) * (((eigenProjector (n := n) X i : SymmMat) : Mat)))
        = eigenvalues X i := trace_mul_eigenProjector_eq_eigenvalue (n := n) X i
    _ = |eigenvalues X i| := by
          symm
          exact abs_of_nonneg hi_nonneg
    _ = ρ(X) := hρi.symm

/-- Helper for Lemma 7.3: a nonpositive maximizing eigenvalue is attained by the negative of its
eigenspace projector inside `Q₂`. -/
private theorem negativeEigenprojectorAttainsSpectralRadius
    (X : SymmMat) (i : Fin n)
    (hρi : ρ(X) = |eigenvalues X i|)
    (hi_nonpos : eigenvalues X i ≤ 0) :
    (-eigenProjector (n := n) X i : SymmMat) ∈ spectral_eigenvalue_l1_unit_ball n ∧
      Matrix.trace ((X : Mat) * (((-eigenProjector (n := n) X i : SymmMat) : Mat))) = ρ(X) := by
  have hmem :
      (-eigenProjector (n := n) X i : SymmMat) ∈ spectral_eigenvalue_l1_unit_ball n := by
    -- Route correction: enter `Q₂` through the established PSD-split API `(0, eigenProjector)`
    -- instead of reopening any signed-projector transport.
    rw [mem_spectral_eigenvalue_l1_unit_ball_iff_exists_psd_trace_split]
    refine ⟨0, eigenProjector (n := n) X i, ?_, eigenProjector_posSemidef (n := n) X i, ?_, ?_⟩
    · simpa using (show (((0 : SymmMat) : Mat)).PosSemidef from Matrix.PosSemidef.zero)
    · simp
    · simpa [eigenProjector_trace_eq_one (n := n) X i]
  refine ⟨hmem, ?_⟩
  -- The trace pairing against the negated projector flips the eigenvalue sign and therefore
  -- recovers its absolute value.
  calc
    Matrix.trace ((X : Mat) * (((-eigenProjector (n := n) X i : SymmMat) : Mat)))
        = -Matrix.trace ((X : Mat) * (((eigenProjector (n := n) X i : SymmMat) : Mat))) := by
            simp [Matrix.mul_neg]
    _ = -eigenvalues X i := by
          rw [trace_mul_eigenProjector_eq_eigenvalue (n := n) X i]
    _ = |eigenvalues X i| := by
          symm
          exact abs_of_nonpos hi_nonpos
    _ = ρ(X) := hρi.symm

/-- Helper for Lemma 7.3: some signed eigenspace projector belongs to `Q₂` and attains the
support value `ρ(X)`. -/
theorem exists_signedEigenprojector_mem_Q2_trace_eq_spectralRadius
    (X : SymmMat) :
    ∃ U ∈ spectral_eigenvalue_l1_unit_ball n,
      Matrix.trace ((X : Mat) * (U : Mat)) = ρ(X) := by
  by_cases hn : n = 0
  · -- In the zero-dimensional branch, `Q₂` contains only `0`, and the spectral radius is `0`.
    subst hn
    refine ⟨0, ?_, ?_⟩
    · rw [mem_spectral_eigenvalue_l1_unit_ball_iff]
      simp
    · have hρ : ρ(X) = 0 := by
        -- With no eigenvalue indices, the supremum formula for `ρ(X)` collapses to `0`.
        rw [realSymmetricMatrix_toReal_spectralRadius_eq_iSup_abs_eigenvalues]
        letI : IsEmpty (Fin 0) := inferInstance
        rw [iSup_of_empty']
        simp
      simpa [hρ]
  · -- In positive dimension, choose a maximizing eigenvalue and close by the corresponding sign
    -- branch of the eigenspace projector witness.
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rcases existsAbsEigenvalueMaximizer (n := n) X hn_pos with ⟨i, hmax⟩
    have hρi : ρ(X) = |eigenvalues X i| :=
      spectralRadiusEqAbsEigenvalueOfIsMaxOn (n := n) X hmax
    by_cases hi_nonneg : 0 ≤ eigenvalues X i
    · -- The maximizing eigenvalue is nonnegative, so the projector itself attains `ρ(X)`.
      rcases positiveEigenprojectorAttainsSpectralRadius (n := n) X i hρi hi_nonneg with
        ⟨hU, htrace⟩
      exact ⟨eigenProjector (n := n) X i, hU, htrace⟩
    · -- Otherwise the maximizing eigenvalue is nonpositive, and the negated projector attains
      -- the same absolute eigenvalue.
      have hi_nonpos : eigenvalues X i ≤ 0 := le_of_not_ge hi_nonneg
      rcases negativeEigenprojectorAttainsSpectralRadius (n := n) X i hρi hi_nonpos with
        ⟨hU, htrace⟩
      exact ⟨-eigenProjector (n := n) X i, hU, htrace⟩
