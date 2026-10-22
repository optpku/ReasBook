/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section

section

variable {r m n : ℕ}

/- Definition 7.21 is `source-facing`: the textbook introduces the vector-side symmetric
functional obtained by summing the `k` largest absolute coordinates and then passes to the
`core/canonical` matrix owner given by the singular values of `X.toEuclideanLin`. The public entry
below uses that matrix-side canonical owner, while `ky_fan_vector_function` is the source-facing
vector companion. -/

/-- The Ky Fan `k`-functional on a finite real vector is the sum of the `k` largest absolute
values, counted with multiplicity. -/
noncomputable def ky_fan_vector_function (k : ℕ) (x : Fin r → ℝ) : ℝ :=
  (((List.ofFn fun i : Fin r ↦ |x i|).mergeSort fun a b ↦ decide (a ≥ b)).take k).sum

-- Proof sketch: this is immediate from unfolding `ky_fan_vector_function`.
/-- Unfolding `ky_fan_vector_function` gives the sorted-list formula for the sum of the `k`
largest absolute values. -/
@[simp] theorem ky_fan_vector_function_def (k : ℕ) (x : Fin r → ℝ) :
    ky_fan_vector_function k x =
      (((List.ofFn fun i : Fin r ↦ |x i|).mergeSort fun a b ↦ decide (a ≥ b)).take k).sum := by
  -- Unfold the source-facing definition.
  rfl

/-- Helper for Definition 7.21: an antitone nonnegative finite vector is already in the Ky Fan
normal form, so sorting by decreasing absolute value does nothing and only the first `k` entries
remain. -/
theorem ky_fan_vector_function_of_antitone_nonneg (k : ℕ) (v : Fin r → ℝ)
    (hv : Antitone v) (h_nonneg : ∀ i, 0 ≤ v i) :
    ky_fan_vector_function k v = ∑ i : Fin r with i.1 < k, v i := by
  -- Replace absolute values by the entries themselves using nonnegativity.
  have habs : (List.ofFn fun i : Fin r ↦ |v i|) = List.ofFn v := by
    exact congrArg List.ofFn (funext fun i ↦ abs_of_nonneg (h_nonneg i))
  -- The tuple is already weakly decreasing, so the merge sort is the identity.
  have hsorted : List.Pairwise (fun a b : ℝ ↦ a ≥ b) (List.ofFn v) := by
    simpa using hv.sortedGE_ofFn.pairwise
  rw [ky_fan_vector_function_def, habs]
  rw [List.mergeSort_eq_self (r := (· ≥ ·)) hsorted, List.sum_take_ofFn]

/-- Definition 7.21: the Ky Fan `k`-norm of a real matrix is the sum of its first `k` singular
values, equivalently the symmetric spectral function associated to the sum of the `k` largest
absolute coordinates of a vector. -/
noncomputable def ky_fan_matrix_norm (k : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Finset.sum (Finset.range k) fun i ↦ X.toEuclideanLin.singularValues i

-- Proof sketch: unfold `ky_fan_matrix_norm`; it is defined as the finite sum of the first `k`
-- singular values of `X.toEuclideanLin`.
/-- The defining formula for `ky_fan_matrix_norm` is the sum of the first `k` singular values of
the associated Euclidean linear map. -/
@[simp] theorem ky_fan_matrix_norm_def (k : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) :
    ky_fan_matrix_norm k X =
      Finset.sum (Finset.range k) fun i ↦ X.toEuclideanLin.singularValues i := by
  -- Unfold the canonical matrix-side definition.
  rfl

/-- Helper for Definition 7.21: singular values vanish once the index passes the smaller matrix
dimension, because the range rank is bounded by both the domain and codomain dimensions. -/
theorem singular_values_eq_zero_of_min_dim_le
    (X : Matrix (Fin m) (Fin n) ℝ) {i : ℕ} (hi : min m n ≤ i) :
    X.toEuclideanLin.singularValues i = 0 := by
  -- Bound the range rank by the domain dimension.
  have hdomain : Module.finrank ℝ X.toEuclideanLin.range ≤ n := by
    simpa [finrank_euclideanSpace] using LinearMap.finrank_range_le X.toEuclideanLin
  -- Bound the range rank by the codomain dimension.
  have hcodomain : Module.finrank ℝ X.toEuclideanLin.range ≤ m := by
    simpa [finrank_euclideanSpace] using Submodule.finrank_le X.toEuclideanLin.range
  -- Past the rank, the singular-value sequence is identically zero.
  rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
  exact le_trans (le_min hcodomain hdomain) hi

/-- Helper for Definition 7.21: the matrix-side finite sum over natural-number indices truncates to
the finite singular-value vector indexed by `Fin (min m n)`. -/
theorem sum_range_singular_values_eq_sum_fin_min
    (k : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) :
    ∑ i ∈ Finset.range k, X.toEuclideanLin.singularValues i =
      ∑ i : Fin (min m n) with i.1 < k, X.toEuclideanLin.singularValues i := by
  by_cases hkmn : k ≤ min m n
  · -- When `k` stays inside the finite singular-value vector, reindex `Fin k` into the filtered
    -- subtype of `Fin (min m n)`.
    have hsubtype :
        (∑ i : {j : Fin (min m n) // j.1 < k}, X.toEuclideanLin.singularValues i.1) =
          ∑ i : Fin (min m n) with i.1 < k, X.toEuclideanLin.singularValues i := by
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (Fin (min m n))))
          (f := fun i : Fin (min m n) ↦ X.toEuclideanLin.singularValues i)
          (p := fun i : Fin (min m n) ↦ i.1 < k))
    have hreindex :
        (∑ i : Fin k, X.toEuclideanLin.singularValues i) =
          ∑ i : {j : Fin (min m n) // j.1 < k}, X.toEuclideanLin.singularValues i.1 := by
      simpa using
        (Fintype.sum_equiv (Fin.castLEquiv hkmn)
          (fun i : Fin k ↦ X.toEuclideanLin.singularValues i)
          (fun i : {j : Fin (min m n) // j.1 < k} ↦ X.toEuclideanLin.singularValues i.1)
          (fun i ↦ rfl))
    calc
      ∑ i ∈ Finset.range k, X.toEuclideanLin.singularValues i =
          ∑ i : Fin k, X.toEuclideanLin.singularValues i := by
            simpa using
              (Fin.sum_univ_eq_sum_range (fun i ↦ X.toEuclideanLin.singularValues i) k).symm
      _ = ∑ i : Fin (min m n) with i.1 < k, X.toEuclideanLin.singularValues i := by
            exact hreindex.trans hsubtype
  · have hmnk : min m n ≤ k := le_of_not_ge hkmn
    -- Once `k` passes `min m n`, every extra singular value is zero.
    have htail :
        ∑ i ∈ Finset.Ico (min m n) k, X.toEuclideanLin.singularValues i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact singular_values_eq_zero_of_min_dim_le X (Finset.mem_Ico.mp hi).1
    have hall : ∀ i : Fin (min m n), i.1 < k := by
      intro i
      exact lt_of_lt_of_le i.2 hmnk
    calc
      ∑ i ∈ Finset.range k, X.toEuclideanLin.singularValues i =
          (∑ i ∈ Finset.range (min m n), X.toEuclideanLin.singularValues i) +
            ∑ i ∈ Finset.Ico (min m n) k, X.toEuclideanLin.singularValues i := by
              rw [← Finset.sum_range_add_sum_Ico _ hmnk]
      _ = ∑ i ∈ Finset.range (min m n), X.toEuclideanLin.singularValues i := by
            simp [htail]
      _ = ∑ i : Fin (min m n), X.toEuclideanLin.singularValues i := by
            simpa using
              (Fin.sum_univ_eq_sum_range (fun i ↦ X.toEuclideanLin.singularValues i) (min m n)).symm
      _ = ∑ i : Fin (min m n) with i.1 < k, X.toEuclideanLin.singularValues i := by
            simp [hall]

/-- Helper for Definition 7.21: on a positive real finite-dimensional endomorphism, the operator
norm is the largest eigenvalue in the decreasing eigenvalue list. -/
theorem positive_operator_norm_eq_top_eigenvalue_real
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
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (hn ▸ hk)
  haveI : Nonempty {x : E // x ≠ 0} := by
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
  · -- Every eigenvalue is bounded above by the first entry of the decreasing eigenvalue list.
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

/-- Helper for Definition 7.21: the operator norm of a real finite-dimensional linear map equals
its first singular value. -/
theorem real_operator_norm_eq_first_singular_value
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) :
    ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  by_cases hk : 0 < Module.finrank ℝ E
  · let k : ℕ := Module.finrank ℝ E
    have hn : Module.finrank ℝ E = k := rfl
    have hgram :=
      positive_operator_norm_eq_top_eigenvalue_real hn hk
        (LinearMap.isPositive_adjoint_comp_self T)
    have hnorm_sq : ‖T.toContinuousLinearMap‖ ^ 2 =
        (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn ⟨0, hk⟩ := by
      -- Compare `‖T‖²` with the top eigenvalue of the Gram operator `T†T`.
      calc
        ‖T.toContinuousLinearMap‖ ^ 2 = ‖(LinearMap.adjoint T ∘ₗ T).toContinuousLinearMap‖ := by
          simpa [pow_two] using
            (ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap).symm
        _ = (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn ⟨0, hk⟩ := hgram
    have hsq : ‖T.toContinuousLinearMap‖ ^ 2 = T.singularValues 0 ^ 2 := by
      -- The Gram eigenvalues are exactly the squared singular values.
      exact hnorm_sq.trans (LinearMap.sq_singularValues_fin T hn ⟨0, hk⟩).symm
    have hnorm_nonneg : 0 ≤ ‖T.toContinuousLinearMap‖ := norm_nonneg _
    have hσ_nonneg : 0 ≤ T.singularValues 0 := T.singularValues_nonneg 0
    -- Both sides are nonnegative, so equality of squares upgrades to equality.
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

/-- Helper for Definition 7.21: the largest singular value of a real matrix is its Euclidean
induced operator norm. -/
theorem matrix_l2_op_norm_eq_first_singular_value
    (X : Matrix (Fin m) (Fin n) ℝ) :
    X.toEuclideanLin.singularValues 0 = ‖X‖ := by
  -- Rewrite the matrix norm through `toEuclideanLin` and apply the linear-map bridge.
  simpa [Matrix.l2_opNorm_def] using
    (real_operator_norm_eq_first_singular_value X.toEuclideanLin).symm

-- Proof sketch: the finite function `fun i : Fin (min m n) ↦ X.toEuclideanLin.singularValues i`
-- lists the singular values of `X` in decreasing order, and the singular-value sequence vanishes
-- beyond `min m n`; therefore the matrix-side sum agrees with the vector-side Ky Fan functional
-- applied to that finite singular-value vector.
/-- The matrix Ky Fan norm is the vector Ky Fan functional applied to the finite singular-value
vector of the matrix. -/
theorem ky_fan_matrix_norm_eq_ky_fan_vector_function_singular_values
    (k : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) :
    ky_fan_matrix_norm k X =
      ky_fan_vector_function k (fun i : Fin (min m n) ↦ X.toEuclideanLin.singularValues i) := by
  -- Rewrite the matrix-side definition to the truncated singular-value sum.
  rw [ky_fan_matrix_norm_def]
  -- On the vector side, singular values are already ordered and nonnegative.
  rw [ky_fan_vector_function_of_antitone_nonneg (v := fun i : Fin (min m n) ↦
    X.toEuclideanLin.singularValues i)]
  · exact sum_range_singular_values_eq_sum_fin_min k X
  · intro i j hij
    exact X.toEuclideanLin.singularValues_antitone (show (i : ℕ) ≤ j from hij)
  · intro i
    exact X.toEuclideanLin.singularValues_nonneg i

-- Proof sketch: the sum over `Finset.range 1` has the unique term indexed by `0`.
/-- The Ky Fan `1`-norm is the largest singular value. -/
@[simp] theorem ky_fan_matrix_norm_one_eq_max_singular_value (X : Matrix (Fin m) (Fin n) ℝ) :
    ky_fan_matrix_norm 1 X = X.toEuclideanLin.singularValues 0 := by
  -- The range sum for `k = 1` contains exactly the index `0`.
  rw [ky_fan_matrix_norm_def]
  simp

-- Proof sketch: combine `ky_fan_matrix_norm_one_eq_max_singular_value` with the standard fact
-- that the Euclidean induced operator norm of a real matrix is its largest singular value.
/-- The Ky Fan `1`-norm agrees with the Euclidean induced operator norm. -/
theorem ky_fan_matrix_norm_one_eq_l2_induced_matrix_norm (X : Matrix (Fin m) (Fin n) ℝ) :
    ky_fan_matrix_norm 1 X = ‖X‖ := by
  -- First identify the Ky Fan `1`-norm with the top singular value.
  rw [ky_fan_matrix_norm_one_eq_max_singular_value]
  -- Then convert the first singular value to the Euclidean induced matrix norm.
  exact matrix_l2_op_norm_eq_first_singular_value X

end
