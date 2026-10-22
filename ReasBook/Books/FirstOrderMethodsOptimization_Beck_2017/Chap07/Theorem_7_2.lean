/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_30
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_10

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open InnerProductSpace
open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "𝕊" => symmetricMatrices n

local instance instTheorem72NormedAddCommGroupMatrix : NormedAddCommGroup Mₙ :=
  Matrix.frobeniusNormedAddCommGroup
local instance instTheorem72NormedSpaceMatrix : NormedSpace ℝ Mₙ :=
  Matrix.frobeniusNormedSpace
local instance instTheorem72InnerProductSpaceMatrix : InnerProductSpace ℝ Mₙ :=
  Matrix.frobeniusInnerProductSpace

/-- Helper for Theorem 7.2: the Frobenius inner product on real matrices is the entrywise double
sum. -/
lemma matrix_inner_eq_sum_mul (A B : Mₙ) :
    ⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j := by
  -- Rewrite the Frobenius inner product through the nested `ℓ²` model of matrices.
  change inner ℝ (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ A i j)
      (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ B i j) =
    ∑ i, ∑ j, A i j * B i j
  rw [PiLp.inner_apply]
  have hrow :
      ∀ i,
        ⟪WithLp.toLp 2 (fun j ↦ A i j), WithLp.toLp 2 (fun j ↦ B i j)⟫_ℝ =
          ∑ j, A i j * B i j := by
    intro i
    -- On each row, the Euclidean inner product is the coordinate dot product.
    simpa [dotProduct, mul_comm] using
      EuclideanSpace.inner_toLp_toLp (fun j ↦ A i j) (fun j ↦ B i j)
  simp [hrow]

/-- Helper for Theorem 7.2: the Riesz pairing on `𝕊^n` is the trace pairing `Tr(XY)`. -/
lemma toDualMap_apply_eq_trace_mul (X Y : 𝕊) :
    (toDualMap ℝ 𝕊 Y : Module.Dual ℝ 𝕊) X = Matrix.trace ((X : Mₙ) * (Y : Mₙ)) := by
  -- Move from the submodule Riesz map to the ambient Frobenius inner product.
  change ⟪Y, X⟫_ℝ = Matrix.trace ((X : Mₙ) * (Y : Mₙ))
  rw [Submodule.coe_inner]
  calc
    ⟪(Y : Mₙ), (X : Mₙ)⟫_ℝ = ∑ i, ∑ j, (Y : Mₙ) i j * (X : Mₙ) i j := by
      rw [matrix_inner_eq_sum_mul]
    _ = Matrix.trace ((Y : Mₙ) * (X : Mₙ)) := by
      symm
      exact matrixDotProduct_eq_sum_mul_symmetricMatrices Y X
    _ = Matrix.trace ((X : Mₙ) * (Y : Mₙ)) := by
      -- For real symmetric matrices, transposing swaps the factors without changing the trace.
      rw [← Matrix.trace_transpose (A := (Y : Mₙ) * (X : Mₙ)), Matrix.transpose_mul]
      simp

/-- Helper for Theorem 7.2: the decreasing rearrangement is antitone. -/
lemma antitone_descendingRearrangement (x : Fin n → ℝ) :
    Antitone (x↓) := by
  -- Sorting is monotone, and `Fin.revPerm` reverses the order.
  simpa [Function.comp_def, descendingRearrangement] using
    (Tuple.monotone_sort x).comp_antitone Fin.rev_anti

/-- Helper for Theorem 7.2: the decreasing rearrangement is idempotent. -/
lemma descendingRearrangement_idem (x : Fin n → ℝ) :
    (x↓)↓ = x↓ := by
  -- After one sorting pass, a second pass leaves the tuple unchanged.
  simpa [descendingRearrangement, Function.comp_assoc, Equiv.Perm.coe_mul] using
    (descendingRearrangement_comp_perm x (Tuple.sort x * Fin.revPerm))

/-- Helper for Theorem 7.2: an antitone vector is already equal to its decreasing rearrangement. -/
lemma descendingRearrangement_eq_self_of_antitone (x : Fin n → ℝ) (hx : Antitone x) :
    x↓ = x := by
  have hsorted : x ∘ Fin.revPerm = x ∘ Tuple.sort x := by
    -- `x ∘ Fin.revPerm` is monotone because `x` is antitone.
    rw [Tuple.comp_sort_eq_comp_iff_monotone]
    intro i j hij
    exact hx (by simpa using hij)
  ext i
  -- Evaluate the sorted identity at the reversed index and simplify.
  have hi := congrFun hsorted (Fin.revPerm i)
  simpa [descendingRearrangement, Function.comp_def] using hi.symm

/-- Helper for Theorem 7.2: against a decreasing target vector, sorting the other vector can only
increase the dot product. -/
lemma dotProduct_le_dotProduct_descendingRearrangement
    (x y : Fin n → ℝ) (hy : Antitone y) :
    dotProduct x y ≤ dotProduct x↓ y := by
  let σ : Equiv.Perm (Fin n) := Fin.revPerm.symm * (Tuple.sort x).symm
  have hx : ∀ i, x i = x↓ (σ i) := by
    intro i
    -- The chosen permutation unsorts `x↓` back to `x`.
    simp [σ, descendingRearrangement, Function.comp_def, Equiv.Perm.coe_mul]
  have hmono : Monovary y x↓ := hy.monovary (antitone_descendingRearrangement x)
  have hσ := Monovary.sum_mul_comp_perm_le_sum_mul (σ := σ) hmono
  rw [dotProduct, dotProduct]
  convert hσ using 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hx i, mul_comm]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [mul_comm]

/-- Helper for Theorem 7.2: a diagonal real matrix is symmetric. -/
lemma diagonal_mem_symmetricMatrices (x : Fin n → ℝ) :
    Matrix.diagonal x ∈ 𝕊 := by
  -- Diagonal matrices are fixed by transpose.
  rw [mem_symmetricMatrices_iff]
  simp

/-- Helper for Theorem 7.2: an orthogonal conjugate of a diagonal real matrix is symmetric. -/
lemma orthogonal_conjugate_diagonal_mem
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    (U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ ∈ 𝕊 := by
  -- Transpose the product and simplify the diagonal transpose.
  rw [mem_symmetricMatrices_iff]
  simp [Matrix.transpose_mul, mul_assoc]

/-- Helper for Theorem 7.2: orthogonal conjugation preserves the characteristic polynomial of a
diagonal matrix. -/
lemma orthogonal_conjugate_diagonal_charpoly
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix.charpoly ((U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ) =
      Matrix.charpoly (Matrix.diagonal x) := by
  -- Cyclically move one orthogonal factor across the characteristic polynomial.
  calc
    Matrix.charpoly ((U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ) =
        Matrix.charpoly ((U : Mₙ) * (Matrix.diagonal x * (U : Mₙ)ᵀ)) := by
          simp [mul_assoc]
    _ = Matrix.charpoly ((Matrix.diagonal x * (U : Mₙ)ᵀ) * (U : Mₙ)) := by
          rw [Matrix.charpoly_mul_comm]
    _ = Matrix.charpoly (Matrix.diagonal x * ((U : Mₙ)ᵀ * (U : Mₙ))) := by
          rw [mul_assoc]
    _ = Matrix.charpoly (Matrix.diagonal x) := by
          have hU : (U : Mₙ)ᵀ * (U : Mₙ) = 1 :=
            (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
          rw [hU, Matrix.mul_one]

/-- Helper for Theorem 7.2: the zero-indexed Hermitian eigenvalue list of an antitone diagonal
matrix is exactly its diagonal. -/
lemma diagonal_eigenvalues_zero_indexed_of_antitone
    (x : Fin n → ℝ) (hx : Antitone x) :
    let A : Mₙ := Matrix.diagonal x
    let hA : A.IsHermitian := by simp [A]
    hA.eigenvalues₀ = fun j : Fin (Fintype.card (Fin n)) ↦ x (Fin.cast (by simp) j) := by
  let A : Mₙ := Matrix.diagonal x
  let hA : A.IsHermitian := by simp [A]
  have hcast_anti :
      Antitone (fun j : Fin (Fintype.card (Fin n)) ↦ x (Fin.cast (by simp) j)) := by
    -- Transport the monotonicity across the canonical `Fin.cast`.
    simpa using hx.comp_monotone
      (show Monotone (fun j : Fin (Fintype.card (Fin n)) ↦ Fin.cast (by simp) j) by
        intro a b hab
        simpa using hab)
  have hroots :
      A.charpoly.roots =
        Multiset.map
          (RCLike.ofReal ∘ fun j : Fin (Fintype.card (Fin n)) ↦ x (Fin.cast (by simp) j))
          Finset.univ.val := by
    -- The roots of a diagonal characteristic polynomial are the diagonal entries.
    rw [show A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (x i)) by
      simpa [A] using Matrix.charpoly_diagonal x]
    rw [Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort :
      (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) =
        List.ofFn (fun j : Fin (Fintype.card (Fin n)) ↦ x (Fin.cast (by simp) j)) := by
    -- Both sides are the decreasing sort of the same real-root multiset.
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hcast_anti.sortedGE_ofFn
  exact List.ofFn_inj.1 (hA.sort_roots_charpoly_eq_eigenvalues₀.symm.trans hsort)

/-- Helper for Theorem 7.2: the eigenvalue map of a diagonal symmetric matrix returns the diagonal
when that diagonal is already decreasing. -/
lemma diagonal_symmetric_eigenvalue_function_eq_of_antitone
    (x : Fin n → ℝ) (hx : Antitone x) :
    symmetric_eigenvalue_function ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩ = x := by
  ext i
  rw [symmetric_eigenvalue_function_apply]
  have hdiag := diagonal_eigenvalues_zero_indexed_of_antitone (n := n) x hx
  simpa using congrFun hdiag (Fin.cast (Fintype.card_fin n).symm i)

/-- Helper for Theorem 7.2: orthogonal conjugation of a decreasing diagonal keeps the same ordered
eigenvalue vector. -/
lemma orthogonal_diagonal_symmetric_eigenvalue_function_eq_of_antitone
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) (hx : Antitone x) :
    symmetric_eigenvalue_function
        ⟨(U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ,
          orthogonal_conjugate_diagonal_mem U x⟩ = x := by
  let Z : 𝕊 :=
    ⟨(U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ, orthogonal_conjugate_diagonal_mem U x⟩
  let D : 𝕊 := ⟨Matrix.diagonal x, diagonal_mem_symmetricMatrices x⟩
  have hchar : ((Z : Mₙ)).charpoly = ((D : Mₙ)).charpoly := by
    simpa [Z, D] using orthogonal_conjugate_diagonal_charpoly U x
  have heig0 : Z.property.isHermitian.eigenvalues₀ = D.property.isHermitian.eigenvalues₀ := by
    -- The ordered zero-indexed Hermitian spectrum is determined by the characteristic polynomial.
    simp_rw [← List.ofFn_inj, ← Z.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀,
      ← D.property.isHermitian.sort_roots_charpoly_eq_eigenvalues₀, hchar]
  ext i
  rw [symmetric_eigenvalue_function_apply]
  have hdiag := diagonal_eigenvalues_zero_indexed_of_antitone (n := n) x hx
  simpa [D] using congrFun (heig0.trans hdiag) (Fin.cast (Fintype.card_fin n).symm i)

/-- Helper for Theorem 7.2: the imported `eigenvalues` lists inherit monovariance because they are
both reindexed from the decreasing zero-indexed eigenvalue lists by the same equivalence. -/
private lemma hermitian_eigenvalues_monovary {A B : Mₙ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Monovary hA.eigenvalues hB.eigenvalues := by
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  -- The zero-indexed eigenvalue lists are decreasing, hence they monovary.
  have hAB : Monovary hA.eigenvalues₀ hB.eigenvalues₀ :=
    hA.eigenvalues₀_antitone.monovary hB.eigenvalues₀_antitone
  -- Reindexing both lists by the same equivalence preserves monovariance.
  simpa [Matrix.IsHermitian.eigenvalues, e] using hAB.comp_right e

/-- Helper for Theorem 7.2: squaring the entries of an orthogonal matrix gives a doubly
stochastic matrix. -/
private lemma orthogonal_entrywise_sq_mem_doubly_stochastic
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (fun i j : Fin n ↦ (Q i j)^2 : Mₙ) ∈ doublyStochastic ℝ (Fin n) := by
  -- The row and column sums are the diagonal entries of `Q Qᵀ` and `Qᵀ Q`.
  exact (mem_doublyStochastic_iff_sum).2 <| by
    constructor
    · intro i j
      positivity
    constructor
    · intro i
      have hQQT : ((Q : Mₙ) * (Q : Mₙ)ᵀ) i i = (1 : Mₙ) i i := by
        simpa using congrFun
          (congrFun ((Matrix.mem_orthogonalGroup_iff (A := (Q : Mₙ)) (R := ℝ)).1 Q.2) i) i
      simpa [Matrix.mul_apply, pow_two] using hQQT
    · intro j
      have hQTQ : (((Q : Mₙ)ᵀ) * (Q : Mₙ)) j j = (1 : Mₙ) j j := by
        simpa using congrFun
          (congrFun ((Matrix.mem_orthogonalGroup_iff' (A := (Q : Mₙ)) (R := ℝ)).1 Q.2) j) j
      simpa [Matrix.mul_apply, pow_two, mul_comm] using hQTQ

/-- Helper for Theorem 7.2: the diagonal entries of an orthogonal conjugate of a diagonal matrix
are weighted by the squared orthogonal entries. -/
private lemma diagonal_conj_entry (y : Fin n → ℝ) (Q : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    (((Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) i i) = ∑ j, (Q i j)^2 * y j := by
  -- Expand the diagonal conjugation and normalize the finite sum.
  rw [mul_assoc]
  simp [Matrix.diagonal, Matrix.mul_apply]
  ring_nf

/-- Helper for Theorem 7.2: after diagonalizing both matrices, the trace pairing becomes the dot
product against the doubly stochastic matrix of squared orthogonal entries. -/
private lemma orthogonal_trace_reduction (x y : Fin n → ℝ) (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    Matrix.trace (Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) =
      dotProduct x ((fun i j : Fin n ↦ (Q i j)^2 : Mₙ) *ᵥ y) := by
  calc
    Matrix.trace (Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ))
      = ∑ i, x i * ∑ j, (Q i j)^2 * y j := by
          rw [Matrix.trace]
          apply Finset.sum_congr rfl
          intro i hi
          change ((Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) i i) = _
          -- The left diagonal factor contributes exactly the scalar `x i`.
          have hmul :
              ((Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)).diag i) =
                x i * (((Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) i i) := by
            rw [show (Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)).diag i
                = ((Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) i i) by rfl]
            rw [mul_assoc]
            simp [Matrix.diagonal, Matrix.mul_apply]
            ring_nf
            simpa [mul_assoc] using
              (Finset.mul_sum Finset.univ (fun j : Fin n ↦ (Q i j)^2 * y j) (x i)).symm
          have hmul' :
              ((Matrix.diagonal x * (Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) i i) =
                x i * (((Q : Mₙ) * Matrix.diagonal y * ((Q : Mₙ)ᵀ)) i i) := by
            simpa [Matrix.diag] using hmul
          rw [hmul', diagonal_conj_entry y Q i]
    _ = dotProduct x ((fun i j : Fin n ↦ (Q i j)^2 : Mₙ) *ᵥ y) := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Theorem 7.2: a doubly stochastic matrix cannot increase the dot product of two
monovarying real vectors. -/
private lemma doubly_stochastic_dotProduct_le_of_monovary (x y : Fin n → ℝ) (P : Mₙ)
    (hxy : Monovary x y) (hP : P ∈ doublyStochastic ℝ (Fin n)) :
    dotProduct x (P *ᵥ y) ≤ dotProduct x y := by
  obtain ⟨w, hw_nonneg, hw_sum, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  calc
    dotProduct x (P *ᵥ y)
      = dotProduct x (((∑ σ, w σ • σ.permMatrix ℝ : Mₙ) : Mₙ) *ᵥ y) := by
          rw [hwP]
    _ = dotProduct x (∑ σ, w σ • ((σ.permMatrix ℝ : Mₙ) *ᵥ y)) := by
          rw [sum_mulVec]
          congr
          ext σ
          rw [smul_mulVec]
    _ = ∑ σ, dotProduct x (w σ • ((σ.permMatrix ℝ : Mₙ) *ᵥ y)) := by
          rw [dotProduct_sum]
    _ = ∑ σ, w σ * ∑ i, x i * y (σ i) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [dotProduct_smul]
          simp [Matrix.permMatrix_mulVec, dotProduct]
    _ ≤ ∑ σ, w σ * dotProduct x y := by
          apply Finset.sum_le_sum
          intro σ hσ
          exact mul_le_mul_of_nonneg_left (hxy.sum_mul_comp_perm_le_sum_mul) (hw_nonneg σ)
    _ = (∑ σ, w σ) * dotProduct x y := by
          simp [Finset.sum_mul]
    _ = dotProduct x y := by
          rw [hw_sum, one_mul]

/-- Helper for Theorem 7.2: every symmetric matrix has an orthogonal diagonalization with the
mathlib `eigenvalues` enumeration on the diagonal. -/
lemma exists_orthogonal_diagonalization_with_eigenvalues (Y : 𝕊) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      (Y : Mₙ) = (U : Mₙ) * Matrix.diagonal Y.property.isHermitian.eigenvalues * (U : Mₙ)ᵀ := by
  let hY : (Y : Mₙ).IsHermitian := Y.property.isHermitian
  refine ⟨hY.eigenvectorUnitary, ?_⟩
  -- Rewrite the Hermitian spectral theorem over `ℝ` into the orthogonal form.
  simpa [hY, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
    Function.comp_apply, mul_assoc] using hY.spectral_theorem

/-- Helper for Theorem 7.2: mathlib's `eigenvalues` coordinate system differs from
`symmetric_eigenvalue_function` only by a fixed permutation of `Fin n`. -/
lemma exists_eigenvalue_reindex_perm :
    ∃ σ : Equiv.Perm (Fin n), ∀ X : 𝕊,
      X.property.isHermitian.eigenvalues = symmetric_eigenvalue_function X ∘ σ := by
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let c : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    { toFun := Fin.cast (Fintype.card_fin n).symm
      invFun := Fin.cast (Fintype.card_fin n)
      left_inv := by
        intro i
        simp
      right_inv := by
        intro i
        simp }
  refine ⟨e.trans c.symm, ?_⟩
  intro X
  -- Rewrite both eigenvalue enumerations to the common zero-indexed spectrum.
  ext i
  simp [Matrix.IsHermitian.eigenvalues, symmetric_eigenvalue_function, e, c, Function.comp_def]

/-- Helper for Theorem 7.2: reindexing both arguments of the Euclidean pairing by the same
permutation leaves the dot product unchanged. -/
lemma dotProduct_comp_perm (σ : Equiv.Perm (Fin n)) (x y : Fin n → ℝ) :
    dotProduct (x ∘ σ) (y ∘ σ) = dotProduct x y := by
  -- Sum over the permuted index set and then collapse back to `Finset.univ`.
  simpa [dotProduct, Function.comp_def] using
    (σ.sum_comp Finset.univ (fun i : Fin n ↦ x i * y i) (by simp))

/-- Helper for Theorem 7.2: Fan's inequality rewritten in the ordered eigenvalue notation used in
this file. -/
lemma fan_inequality_trace_le_dotProduct_symmetric_eigenvalue_function
    (X Y : 𝕊) :
    Matrix.trace ((X : Mₙ) * (Y : Mₙ)) ≤
      dotProduct (symmetric_eigenvalue_function X) (symmetric_eigenvalue_function Y) := by
  obtain ⟨σ, hσ⟩ := exists_eigenvalue_reindex_perm (n := n)
  let hX : (X : Mₙ).IsHermitian := X.property.isHermitian
  let hY : (Y : Mₙ).IsHermitian := Y.property.isHermitian
  let U : Matrix.orthogonalGroup (Fin n) ℝ := hX.eigenvectorUnitary
  let W : Matrix.orthogonalGroup (Fin n) ℝ := hY.eigenvectorUnitary
  let Q : Matrix.orthogonalGroup (Fin n) ℝ := star U * W
  have hQ : ((Q : Mₙ)) = (U : Mₙ)ᵀ * (W : Mₙ) := by
    change star (U : Mₙ) * (W : Mₙ) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hdiagX : (X : Mₙ) = (U : Mₙ) * Matrix.diagonal hX.eigenvalues * (U : Mₙ)ᵀ := by
    -- Use the Hermitian spectral theorem in real coordinates.
    simpa [hX, U, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_apply, mul_assoc] using hX.spectral_theorem
  have hdiagY : (Y : Mₙ) = (W : Mₙ) * Matrix.diagonal hY.eigenvalues * (W : Mₙ)ᵀ := by
    -- The same diagonalization applies to `Y`.
    simpa [hY, W, Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_apply, mul_assoc] using hY.spectral_theorem
  have htrace : Matrix.trace ((X : Mₙ) * (Y : Mₙ)) =
      Matrix.trace (Matrix.diagonal hX.eigenvalues * (Q : Mₙ) *
        Matrix.diagonal hY.eigenvalues * ((Q : Mₙ)ᵀ)) := by
    -- Cycle the trace so that the relative orthogonal matrix `Q = Uᵀ W` appears explicitly.
    conv_lhs => rw [hdiagX, hdiagY]
    rw [show Matrix.trace ((U : Mₙ) * Matrix.diagonal hX.eigenvalues * (U : Mₙ)ᵀ *
        ((W : Mₙ) * Matrix.diagonal hY.eigenvalues * (W : Mₙ)ᵀ))
        = Matrix.trace (((U : Mₙ) * Matrix.diagonal hX.eigenvalues) * ((U : Mₙ)ᵀ * (W : Mₙ)) *
            (Matrix.diagonal hY.eigenvalues * (W : Mₙ)ᵀ)) by
          simp [mul_assoc]]
    rw [Matrix.trace_mul_cycle ((U : Mₙ) * Matrix.diagonal hX.eigenvalues) ((U : Mₙ)ᵀ * (W : Mₙ))
      (Matrix.diagonal hY.eigenvalues * (W : Mₙ)ᵀ)]
    rw [show Matrix.trace ((Matrix.diagonal hY.eigenvalues * (W : Mₙ)ᵀ) *
        ((U : Mₙ) * Matrix.diagonal hX.eigenvalues) * ((U : Mₙ)ᵀ * (W : Mₙ)))
        = Matrix.trace ((Matrix.diagonal hY.eigenvalues * ((W : Mₙ)ᵀ * (U : Mₙ))) *
            (Matrix.diagonal hX.eigenvalues * ((U : Mₙ)ᵀ * (W : Mₙ)))) by
          simp [mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp [hQ, mul_assoc]
  -- Fan's inequality follows from the doubly stochastic reduction, then we reindex to `λ`.
  calc
    Matrix.trace ((X : Mₙ) * (Y : Mₙ))
      = Matrix.trace (Matrix.diagonal hX.eigenvalues * (Q : Mₙ) *
          Matrix.diagonal hY.eigenvalues * ((Q : Mₙ)ᵀ)) := htrace
    _ = dotProduct hX.eigenvalues ((fun i j : Fin n ↦ (Q i j)^2 : Mₙ) *ᵥ hY.eigenvalues) := by
          exact orthogonal_trace_reduction hX.eigenvalues hY.eigenvalues Q
    _ ≤ dotProduct hX.eigenvalues hY.eigenvalues := by
          exact doubly_stochastic_dotProduct_le_of_monovary _ _ _
            (hermitian_eigenvalues_monovary hX hY)
            (orthogonal_entrywise_sq_mem_doubly_stochastic Q)
    _ = dotProduct (symmetric_eigenvalue_function X ∘ σ) (symmetric_eigenvalue_function Y ∘ σ) := by
      rw [hσ X, hσ Y]
    _ = dotProduct (symmetric_eigenvalue_function X) (symmetric_eigenvalue_function Y) := by
      exact dotProduct_comp_perm σ
        (symmetric_eigenvalue_function X) (symmetric_eigenvalue_function Y)

/-- Helper for Theorem 7.2: conjugating a diagonal matrix by the permutation matrix of `σ`
reindexes the diagonal entries by `σ`. -/
lemma diagonal_comp_perm_eq_orthogonal_conjugate
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    Matrix.diagonal (x ∘ σ) =
      ((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
        Matrix.diagonal x *
        (((permutationOrthogonalMatrix σ : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) := by
  -- Compute with the underlying permutation matrix; only one summand survives in each entry.
  change Matrix.diagonal (x ∘ σ) = σ.permMatrix ℝ * Matrix.diagonal x * (σ.permMatrix ℝ)ᵀ
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.mul_apply, Matrix.diagonal]
    rw [Finset.sum_eq_single (σ i)]
    · simp
    · intro b hb hne
      by_cases hbi : (Equiv.symm σ) b = i
      · have : b = σ i := by simpa using congrArg σ hbi
        contradiction
      · simp [hbi]
    · intro hnot
      simp at hnot
  · simp [Matrix.mul_apply, Matrix.diagonal, hij]
    rw [Finset.sum_eq_single (σ i)]
    · simp [hij]
    · intro b hb hne
      by_cases hbj : (Equiv.symm σ) b = j
      · have hbσ : b = σ j := by simpa using congrArg σ hbj
        by_cases hbi : σ i = b
        · exfalso
          apply hij
          apply σ.injective
          simpa [hbσ] using hbi
        · simp [hbj, hbi]
      · simp [hbj]
    · intro hnot
      simp at hnot

/-- Helper for Theorem 7.2: every symmetric matrix admits an orthogonal diagonalization whose
diagonal entries are exactly `symmetric_eigenvalue_function`. -/
lemma exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function
    (Y : 𝕊) :
    ∃ U : Matrix.orthogonalGroup (Fin n) ℝ,
      (Y : Mₙ) = (U : Mₙ) * Matrix.diagonal (symmetric_eigenvalue_function Y) * (U : Mₙ)ᵀ := by
  obtain ⟨σ, hσ⟩ := exists_eigenvalue_reindex_perm (n := n)
  rcases exists_orthogonal_diagonalization_with_eigenvalues Y with ⟨V, hV⟩
  let P : Matrix.orthogonalGroup (Fin n) ℝ := permutationOrthogonalMatrix σ
  refine ⟨V * P, ?_⟩
  -- Route correction: the imported diagonalization uses `eigenvalues`; conjugating the diagonal
  -- by the fixed permutation matrix converts it to `symmetric_eigenvalue_function`.
  calc
    (Y : Mₙ) = (V : Mₙ) * Matrix.diagonal Y.property.isHermitian.eigenvalues * (V : Mₙ)ᵀ := hV
    _ = (V : Mₙ) *
        (((P : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
          Matrix.diagonal (symmetric_eigenvalue_function Y) *
          ((P : Mₙ)ᵀ)) *
        (V : Mₙ)ᵀ := by
          rw [hσ Y, diagonal_comp_perm_eq_orthogonal_conjugate σ (symmetric_eigenvalue_function Y)]
    _ = ((V * P : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ) *
        Matrix.diagonal (symmetric_eigenvalue_function Y) *
        (((V * P : Matrix.orthogonalGroup (Fin n) ℝ) : Mₙ)ᵀ) := by
          simp [mul_assoc, Matrix.transpose_mul]

/-- Helper for Theorem 7.2: after diagonalizing `Y` in the ordered eigenvalue basis, the trace
pairing with an orthogonal conjugate of `diag x` is the Euclidean pairing `⟨x, λ(Y)⟩`. -/
lemma trace_orthogonal_diagonal_mul_eq_dotProduct_symmetric_eigenvalue_function
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (Y : 𝕊)
    (hY : (Y : Mₙ) = (U : Mₙ) * Matrix.diagonal (symmetric_eigenvalue_function Y) * (U : Mₙ)ᵀ)
    (x : Fin n → ℝ) :
    Matrix.trace (((U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ) * (Y : Mₙ)) =
      dotProduct x (symmetric_eigenvalue_function Y) := by
  have hU : ((U : Mₙ)ᵀ * (U : Mₙ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (U : Mₙ)) (R := ℝ)).1 U.2
  -- Use the diagonalization of `Y`, cycle the trace, and then evaluate the diagonal trace.
  rw [hY]
  have hmul :
      ((U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ) *
          ((U : Mₙ) * Matrix.diagonal (symmetric_eigenvalue_function Y) * (U : Mₙ)ᵀ) =
        (U : Mₙ) *
          (Matrix.diagonal x * Matrix.diagonal (symmetric_eigenvalue_function Y)) *
          (U : Mₙ)ᵀ := by
    calc
      ((U : Mₙ) * Matrix.diagonal x * (U : Mₙ)ᵀ) *
          ((U : Mₙ) * Matrix.diagonal (symmetric_eigenvalue_function Y) * (U : Mₙ)ᵀ)
        = (U : Mₙ) * Matrix.diagonal x *
            (((U : Mₙ)ᵀ * (U : Mₙ)) * Matrix.diagonal (symmetric_eigenvalue_function Y)) *
            (U : Mₙ)ᵀ := by
              simp [mul_assoc]
      _ = (U : Mₙ) * Matrix.diagonal x * Matrix.diagonal (symmetric_eigenvalue_function Y) *
            (U : Mₙ)ᵀ := by
              rw [hU]
              simp
      _ = (U : Mₙ) *
            (Matrix.diagonal x * Matrix.diagonal (symmetric_eigenvalue_function Y)) *
            (U : Mₙ)ᵀ := by
              simp [mul_assoc]
  rw [hmul]
  rw [Matrix.trace_mul_cycle (U : Mₙ)
    (Matrix.diagonal x * Matrix.diagonal (symmetric_eigenvalue_function Y)) ((U : Mₙ)ᵀ)]
  rw [hU]
  simp [Matrix.trace_diagonal, dotProduct]

-- Proof sketch: prove the two inequalities from the textbook. For the `≤` direction, expand the
-- left-hand conjugate on `𝕊` using the Frobenius/trace pairing identified by `toDualMap`, apply
-- Fan's inequality to bound `Tr(XY)` by the Euclidean pairing of the ordered eigenvalue vectors,
-- and then recognize the resulting supremum as `f* (λ Y)`. For the reverse inequality, diagonalize
-- `Y`, restrict the left-hand supremum to matrices sharing this eigenbasis, and rewrite those
-- matrices as conjugates of diagonal matrices so that the spectral term reduces to `f`.
/-- Theorem 7.2: for a permutation symmetric function `f` on `ℝ^n`, the Fenchel conjugate of the
spectral function `f ∘ λ` on `𝕊^n`, viewed on `𝕊^n` through the Frobenius Riesz map
`toDualMap ℝ 𝕊`, is the vector-side Fenchel conjugate `f*` composed with the ordered eigenvalue
map `λ`. -/
theorem spectral_conjugate_formula
    (f : (Fin n → ℝ) → EReal) (hf : IsPermutationSymmetricFunction f) :
    (fun Y : 𝕊 ↦ conjugate_function (f ∘ symmetric_eigenvalue_function) ↑(toDualMap ℝ 𝕊 Y)) =
      fun Y : 𝕊 ↦ conjugate_function f (dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) :=
  by
    ext Y
    rw [conjugate_function_apply, conjugate_function_apply]
    have hf_desc :
        ∀ x : Fin n → ℝ, f x = f x↓ :=
      ((isPermutationSymmetricFunction_iff_forall_eq_descendingRearrangement f).1 hf).2
    apply le_antisymm
    · refine sSup_le ?_
      rintro z ⟨X, rfl⟩
      -- Use the trace pairing formula and Fan's inequality, then insert `λ(X)` as a vector witness.
      calc
        (((toDualMap ℝ 𝕊 Y : Module.Dual ℝ 𝕊) X : ℝ) : EReal) - f (symmetric_eigenvalue_function X)
          = ((Matrix.trace ((X : Mₙ) * (Y : Mₙ)) : ℝ) : EReal) - f (symmetric_eigenvalue_function X) := by
              rw [toDualMap_apply_eq_trace_mul]
        _ ≤ ((dotProduct (symmetric_eigenvalue_function X) (symmetric_eigenvalue_function Y) : ℝ) : EReal) -
              f (symmetric_eigenvalue_function X) := by
              have hfan :
                  (((Matrix.trace ((X : Mₙ) * (Y : Mₙ)) : ℝ) : EReal)) ≤
                    (((dotProduct (symmetric_eigenvalue_function X)
                        (symmetric_eigenvalue_function Y) : ℝ) : EReal)) := by
                exact_mod_cast
                  fan_inequality_trace_le_dotProduct_symmetric_eigenvalue_function X Y
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                add_le_add_left hfan (-f (symmetric_eigenvalue_function X))
        _ ≤ sSup (Set.range fun x : Fin n → ℝ ↦
              (((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x : ℝ) : EReal) -
                f x) := by
              simpa [dotProductEquiv, dotProduct_comm] using
                (le_sSup (Set.mem_range_self (symmetric_eigenvalue_function X)) :
                  ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y))
                      (symmetric_eigenvalue_function X) : ℝ) : EReal) -
                      f (symmetric_eigenvalue_function X)) ≤
                    sSup (Set.range fun x : Fin n → ℝ ↦
                      (((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x : ℝ) :
                        EReal) - f x))
    · refine sSup_le ?_
      rintro z ⟨x, rfl⟩
      obtain ⟨U, hY⟩ := exists_orthogonal_diagonalization_with_symmetric_eigenvalue_function Y
      let Z : 𝕊 :=
        ⟨(U : Mₙ) * Matrix.diagonal (x↓) * (U : Mₙ)ᵀ,
          orthogonal_conjugate_diagonal_mem U (x↓)⟩
      have hdot :
          dotProduct x (symmetric_eigenvalue_function Y) ≤
            dotProduct x↓ (symmetric_eigenvalue_function Y) :=
        dotProduct_le_dotProduct_descendingRearrangement x
          (symmetric_eigenvalue_function Y) (symmetric_eigenvalue_function_antitone Y)
      have hsort :
          ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x : ℝ) : EReal) - f x) ≤
            ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x↓ : ℝ) : EReal) -
              f (x↓)) := by
        -- Sorting increases the linear term against the decreasing eigenvalue vector, while `f`
        -- is unchanged by permutation symmetry.
        rw [hf_desc x]
        have hdotE :
            ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x : ℝ) : EReal)) ≤
              ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x↓ : ℝ) : EReal)) := by
          simpa [dotProductEquiv, dotProduct_comm] using (show
            dotProduct x (symmetric_eigenvalue_function Y) ≤
              dotProduct x↓ (symmetric_eigenvalue_function Y) from hdot)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_le_add_left hdotE (-f (x↓))
      have htrace :
          Matrix.trace (((U : Mₙ) * Matrix.diagonal (x↓) * (U : Mₙ)ᵀ) * (Y : Mₙ)) =
            dotProduct (x↓) (symmetric_eigenvalue_function Y) :=
        trace_orthogonal_diagonal_mul_eq_dotProduct_symmetric_eigenvalue_function U Y hY (x↓)
      have hspec :
          symmetric_eigenvalue_function Z = x↓ :=
        orthogonal_diagonal_symmetric_eigenvalue_function_eq_of_antitone U (x↓)
          (antitone_descendingRearrangement x)
      have hpair :
          ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) (x↓) : ℝ) : EReal)) =
            (((toDualMap ℝ 𝕊 Y : Module.Dual ℝ 𝕊) Z : ℝ) : EReal) := by
        rw [toDualMap_apply_eq_trace_mul Z Y, htrace]
        simp [dotProductEquiv, dotProduct_comm]
      -- Realize the sorted vector witness by an orthogonal conjugate of a diagonal matrix.
      calc
        ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x : ℝ) : EReal) - f x)
          ≤ ((((dotProductEquiv ℝ (Fin n) (symmetric_eigenvalue_function Y)) x↓ : ℝ) : EReal) -
              f (x↓)) := hsort
        _ = (((toDualMap ℝ 𝕊 Y : Module.Dual ℝ 𝕊) Z : ℝ) : EReal) -
              f (symmetric_eigenvalue_function Z) := by
              rw [hpair, ← hspec]
        _ ≤ sSup (Set.range fun X : 𝕊 ↦
              (((toDualMap ℝ 𝕊 Y : Module.Dual ℝ 𝕊) X : ℝ) : EReal) -
                f (symmetric_eigenvalue_function X)) := by
              exact le_sSup (Set.mem_range_self Z)

end
