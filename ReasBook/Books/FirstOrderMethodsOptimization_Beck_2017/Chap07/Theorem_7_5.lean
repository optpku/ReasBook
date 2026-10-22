/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_29
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_9
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Matrix Function

noncomputable section

section

variable {m n : ℕ}

local notation "𝕄" => Matrix (Fin m) (Fin n) ℝ

/-- The ambient real matrix space is equipped with its Frobenius norm. -/
local instance instTheorem75NormedAddCommGroupMatrix : NormedAddCommGroup 𝕄 :=
  Matrix.frobeniusNormedAddCommGroup

/-- The ambient real matrix space is a normed real vector space. -/
local instance instTheorem75NormedSpaceMatrix : NormedSpace ℝ 𝕄 :=
  Matrix.frobeniusNormedSpace

/-- The ambient real matrix space is equipped with its Frobenius inner product. -/
local instance instTheorem75InnerProductSpaceMatrix : InnerProductSpace ℝ 𝕄 :=
  Matrix.frobeniusInnerProductSpace

/-- Helper for Theorem 7.5: the rectangular diagonal matrix with diagonal entries `x` and zero
off-diagonal entries. -/
def rectangularDiagonalProfile (x : Fin (min m n) → ℝ) : 𝕄 :=
  fun i j ↦
    if h : i.1 = j.1 then
      x ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
    else 0

/-- Helper for Theorem 7.5: evaluating `rectangularDiagonalProfile x` picks out the corresponding
diagonal coordinate of `x` and vanishes off the common diagonal. -/
theorem rectangularDiagonalProfile_apply (x : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) :
    rectangularDiagonalProfile x i j =
      if h : i.1 = j.1 then
        x ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩
      else 0 := by
  -- This is the defining evaluation rule for the local rectangular diagonal model.
  rfl

/-- Helper for Theorem 7.5: applying the same orthogonal singular-vector factors to the local
rectangular diagonal profile. -/
def orthogonalRectangularDiagonalProfileMap
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Fin (min m n) → ℝ) → 𝕄 :=
  fun x ↦
    (U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile x *
      ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)

/-- Helper for Theorem 7.5: evaluating the orthogonal rectangular diagonal profile map gives the
matrix product `U * rectangularDiagonalProfile x * Vᵀ`. -/
@[simp] theorem orthogonalRectangularDiagonalProfileMap_apply
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalProfileMap U V x =
      (U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile x *
        ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
  -- This is the defining evaluation rule for the orthogonal lift of the diagonal profile.
  rfl

/-- Helper for Theorem 7.5: the Gram matrix of `rectangularDiagonalProfile x` is diagonal with the
squared diagonal entries of `x` followed by zeros. -/
theorem rectangularDiagonalProfile_conjTranspose_mul_eq_squared_tail
    (x : Fin (min m n) → ℝ) :
    (rectangularDiagonalProfile x)ᴴ * rectangularDiagonalProfile x =
      Matrix.diagonal
        (fun j : Fin n ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0) := by
  classical
  -- Compute the Gram matrix entrywise by isolating the unique common diagonal term.
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.mul_apply]
    by_cases hi : i.1 < m
    · let ii : Fin m := ⟨i.1, hi⟩
      rw [Fintype.sum_eq_single ii]
      · -- On the diagonal, the surviving term is the square of the corresponding diagonal entry.
        have hmin : i.1 < min m n := Nat.lt_min.mpr ⟨hi, i.2⟩
        rw [Matrix.diagonal_apply, if_pos rfl]
        simpa [hmin, pow_two, rectangularDiagonalProfile, ii]
      · intro k hk
        -- Away from the matching row index, the summand is zero.
        have hk' : k.1 ≠ i.1 := by
          intro hki
          apply hk
          ext
          exact hki
        simp [rectangularDiagonalProfile, hk']
    · have hk' : ∀ k : Fin m, k.1 ≠ i.1 := by
        intro k hki
        exact hi (hki ▸ k.2)
      have hsum :
          (∑ k : Fin m,
              ((rectangularDiagonalProfile x)ᴴ i k) * rectangularDiagonalProfile x k i) = 0 := by
        -- If the row index lies past `m`, every entry in the `i`-th column is zero.
        apply Fintype.sum_eq_zero
        intro k
        simp [rectangularDiagonalProfile, hk' k]
      have hmin : ¬ i.1 < min m n := by
        intro h
        exact hi (Nat.lt_of_lt_of_le h (Nat.min_le_left _ _))
      rw [Matrix.diagonal_apply, if_pos rfl]
      simpa [hmin] using hsum
  · rw [Matrix.diagonal_apply]
    have hmul : (((rectangularDiagonalProfile x)ᴴ * rectangularDiagonalProfile x) i j) = 0 := by
      rw [Matrix.mul_apply]
      by_cases hi : i.1 < m
      · let ii : Fin m := ⟨i.1, hi⟩
        rw [Fintype.sum_eq_single ii]
        · -- Off the diagonal, the surviving term vanishes because the column indices differ.
          have hij' : ii.1 ≠ j.1 := by
            intro h
            apply hij
            ext
            simpa [ii] using h
          simp [rectangularDiagonalProfile, hij']
        · intro k hk
          have hk' : k.1 ≠ i.1 := by
            intro hki
            apply hk
            ext
            exact hki
          simp [rectangularDiagonalProfile, hk']
      · have hk' : ∀ k : Fin m, k.1 ≠ i.1 := by
          intro k hki
          exact hi (hki ▸ k.2)
        have hsum :
            (∑ k : Fin m,
                ((rectangularDiagonalProfile x)ᴴ i k) * rectangularDiagonalProfile x k j) = 0 := by
          -- Again, if the would-be matching row is unavailable, every summand is zero.
          apply Fintype.sum_eq_zero
          intro k
          simp [rectangularDiagonalProfile, hk' k]
        simpa using hsum
    rw [if_neg hij]
    exact hmul

/-- Helper for Theorem 7.5: squaring a nonnegative antitone diagonal profile and appending zeros
preserves antitonicity. -/
theorem squared_tail_antitone_rectangularProfile (x : Fin (min m n) → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_antitone : Antitone x) :
    Antitone (fun j : Fin n ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0) := by
  -- Compare either two genuine diagonal entries or a diagonal entry with the zero tail.
  intro i j hij
  by_cases hi : i.1 < min m n
  · by_cases hj : j.1 < min m n
    · have hxj : 0 ≤ x ⟨j.1, hj⟩ := hx_nonneg _
      have hle : x ⟨j.1, hj⟩ ≤ x ⟨i.1, hi⟩ := hx_antitone (by simpa using hij)
      have hsquare : x ⟨j.1, hj⟩ ^ 2 ≤ x ⟨i.1, hi⟩ ^ 2 := pow_le_pow_left₀ hxj hle 2
      simpa only [hi, hj] using hsquare
    · have hxi : 0 ≤ x ⟨i.1, hi⟩ := hx_nonneg _
      simpa only [hi, hj] using sq_nonneg (x ⟨i.1, hi⟩)
  · have hj : ¬ j.1 < min m n := by
      intro hj
      exact hi (lt_of_le_of_lt (show i.1 ≤ j.1 by simpa using hij) hj)
    simp [hi, hj]

/-- Helper for Theorem 7.5: a real diagonal matrix with antitone diagonal entries has ordered
eigenvalue list equal to that diagonal. -/
theorem diagonal_eigenvalues_zero_indexed_eq_rectangularProfile
    (y : Fin n → ℝ) (hy : Antitone y) :
    let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal y
    let hA : A.IsHermitian := by simp [A]
    hA.eigenvalues₀ = fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal y
  let hA : A.IsHermitian := by
    simp [A]
  have hcast_anti :
      Antitone (fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j)) := by
    -- Transport antitonicity across the standard `Fin.cast` reindexing.
    simpa using hy.comp_monotone
      (show Monotone (fun j : Fin (Fintype.card (Fin n)) ↦ Fin.cast (by simp) j) by
        intro a b hab
        simpa using hab)
  have hroots :
      A.charpoly.roots =
        Multiset.map
          (RCLike.ofReal ∘ fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j))
          Finset.univ.val := by
    -- The characteristic polynomial of a diagonal matrix factors into the diagonal linear terms.
    rw [show A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (y i)) by
      simpa [A] using Matrix.charpoly_diagonal y]
    rw [Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort :
      (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) =
        List.ofFn (fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j)) := by
    -- Both sides are the decreasing sort of the same real root multiset.
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hcast_anti.sortedGE_ofFn
  exact List.ofFn_inj.1 (hA.sort_roots_charpoly_eq_eigenvalues₀.symm.trans hsort)

/-- Helper for Theorem 7.5: a nonnegative antitone rectangular diagonal profile is exactly the
ordered singular-value vector of its diagonal matrix realization. -/
theorem singular_value_function_rectangularDiagonalProfile_eq_of_nonneg_antitone
    (x : Fin (min m n) → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (hx_antitone : Antitone x) :
    singular_value_function (rectangularDiagonalProfile x) = x := by
  let y : Fin n → ℝ := fun j ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0
  have hgram : (rectangularDiagonalProfile x)ᴴ * rectangularDiagonalProfile x = Matrix.diagonal y := by
    -- The Gram matrix is diagonal with squared diagonal entries and a zero tail.
    simpa [y] using rectangularDiagonalProfile_conjTranspose_mul_eq_squared_tail (m := m) (n := n) x
  have hy_antitone : Antitone y :=
    squared_tail_antitone_rectangularProfile x hx_nonneg hx_antitone
  have hy_hermitian : (Matrix.diagonal y).IsHermitian := by
    simp
  have hdiag_eigs :
      ((Matrix.isSymmetric_toEuclideanLin_iff).2 hy_hermitian).eigenvalues finrank_euclideanSpace =
        fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
    -- The ordered eigenvalues of the diagonal Gram matrix are exactly its diagonal entries.
    simpa [Matrix.IsHermitian.eigenvalues₀] using
      diagonal_eigenvalues_zero_indexed_eq_rectangularProfile (n := n) y hy_antitone
  ext i
  have hi_n : (i : ℕ) < n := lt_of_lt_of_le i.2 (Nat.min_le_right _ _)
  have hsquare : (singular_value_function (rectangularDiagonalProfile x) i) ^ 2 = x i ^ 2 := by
    have hgram' : (rectangularDiagonalProfile x)ᵀ * rectangularDiagonalProfile x = Matrix.diagonal y := by
      simpa using hgram
    have hcomp :
        LinearMap.adjoint (Matrix.toEuclideanLin (rectangularDiagonalProfile x)) ∘ₗ
            Matrix.toEuclideanLin (rectangularDiagonalProfile x) =
          Matrix.toEuclideanLin (Matrix.diagonal y) := by
      -- Translate the Gram matrix identity from matrices to Euclidean linear maps.
      rw [show LinearMap.adjoint (Matrix.toEuclideanLin (rectangularDiagonalProfile x)) =
          Matrix.toEuclideanLin ((rectangularDiagonalProfile x)ᴴ) by
        simpa using
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := rectangularDiagonalProfile x)).symm]
      ext v j
      simpa [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hgram'] using
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ (M *ᵥ v.ofLp) j) hgram'
    have hsq :
        (Matrix.toEuclideanLin (rectangularDiagonalProfile x)).singularValues i ^ 2 =
          ((Matrix.isSymmetric_toEuclideanLin_iff).2 hy_hermitian).eigenvalues
            finrank_euclideanSpace ⟨i.1, by simpa using hi_n⟩ := by
      -- Singular values are the square roots of the ordered eigenvalues of the Gram operator.
      simpa [hcomp] using
        (LinearMap.sq_singularValues_of_lt
          (T := Matrix.toEuclideanLin (rectangularDiagonalProfile x))
          (hn := finrank_euclideanSpace) (i := i.1) (by simpa using hi_n))
    rw [singular_value_function_apply]
    rw [hsq, hdiag_eigs]
    have hyi : y ⟨i.1, by simpa using hi_n⟩ = x i ^ 2 := by
      dsimp [y]
      rw [if_pos i.2]
    simpa [hyi]
  have hσ_nonneg : 0 ≤ singular_value_function (rectangularDiagonalProfile x) i :=
    singular_value_function_nonneg (rectangularDiagonalProfile x) i
  have hx_i_nonneg : 0 ≤ x i := hx_nonneg i
  -- Nonnegative numbers with the same square are equal.
  nlinarith

/-- Helper for Theorem 7.5: the chapter's `Function.descendingRearrangement` agrees with the
earlier tuple-sorting `x↓` notation from Chapter 7. -/
lemma function_descendingRearrangement_eq_descendingRearrangement
    (x : Fin (min m n) → ℝ) :
    Function.descendingRearrangement x = descendingRearrangement x := by
  have hfun_antitone : Antitone (Function.descendingRearrangement x) := by
    let L := (List.ofFn x).mergeSort (· ≥ ·)
    have hpair : L.Pairwise (fun a b : ℝ ↦ a ≥ b) := by
      simpa [L] using
        (List.pairwise_mergeSort' (r := fun a b : ℝ ↦ a ≥ b) (List.ofFn x))
    have hanti_get : Antitone L.get := hpair.sortedGE.antitone_get
    intro i j hij
    have hiL : i.1 < L.length := by
      simpa [L] using i.2
    have hjL : j.1 < L.length := by
      simpa [L] using j.2
    rw [show Function.descendingRearrangement x i = L.get ⟨i.1, hiL⟩ by
      rw [Function.descendingRearrangement_apply]
      simpa [L] using (List.getD_eq_get L 0 ⟨i.1, hiL⟩)]
    rw [show Function.descendingRearrangement x j = L.get ⟨j.1, hjL⟩ by
      rw [Function.descendingRearrangement_apply]
      simpa [L] using (List.getD_eq_get L 0 ⟨j.1, hjL⟩)]
    exact hanti_get (by simpa using hij)
  have hfun_multiset :
      Multiset.map (Function.descendingRearrangement x) Finset.univ.val =
        Multiset.map x Finset.univ.val := by
    have hlist :
        ((List.ofFn (Function.descendingRearrangement x) : List ℝ) : Multiset ℝ) =
          (List.ofFn x : List ℝ) := by
      rw [show List.ofFn (Function.descendingRearrangement x) =
          (List.ofFn x).mergeSort (· ≥ ·) by
        apply List.ext_get
        · simp
        · intro k hk₁ hk₂
          have hkfin : k < min m n := by
            simpa using hk₁
          rw [show
              (List.ofFn (Function.descendingRearrangement x)).get ⟨k, hk₁⟩ =
                Function.descendingRearrangement x ⟨k, hkfin⟩ by
            simp]
          rw [Function.descendingRearrangement_apply]
          have hkL : k < ((List.ofFn x).mergeSort (· ≥ ·)).length := by
            simpa using hk₂
          rw [show ((List.ofFn x).mergeSort (· ≥ ·)).getD k 0 =
              ((List.ofFn x).mergeSort (· ≥ ·)).get ⟨k, hkL⟩ by
            simpa using
              (List.getD_eq_get ((List.ofFn x).mergeSort (· ≥ ·)) 0 ⟨k, hkL⟩)]]
      exact Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _)
    simpa [Fin.univ_val_map] using hlist
  have htuple_multiset :
      Multiset.map (descendingRearrangement x) Finset.univ.val = Multiset.map x Finset.univ.val := by
    simpa [descendingRearrangement, Function.comp_assoc, Equiv.Perm.coe_mul] using
      (multiset_map_comp_perm x (Tuple.sort x * Fin.revPerm))
  exact antitone_eq_of_multiset_eq hfun_antitone (antitone_descendingRearrangement x)
    (hfun_multiset.trans htuple_multiset.symm)

/-- Helper for Theorem 7.5: the chapter's `Function.descendingRearrangement` is antitone. -/
lemma antitone_function_descendingRearrangement (x : Fin (min m n) → ℝ) :
    Antitone (Function.descendingRearrangement x) := by
  rw [function_descendingRearrangement_eq_descendingRearrangement x]
  exact antitone_descendingRearrangement x

/-- Helper for Theorem 7.5: against an antitone target vector, sorting the other vector in
decreasing order can only increase the dot product. -/
lemma dotProduct_le_dotProduct_function_descendingRearrangement
    (x y : Fin (min m n) → ℝ) (hy : Antitone y) :
    dotProduct x y ≤ dotProduct (Function.descendingRearrangement x) y := by
  rw [function_descendingRearrangement_eq_descendingRearrangement x]
  exact dotProduct_le_dotProduct_descendingRearrangement x y hy

/-- Helper for Theorem 7.5: the Frobenius inner product on real rectangular matrices is the
entrywise double sum. -/
lemma matrix_inner_eq_sum_mul_rectangular (A B : 𝕄) :
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

/-- Helper for Theorem 7.5: the Frobenius Riesz pairing on `ℝ^(m × n)` is the trace pairing
`Tr(XᵀY)`. -/
lemma toDualMap_apply_eq_trace_transpose_mul (X Y : 𝕄) :
    ((↑(toDualMap ℝ 𝕄 Y) : Module.Dual ℝ 𝕄) X) = Matrix.trace (Xᵀ * Y) := by
  -- Move from the Riesz map to the ambient Frobenius inner product and then rewrite the sum.
  change ⟪Y, X⟫_ℝ = Matrix.trace (Xᵀ * Y)
  calc
    ⟪Y, X⟫_ℝ = ∑ i, ∑ j, Y i j * X i j := by
      rw [matrix_inner_eq_sum_mul_rectangular]
    _ = ∑ i, ∑ j, X i j * Y i j := by
      simp_rw [mul_comm]
    _ = Matrix.trace (Xᵀ * Y) := by
      symm
      exact trace_transpose_mul_eq_sum_entrywise_mul X Y

/-- Helper for Theorem 7.5: the rectangular diagonal singular-value matrix from Theorem 7.4 is
the local rectangular diagonal profile applied to `singular_value_function`. -/
lemma singular_value_diagonal_matrix_eq_rectangularDiagonal_singular_value_function
    (Y : 𝕄) :
    singular_value_diagonal_matrix Y = rectangularDiagonalProfile (singular_value_function Y) := by
  -- Both source-facing diagonal matrices are defined by the same entrywise formula.
  ext i j
  simp [singular_value_diagonal_matrix, rectangularDiagonalProfile]

/-- Helper for Theorem 7.5: every real rectangular matrix admits an orthogonal diagonalization
whose rectangular diagonal is exactly its singular-value vector. -/
lemma exists_orthogonal_rectangular_diagonalization_with_singular_value_function
    (Y : 𝕄) :
    ∃ U : Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
        Y = orthogonalRectangularDiagonalProfileMap U V (singular_value_function Y) := by
  have hself :
      Matrix.trace (Yᵀ * Y) =
        dotProduct (singular_value_function Y) (singular_value_function Y) :=
    trace_transpose_mul_eq_dotProduct_singular_value_function Y
  rcases
      (von_neumann_trace_inequality_eq_iff Y Y).1 hself with
    ⟨U, V, hY, _⟩
  refine ⟨U, V, ?_⟩
  -- Equality in the self-pairing case gives the ordered singular-value decomposition of `Y`.
  calc
    Y = (U : Matrix (Fin m) (Fin m) ℝ) * singular_value_diagonal_matrix Y *
          ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := hY
    _ = orthogonalRectangularDiagonalProfileMap U V (singular_value_function Y) := by
          rw [orthogonalRectangularDiagonalProfileMap_apply,
            singular_value_diagonal_matrix_eq_rectangularDiagonal_singular_value_function]

/-- Helper for Theorem 7.5: orthogonal left/right factors do not change a nonnegative antitone
rectangular diagonal singular-value profile. -/
lemma singular_value_function_orthogonalRectangularDiagonalMap_eq_of_nonneg_antitone
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (hx_antitone : Antitone x) :
    singular_value_function (orthogonalRectangularDiagonalProfileMap U V x) = x := by
  let y : Fin n → ℝ := fun j ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0
  let Z : 𝕄 := orthogonalRectangularDiagonalProfileMap U V x
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (V : Matrix (Fin n) (Fin n) ℝ) *
      (Matrix.diagonal y * ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ))
  have hDx :
      (rectangularDiagonalProfile x)ᵀ * rectangularDiagonalProfile x = Matrix.diagonal y := by
    -- The rectangular diagonal Gram matrix is the diagonal matrix of squared entries.
    simpa [y] using
      rectangularDiagonalProfile_conjTranspose_mul_eq_squared_tail (m := m) (n := n) x
  have hU :
      ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) * (U : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (U : Matrix (Fin m) (Fin m) ℝ)) (R := ℝ)).1 U.2
  have hZgram :
      Zᵀ * Z = A := by
    -- Route correction: instead of unfolding singular values directly, compute the Gram matrix of
    -- `Z = U * rectangularDiagonal x * Vᵀ` and cancel the left orthogonal factor first.
    calc
      Zᵀ * Z
        = ((V : Matrix (Fin n) (Fin n) ℝ) * (rectangularDiagonalProfile x)ᵀ *
            ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
            ((U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile x *
              ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
              simp [Z, orthogonalRectangularDiagonalProfileMap_apply, Matrix.transpose_mul,
                Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℝ) *
            (((rectangularDiagonalProfile x)ᵀ * ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
              ((U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile x)) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              simp [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℝ) *
            ((rectangularDiagonalProfile x)ᵀ *
              (((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
                ((U : Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile x))) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              simp [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℝ) *
            ((rectangularDiagonalProfile x)ᵀ *
              ((((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) * (U : Matrix (Fin m) (Fin m) ℝ)) *
                rectangularDiagonalProfile x)) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              simp [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℝ) *
            (((rectangularDiagonalProfile x)ᵀ * rectangularDiagonalProfile x)) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              rw [hU]
              simp [Matrix.mul_assoc]
      _ = A := by
              simp [A, hDx, Matrix.mul_assoc]
  have hy_antitone : Antitone y :=
    squared_tail_antitone_rectangularProfile x hx_nonneg hx_antitone
  have hA : A.IsHermitian := by
    -- Orthogonal conjugation preserves symmetry of the diagonal Gram matrix.
    rw [Matrix.IsHermitian]
    simp [A, Matrix.transpose_mul, Matrix.mul_assoc]
  have hD : (Matrix.diagonal y).IsHermitian := by
    simp
  have hchar : Matrix.charpoly A = Matrix.charpoly (Matrix.diagonal y) := by
    -- The Gram matrix is orthogonally conjugate to the diagonal model.
    simpa [A, Matrix.mul_assoc] using orthogonal_conjugate_diagonal_charpoly V y
  have hA_eigenvalues₀ :
      hA.eigenvalues₀ = fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
    have heig0 : hA.eigenvalues₀ = hD.eigenvalues₀ := by
      -- The ordered Hermitian spectrum depends only on the characteristic polynomial.
      simp_rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀,
        ← hD.sort_roots_charpoly_eq_eigenvalues₀, hchar]
    have hdiag :
        hD.eigenvalues₀ = fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
      simpa [Matrix.IsHermitian.eigenvalues₀] using
        diagonal_eigenvalues_zero_indexed_eq_rectangularProfile (n := n) y hy_antitone
    exact heig0.trans hdiag
  have hA_eigenvalues :
      ((Matrix.isSymmetric_toEuclideanLin_iff).2 hA).eigenvalues finrank_euclideanSpace =
        fun j : Fin (Fintype.card (Fin n)) ↦ y (Fin.cast (by simp) j) := by
    -- Transfer the zero-indexed Hermitian eigenvalue description to the Euclidean-linear-map API.
    simpa [Matrix.IsHermitian.eigenvalues₀] using hA_eigenvalues₀
  ext i
  have hi_n : (i : ℕ) < n := lt_of_lt_of_le i.2 (Nat.min_le_right _ _)
  have hsquare : (singular_value_function Z i) ^ 2 = x i ^ 2 := by
    have hcomp :
        LinearMap.adjoint (Matrix.toEuclideanLin Z) ∘ₗ Matrix.toEuclideanLin Z =
          Matrix.toEuclideanLin A := by
      -- Translate the matrix Gram identity to the Euclidean linear map `Z.toEuclideanLin`.
      rw [show LinearMap.adjoint (Matrix.toEuclideanLin Z) = Matrix.toEuclideanLin (Zᵀ) by
        simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := Z)).symm]
      ext v j
      simpa [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, A] using
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ (M *ᵥ v.ofLp) j) hZgram
    have hsq :
        (Matrix.toEuclideanLin Z).singularValues i ^ 2 =
          ((Matrix.isSymmetric_toEuclideanLin_iff).2 hA).eigenvalues
            finrank_euclideanSpace ⟨i.1, by simpa using hi_n⟩ := by
      -- Singular values are square roots of the ordered Gram eigenvalues.
      simpa [hcomp] using
        (LinearMap.sq_singularValues_of_lt
          (T := Matrix.toEuclideanLin Z)
          (hn := finrank_euclideanSpace) (i := i.1) (by simpa using hi_n))
    rw [singular_value_function_apply]
    rw [hsq, hA_eigenvalues]
    have hyi : y ⟨i.1, by simpa using hi_n⟩ = x i ^ 2 := by
      dsimp [y]
      rw [if_pos i.2]
    simpa [hyi]
  have hσ_nonneg : 0 ≤ singular_value_function Z i := singular_value_function_nonneg Z i
  have hx_i_nonneg : 0 ≤ x i := hx_nonneg i
  -- Nonnegative numbers with the same square are equal.
  nlinarith

/-- Helper for Theorem 7.5: once `Y` is written in ordered singular-value coordinates, pairing it
with another matrix sharing the same orthogonal factors reduces to the Euclidean dot product of
the two diagonal profiles. -/
lemma trace_orthogonalRectangularDiagonalMap_transpose_mul_eq_dotProduct_of_nonneg_antitone
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ) (Y : 𝕄)
    (hY : Y = orthogonalRectangularDiagonalProfileMap U V (singular_value_function Y))
    (x : Fin (min m n) → ℝ) (hx_nonneg : ∀ i, 0 ≤ x i) (hx_antitone : Antitone x) :
    Matrix.trace ((orthogonalRectangularDiagonalProfileMap U V x)ᵀ * Y) =
      dotProduct x (singular_value_function Y) := by
  have hV :
      ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) * (V : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (V : Matrix (Fin n) (Fin n) ℝ)) (R := ℝ)).1 V.2
  have hU :
      ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) * (U : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := (U : Matrix (Fin m) (Fin m) ℝ)) (R := ℝ)).1 U.2
  have hxσ :
      singular_value_function (rectangularDiagonalProfile x) = x :=
    singular_value_function_rectangularDiagonalProfile_eq_of_nonneg_antitone
      x hx_nonneg hx_antitone
  have hσYdiag :
      singular_value_function (rectangularDiagonalProfile (singular_value_function Y)) =
        singular_value_function Y := by
    -- The singular values of the diagonal model of `σ(Y)` are exactly `σ(Y)` again.
    exact singular_value_function_rectangularDiagonalProfile_eq_of_nonneg_antitone
      (singular_value_function Y) (singular_value_function_nonneg Y)
      (singular_value_function_antitone Y)
  have hDx :
      singular_value_diagonal_matrix (rectangularDiagonalProfile x) =
        rectangularDiagonalProfile x := by
    -- Rewrite the imported singular-value diagonal through the already identified profile `x`.
    simpa [hxσ] using
      singular_value_diagonal_matrix_eq_rectangularDiagonal_singular_value_function
        (rectangularDiagonalProfile x)
  have hDY :
      singular_value_diagonal_matrix (rectangularDiagonalProfile (singular_value_function Y)) =
        rectangularDiagonalProfile (singular_value_function Y) := by
    -- The same identification applies to the diagonal model of `σ(Y)`.
    simpa [hσYdiag] using
      singular_value_diagonal_matrix_eq_rectangularDiagonal_singular_value_function
        (rectangularDiagonalProfile (singular_value_function Y))
  have hdiag :
      Matrix.trace
          ((rectangularDiagonalProfile x)ᵀ *
            rectangularDiagonalProfile (singular_value_function Y)) =
        dotProduct x (singular_value_function Y) := by
    -- The diagonal pairing is exactly Theorem 7.4's singular-value trace formula.
    calc
      Matrix.trace
          ((rectangularDiagonalProfile x)ᵀ *
            rectangularDiagonalProfile (singular_value_function Y))
        = Matrix.trace
            ((singular_value_diagonal_matrix (rectangularDiagonalProfile x))ᵀ *
              singular_value_diagonal_matrix
                (rectangularDiagonalProfile (singular_value_function Y))) := by
                  rw [hDx, hDY]
      _ = dotProduct
            (singular_value_function (rectangularDiagonalProfile x))
            (singular_value_function
              (rectangularDiagonalProfile (singular_value_function Y))) := by
            exact trace_singular_value_diagonal_matrix_transpose_mul
              (rectangularDiagonalProfile x)
              (rectangularDiagonalProfile (singular_value_function Y))
      _ = dotProduct x (singular_value_function Y) := by
            rw [hxσ, hσYdiag]
  have hprod :
      ((orthogonalRectangularDiagonalProfileMap U V x)ᵀ *
          orthogonalRectangularDiagonalProfileMap U V (singular_value_function Y)) =
        (V : Matrix (Fin n) (Fin n) ℝ) *
          (((rectangularDiagonalProfile x)ᵀ) *
            rectangularDiagonalProfile (singular_value_function Y)) *
          ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
    -- After transposing the left factor, the common orthogonal matrices cancel to the diagonal core.
    calc
      ((orthogonalRectangularDiagonalProfileMap U V x)ᵀ *
          orthogonalRectangularDiagonalProfileMap U V (singular_value_function Y))
        = ((V : Matrix (Fin n) (Fin n) ℝ) * (rectangularDiagonalProfile x)ᵀ *
            ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ)) *
            ((U : Matrix (Fin m) (Fin m) ℝ) *
              rectangularDiagonalProfile (singular_value_function Y) *
              ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
              simp [orthogonalRectangularDiagonalProfileMap_apply, Matrix.transpose_mul,
                Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℝ) *
            ((rectangularDiagonalProfile x)ᵀ *
              (((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
                ((U : Matrix (Fin m) (Fin m) ℝ) *
                  rectangularDiagonalProfile (singular_value_function Y)))) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              simp [Matrix.mul_assoc]
      _ = (V : Matrix (Fin n) (Fin n) ℝ) *
            (((rectangularDiagonalProfile x)ᵀ) *
              rectangularDiagonalProfile (singular_value_function Y)) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
              rw [show
                  ((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
                      ((U : Matrix (Fin m) (Fin m) ℝ) *
                        rectangularDiagonalProfile (singular_value_function Y)) =
                    (((U : Matrix (Fin m) (Fin m) ℝ)ᵀ) *
                      (U : Matrix (Fin m) (Fin m) ℝ)) *
                      rectangularDiagonalProfile (singular_value_function Y) by
                    simp [Matrix.mul_assoc]]
              rw [hU]
              simp [Matrix.mul_assoc]
  -- Substitute the ordered singular-value decomposition of `Y`, then cycle the trace past `V`.
  calc
    Matrix.trace ((orthogonalRectangularDiagonalProfileMap U V x)ᵀ * Y)
      = Matrix.trace
          ((orthogonalRectangularDiagonalProfileMap U V x)ᵀ *
            orthogonalRectangularDiagonalProfileMap U V (singular_value_function Y)) := by
              conv_lhs => rw [hY]
    _ = Matrix.trace
          ((V : Matrix (Fin n) (Fin n) ℝ) *
            (((rectangularDiagonalProfile x)ᵀ) *
              rectangularDiagonalProfile (singular_value_function Y)) *
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
              rw [hprod]
    _ = Matrix.trace
          (((rectangularDiagonalProfile x)ᵀ) *
            rectangularDiagonalProfile (singular_value_function Y)) := by
          rw [show
              (V : Matrix (Fin n) (Fin n) ℝ) *
                  (((rectangularDiagonalProfile x)ᵀ) *
                    rectangularDiagonalProfile (singular_value_function Y)) *
                  ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) =
                ((V : Matrix (Fin n) (Fin n) ℝ) *
                    (((rectangularDiagonalProfile x)ᵀ) *
                      rectangularDiagonalProfile (singular_value_function Y))) *
                  ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ) by
                simp [Matrix.mul_assoc]]
          rw [Matrix.trace_mul_cycle
            (V : Matrix (Fin n) (Fin n) ℝ)
            ((((rectangularDiagonalProfile x)ᵀ) *
              rectangularDiagonalProfile (singular_value_function Y)))
            ((V : Matrix (Fin n) (Fin n) ℝ)ᵀ)]
          simp [hV, Matrix.mul_assoc]
    _ = dotProduct x (singular_value_function Y) := hdiag

/- Theorem 7.5 is `source-facing` in the rectangular spectral-function API. The relevant owner
declarations are Chapter 4's `conjugate_function`, Chapter 7's `singular_value_function`, and
Chapter 7's `Function.IsAbsolutelyPermutationSymmetric`. The theorem itself is the matrix analogue
of Theorem 7.2, so the canonical public surface uses the Frobenius Riesz map
`toDualMap ℝ 𝕄` rather than introducing a second matrix-side conjugate wrapper. -/

-- Proof sketch: prove the two inequalities in the textbook. For the `≤` direction, expand the
-- left-hand conjugate on `𝕄` using the Frobenius pairing from `toDualMap`, apply von Neumann's
-- trace inequality to bound `Tr(XᵀY)` by the Euclidean pairing of the singular-value vectors, and
-- then recognize the supremum as `f* (σ Y)`. For the reverse inequality, take a singular value
-- decomposition of `Y`, restrict the left-hand supremum to matrices with the same singular-vector
-- bases, and rewrite those matrices so that the singular-value term reduces to `f`.
/-- Theorem 7.5: for an absolutely permutation-symmetric extended-real-valued function `f` on
`ℝ^(min(m,n))`, the Fenchel conjugate of the spectral lift `f ∘ σ` on `ℝ^(m × n)`, viewed on the
matrix space through the Frobenius Riesz map `toDualMap ℝ 𝕄`, is the vector-side Fenchel
conjugate `f*` composed with the singular-value map `σ`. -/
theorem matrix_spectral_conjugate_formula
    (f : (Fin (min m n) → ℝ) → EReal) (hf : Function.IsAbsolutelyPermutationSymmetric f) :
    (fun Y : 𝕄 ↦ conjugate_function (f ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
      fun Y : 𝕄 ↦
        conjugate_function f
          (dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) := by
  ext Y
  rw [conjugate_function_apply, conjugate_function_apply]
  apply le_antisymm
  · refine sSup_le ?_
    rintro z ⟨X, rfl⟩
    -- Use the Frobenius/trace pairing and von Neumann's inequality, then insert `σ(X)` as a
    -- vector witness on the right-hand conjugate.
    calc
      ((((↑(toDualMap ℝ 𝕄 Y) : Module.Dual ℝ 𝕄) X : ℝ) : EReal) - f (singular_value_function X))
        = ((Matrix.trace (Xᵀ * Y) : ℝ) : EReal) - f (singular_value_function X) := by
            rw [toDualMap_apply_eq_trace_transpose_mul]
      _ ≤
          ((dotProduct (singular_value_function X) (singular_value_function Y) : ℝ) : EReal) -
            f (singular_value_function X) := by
              have hvn :
                  (((Matrix.trace (Xᵀ * Y) : ℝ) : EReal)) ≤
                    (((dotProduct (singular_value_function X)
                        (singular_value_function Y) : ℝ) : EReal)) := by
                exact_mod_cast von_neumann_trace_inequality X Y
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                add_le_add_left hvn (-f (singular_value_function X))
      _ ≤ sSup (Set.range fun x : Fin (min m n) → ℝ ↦
            (((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) x : ℝ) : EReal) -
              f x) := by
            simpa [dotProductEquiv, dotProduct_comm] using
              (le_sSup (Set.mem_range_self (singular_value_function X)) :
                ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y))
                    (singular_value_function X) : ℝ) : EReal) -
                    f (singular_value_function X)) ≤
                  sSup (Set.range fun x : Fin (min m n) → ℝ ↦
                    (((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) x : ℝ) :
                      EReal) - f x))
  · refine sSup_le ?_
    rintro z ⟨x, rfl⟩
    obtain ⟨U, V, hY⟩ :=
      exists_orthogonal_rectangular_diagonalization_with_singular_value_function Y
    let xCanon : Fin (min m n) → ℝ :=
      Function.descendingRearrangement (fun i ↦ |x i|)
    let Z : 𝕄 := orthogonalRectangularDiagonalProfileMap U V xCanon
    have hxCanon_eq :
        xCanon = Function.descendingRearrangement (fun i ↦ |x i|) := by
      rfl
    have hxCanon_nonneg : ∀ i, 0 ≤ xCanon i := by
      intro i
      -- Each coordinate of the sorted absolute-value profile is nonnegative.
      rw [show xCanon i = Function.descendingRearrangement (fun j ↦ |x j|) i by rfl]
      rw [Function.descendingRearrangement_apply]
      let L := (List.ofFn fun j : Fin (min m n) ↦ |x j|).mergeSort (· ≥ ·)
      have hiL : i.1 < L.length := by
        simpa [L] using i.2
      rw [show L.getD i 0 = L.get ⟨i.1, hiL⟩ by
        simpa [L] using (List.getD_eq_get L 0 ⟨i.1, hiL⟩)]
      have hmem_sorted : L.get ⟨i.1, hiL⟩ ∈ L := List.get_mem L ⟨i.1, hiL⟩
      have hmem_original : L.get ⟨i.1, hiL⟩ ∈ List.ofFn (fun j : Fin (min m n) ↦ |x j|) := by
        exact (List.mem_mergeSort).1 hmem_sorted
      rcases (List.mem_ofFn).1 hmem_original with ⟨j, hj⟩
      simpa [L, hj] using abs_nonneg (x j)
    have hxCanon_antitone : Antitone xCanon := by
      -- The canonical witness is the decreasing rearrangement `|x|↓`.
      rw [hxCanon_eq]
      exact antitone_function_descendingRearrangement (fun i ↦ |x i|)
    have hdot_abs :
        dotProduct x (singular_value_function Y) ≤
          dotProduct (fun i ↦ |x i|) (singular_value_function Y) := by
      -- Taking absolute values can only increase the pairing against the nonnegative vector `σ(Y)`.
      rw [dotProduct, dotProduct]
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_right (le_abs_self (x i)) (singular_value_function_nonneg Y i)
    have hdot_sort :
        dotProduct (fun i ↦ |x i|) (singular_value_function Y) ≤
          dotProduct xCanon (singular_value_function Y) := by
      -- Sorting the absolute values improves the pairing against the decreasing target `σ(Y)`.
      rw [hxCanon_eq]
      exact dotProduct_le_dotProduct_function_descendingRearrangement
        (fun i ↦ |x i|) (singular_value_function Y) (singular_value_function_antitone Y)
    have hsort :
        ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) x : ℝ) : EReal) - f x) ≤
          ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) xCanon : ℝ) : EReal) -
            f xCanon) := by
      have hdot :
          dotProduct x (singular_value_function Y) ≤
            dotProduct xCanon (singular_value_function Y) :=
        le_trans hdot_abs hdot_sort
      have hdotE :
          ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) x : ℝ) : EReal)) ≤
            ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) xCanon : ℝ) :
                EReal)) := by
        simpa [dotProductEquiv, dotProduct_comm] using hdot
      -- The linear term improves under `|x|↓`, while `f` is unchanged by absolute permutation
      -- symmetry.
      rw [show f x = f xCanon by
        simpa [xCanon] using hf.map_eq_abs_descendingRearrangement x]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        add_le_add_left hdotE (-f xCanon)
    have htrace :
        Matrix.trace (Zᵀ * Y) = dotProduct xCanon (singular_value_function Y) := by
      -- Pair the canonical witness matrix with the ordered singular-value decomposition of `Y`.
      simpa [Z] using
        trace_orthogonalRectangularDiagonalMap_transpose_mul_eq_dotProduct_of_nonneg_antitone
          U V Y hY xCanon hxCanon_nonneg hxCanon_antitone
    have hspec :
        singular_value_function Z = xCanon := by
      -- The witness matrix has singular-value profile exactly `|x|↓`.
      simpa [Z] using
        singular_value_function_orthogonalRectangularDiagonalMap_eq_of_nonneg_antitone
          U V xCanon hxCanon_nonneg hxCanon_antitone
    have hpair :
        ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) xCanon : ℝ) : EReal)) =
          (((↑(toDualMap ℝ 𝕄 Y) : Module.Dual ℝ 𝕄) Z : ℝ) : EReal) := by
      rw [toDualMap_apply_eq_trace_transpose_mul Z Y, htrace]
      simp [dotProductEquiv, dotProduct_comm]
    -- Realize the sorted absolute-value witness by a matrix sharing the singular bases of `Y`.
    calc
      ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) x : ℝ) : EReal) - f x)
        ≤ ((((dotProductEquiv ℝ (Fin (min m n)) (singular_value_function Y)) xCanon : ℝ) :
              EReal) - f xCanon) := hsort
      _ = (((↑(toDualMap ℝ 𝕄 Y) : Module.Dual ℝ 𝕄) Z : ℝ) : EReal) -
            f (singular_value_function Z) := by
              rw [hpair, ← hspec]
      _ ≤ sSup (Set.range fun X : 𝕄 ↦
            ((((↑(toDualMap ℝ 𝕄 Y) : Module.Dual ℝ 𝕄) X : ℝ) : EReal) -
              f (singular_value_function X))) := by
            exact le_sSup (Set.mem_range_self Z)

end
