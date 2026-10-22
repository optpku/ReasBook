/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_12

-- Semantic recall: `det_ne_zero_of_sum_row_lt_diag` in
-- `Mathlib.LinearAlgebra.Matrix.Gershgorin` provides the canonical strict
-- diagonal-dominance input, and the irreducible branch reuses the
-- source-facing owner `Matrix.IsIrreduciblyDiagonallyDominant` from
-- Definition 1.2.12.

namespace Matrix

variable {n : ℕ}

/-- Helper for Chapter01 Theorem 1.2.13: the maximum absolute value of a vector indexed by
`Fin n`. This is the scalar used in the textbook singular-kernel contradiction. -/
noncomputable def maxAbs [Nonempty (Fin n)] (v : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |v i|

/-- Helper for Chapter01 Theorem 1.2.13: the indices where a vector attains its maximum absolute
value. This is the candidate reducibility subset in the irreducible branch. -/
noncomputable def maxAbsIndexSet [Nonempty (Fin n)] (v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => |v i| = maxAbs v

/-- Helper for Chapter01 Theorem 1.2.13: some index attains the maximum absolute value. -/
lemma maxAbsIndexSet_nonempty [Nonempty (Fin n)] (v : Fin n → ℝ) :
    (maxAbsIndexSet v).Nonempty := by
  classical
  -- Choose an index where the finite set of absolute values attains its supremum.
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => |v j|
  refine ⟨i, ?_⟩
  simp [maxAbsIndexSet, maxAbs, hi]

/-- Helper for Chapter01 Theorem 1.2.13: every coordinate is bounded by the maximal absolute
value. -/
lemma abs_le_maxAbs [Nonempty (Fin n)] (v : Fin n → ℝ) (i : Fin n) :
    |v i| ≤ maxAbs v := by
  -- This is the defining upper-bound property of the finite supremum.
  simpa [maxAbs] using Finset.le_sup' (f := fun j => |v j|) (Finset.mem_univ i)

/-- Helper for Chapter01 Theorem 1.2.13: a nonzero vector has positive maximum absolute value. -/
lemma maxAbs_pos_of_ne_zero [Nonempty (Fin n)] {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < maxAbs v := by
  classical
  -- A nonzero coordinate gives a positive lower bound on the maximal absolute value.
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    have hi' : ¬ v i ≠ 0 := by
      exact fun hvi => h ⟨i, hvi⟩
    simpa using hi'
  exact lt_of_lt_of_le (abs_pos.mpr hi) (abs_le_maxAbs v i)

/-- Helper for Chapter01 Theorem 1.2.13: a strictly diagonally dominant real matrix has nonzero
determinant by the Gershgorin determinant criterion. -/
lemma det_ne_zero_of_isStrictlyDiagonallyDominant
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsStrictlyDiagonallyDominant) :
    A.det ≠ 0 := by
  -- The strict row inequalities are exactly the hypotheses of mathlib's Gershgorin lemma.
  simpa [Matrix.IsStrictlyDiagonallyDominant, Real.norm_eq_abs] using
    (det_ne_zero_of_sum_row_lt_diag (A := A) hA)

/-- Helper for Chapter01 Theorem 1.2.13: a kernel vector row equation at an index of maximal
absolute value forces the diagonal term to be bounded by the weighted off-diagonal sum. -/
lemma row_kernel_bound_of_mem_maxAbsIndexSet [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hAv : A *ᵥ v = 0)
    {k : Fin n} (hk : k ∈ maxAbsIndexSet v) :
    |A k k| * maxAbs v ≤ ∑ j ∈ Finset.univ.erase k, |A k j| * |v j| := by
  -- Evaluate the kernel equation in row `k` and isolate the diagonal summand.
  have hrow : ∑ j, A k j * v j = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hAv k
  have hsplit : A k k * v k + ∑ j ∈ Finset.univ.erase k, A k j * v j = 0 := by
    simpa [Finset.add_sum_erase _ (fun j => A k j * v j) (Finset.mem_univ k)] using hrow
  have hdiag : A k k * v k = -∑ j ∈ Finset.univ.erase k, A k j * v j :=
    (add_eq_zero_iff_eq_neg).mp hsplit
  have hkabs : |v k| = maxAbs v := by
    simpa [maxAbsIndexSet] using hk
  -- Taking absolute values and the triangle inequality gives the desired bound.
  calc
    |A k k| * maxAbs v = |A k k * v k| := by rw [abs_mul, hkabs]
    _ = |∑ j ∈ Finset.univ.erase k, A k j * v j| := by rw [hdiag, abs_neg]
    _ ≤ ∑ j ∈ Finset.univ.erase k, |A k j * v j| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (fun j => A k j * v j) (Finset.univ.erase k))
    _ = ∑ j ∈ Finset.univ.erase k, |A k j| * |v j| := by
      simp [abs_mul]

/-- Helper for Chapter01 Theorem 1.2.13: outside the maximal-absolute-value index set, every
entry in a diagonally dominant kernel row coming from that maximal set must vanish. -/
lemma zero_entry_of_mem_maxAbsIndexSet [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hDiag : A.IsDiagonallyDominant)
    (hv0 : v ≠ 0) (hAv : A *ᵥ v = 0) {k j : Fin n} (hk : k ∈ maxAbsIndexSet v)
    (hj : j ∉ maxAbsIndexSet v) :
    A k j = 0 := by
  by_contra hkj
  have hmax_pos : 0 < maxAbs v := maxAbs_pos_of_ne_zero hv0
  have hrow :=
    row_kernel_bound_of_mem_maxAbsIndexSet A v hAv hk
  have hjk : j ≠ k := by
    intro hEq
    apply hj
    simpa [hEq] using hk
  have hj_lt : |v j| < maxAbs v := by
    refine lt_of_le_of_ne (abs_le_maxAbs v j) ?_
    simpa [maxAbsIndexSet] using hj
  have hsum_lt :
      ∑ l ∈ Finset.univ.erase k, |A k l| * |v l| <
        ∑ l ∈ Finset.univ.erase k, |A k l| * maxAbs v := by
    -- The `j`-summand is strictly smaller while every other summand is bounded by `maxAbs v`.
    refine Finset.sum_lt_sum ?_ ?_
    · intro l hl
      exact mul_le_mul_of_nonneg_left (abs_le_maxAbs v l) (abs_nonneg _)
    · refine ⟨j, by simp [hjk], ?_⟩
      exact mul_lt_mul_of_pos_left hj_lt (abs_pos.mpr hkj)
  have hdiag_mul :
      ∑ l ∈ Finset.univ.erase k, |A k l| * maxAbs v ≤ |A k k| * maxAbs v := by
    -- Multiply the diagonal-dominance inequality by the positive maximal modulus.
    calc
      ∑ l ∈ Finset.univ.erase k, |A k l| * maxAbs v =
          (∑ l ∈ Finset.univ.erase k, |A k l|) * maxAbs v := by
            rw [Finset.sum_mul]
      _ ≤ |A k k| * maxAbs v :=
        mul_le_mul_of_nonneg_right (hDiag k) (le_of_lt hmax_pos)
  -- The row bound and diagonal dominance now contradict the strict summand gap.
  exact (lt_irrefl (|A k k| * maxAbs v))
    (lt_of_le_of_lt hrow (lt_of_lt_of_le hsum_lt hdiag_mul))

/-- Helper for Chapter01 Theorem 1.2.13: a row with strict diagonal dominance cannot lie in the
maximal-absolute-value index set of a nonzero kernel vector. -/
lemma strict_row_not_mem_maxAbsIndexSet [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (hv0 : v ≠ 0) (hAv : A *ᵥ v = 0)
    {i : Fin n} (hstrict : ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) :
    i ∉ maxAbsIndexSet v := by
  intro hi
  have hmax_pos : 0 < maxAbs v := maxAbs_pos_of_ne_zero hv0
  have hrow :=
    row_kernel_bound_of_mem_maxAbsIndexSet A v hAv hi
  have hsum_le :
      ∑ j ∈ Finset.univ.erase i, |A i j| * |v j| ≤
        ∑ j ∈ Finset.univ.erase i, |A i j| * maxAbs v := by
    -- Replace each `|v j|` by the common upper bound `maxAbs v`.
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (abs_le_maxAbs v j) (abs_nonneg _)
  have hstrict_mul :
      ∑ j ∈ Finset.univ.erase i, |A i j| * maxAbs v < |A i i| * maxAbs v := by
    -- The strict row inequality survives multiplication by the positive maximal modulus.
    calc
      ∑ j ∈ Finset.univ.erase i, |A i j| * maxAbs v =
          (∑ j ∈ Finset.univ.erase i, |A i j|) * maxAbs v := by
            rw [Finset.sum_mul]
      _ < |A i i| * maxAbs v := mul_lt_mul_of_pos_right hstrict hmax_pos
  -- Chaining the three inequalities produces the impossible strict self-inequality.
  exact (lt_irrefl (|A i i| * maxAbs v))
    (lt_of_le_of_lt hrow (lt_of_le_of_lt hsum_le hstrict_mul))

/-- Helper for Chapter01 Theorem 1.2.13: if a real matrix is diagonally dominant, has at least
one strict row, and has zero determinant, then the maximal-absolute-value kernel-vector argument
produces a reducibility witness. -/
lemma isSubsetReducible_of_diagonallyDominant_exists_strict_row_det_eq_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (hDiag : A.IsDiagonallyDominant)
    (hStrict : ∃ i : Fin n, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) (hdet : A.det = 0) :
    A.IsSubsetReducible := by
  classical
  obtain ⟨i0, hi0_strict⟩ := hStrict
  let _ : Nonempty (Fin n) := ⟨i0⟩
  obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let J : Finset (Fin n) := maxAbsIndexSet v
  have hJ_nonempty : J.Nonempty := by
    -- A finite maximum is attained, so the candidate subset is nonempty.
    simpa [J] using maxAbsIndexSet_nonempty v
  have hi0_not_mem : i0 ∉ J := by
    -- The strict row witness proves that `J` is a proper subset.
    simpa [J] using strict_row_not_mem_maxAbsIndexSet A v hv0 hAv hi0_strict
  have hJ_ssubset : J ⊂ Finset.univ := by
    refine ⟨?_, ?_⟩
    · intro x hx
      simp
    · intro hsubset_rev
      exact hi0_not_mem (hsubset_rev (by simp))
  have hJ_card : J.card < Fintype.card (Fin n) := by
    -- Proper containment in `Finset.univ` gives the needed cardinal bound.
    simpa [J] using Finset.card_lt_card hJ_ssubset
  refine ⟨J, hJ_nonempty, hJ_card, ?_⟩
  intro k j hk hj
  -- Closure of `J` under outgoing nonzero edges is the core maximal-modulus lemma.
  exact zero_entry_of_mem_maxAbsIndexSet A v hDiag hv0 hAv (by simpa [J] using hk)
    (by simpa [J] using hj)

/-- Chapter01 Theorem 1.2.13 (Diagonal Dominant Theorem): if a real square matrix is either
strictly diagonally dominant or irreducibly diagonally dominant, then it is invertible. The
canonical Lean surface for matrix invertibility is `IsUnit A`. -/
theorem isUnit_of_isStrictlyDiagonallyDominant_or_isIrreduciblyDiagonallyDominant
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsStrictlyDiagonallyDominant ∨ A.IsIrreduciblyDiagonallyDominant) :
    IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rcases hA with hA | hA
  · -- The strict branch closes immediately once the determinant is known to be nonzero.
    exact isUnit_iff_ne_zero.mpr (det_ne_zero_of_isStrictlyDiagonallyDominant A hA)
  · by_cases hEmpty : IsEmpty (Fin n)
    · -- In the empty-index case the irreducible hypothesis is impossible because no strict row
      -- exists.
      classical
      obtain ⟨i, _⟩ := hA.exists_strict_row
      exact (hEmpty.false i).elim
    · -- The irreducible branch reduces to ruling out determinant zero by the source subset
      -- reducibility contradiction.
      have hdet : A.det ≠ 0 := by
        intro hdet
        exact hA.isIrreducible
          (isSubsetReducible_of_diagonallyDominant_exists_strict_row_det_eq_zero
            A hA.isDiagonallyDominant hA.exists_strict_row hdet)
      exact isUnit_iff_ne_zero.mpr hdet

end Matrix
