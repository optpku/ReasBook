/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import Mathlib.Data.List.OfFn
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_8
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_9
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_5
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open Function Matrix
open InnerProductSpace
open scoped Function

noncomputable section

section

variable {m n : ℕ}

local notation "𝕄" => Matrix (Fin m) (Fin n) ℝ

/-- The ambient real matrix space is equipped with its Frobenius norm. -/
local instance theorem76FrobeniusNormedAddCommGroup : NormedAddCommGroup 𝕄 :=
  Matrix.frobeniusNormedAddCommGroup

/-- The ambient real matrix space is a normed real vector space. -/
local instance theorem76FrobeniusNormedSpace : NormedSpace ℝ 𝕄 :=
  Matrix.frobeniusNormedSpace

/-- The ambient real matrix space is equipped with its Frobenius inner product. -/
local instance theorem76FrobeniusInnerProductSpace : InnerProductSpace ℝ 𝕄 :=
  Matrix.frobeniusInnerProductSpace

/-- Helper for Theorem 7.6: the rectangular diagonal embedding is continuous. -/
lemma continuous_rectangularDiagonal :
    Continuous (rectangularDiagonalProfile : (Fin (min m n) → ℝ) → 𝕄) := by
  -- Each entry of the rectangular diagonal embedding is either a fixed coordinate projection or
  -- the constant zero function.
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  by_cases h : i.1 = j.1
  · have hji : j.1 < min m n := Nat.lt_min.mpr ⟨h.symm ▸ i.2, j.2⟩
    let k : Fin (min m n) := ⟨j.1, hji⟩
    simpa [rectangularDiagonalProfile, h] using
      (continuous_apply k : Continuous fun x : Fin (min m n) → ℝ ↦ x k)
  · simpa [rectangularDiagonalProfile, h] using
      (continuous_const : Continuous fun _ : Fin (min m n) → ℝ ↦ (0 : ℝ))

/-- Helper for Theorem 7.6: the rectangular diagonal embedding is affine on segments. -/
lemma rectangularDiagonal_segment
    (x y : Fin (min m n) → ℝ) (t : ℝ) :
    rectangularDiagonalProfile (t • x + (1 - t) • y) =
      t • rectangularDiagonalProfile x + (1 - t) • rectangularDiagonalProfile y := by
  -- The rectangular diagonal construction is entrywise linear in its vector input.
  ext i j
  by_cases h : i.1 = j.1
  · simp [rectangularDiagonalProfile, h]
  · simp [rectangularDiagonalProfile, h]

/-- Helper for Theorem 7.6: the coordinatewise sign pattern attached to a vector. -/
def sign_pattern (x : Fin (min m n) → ℝ) : Fin (min m n) → ℝ :=
  fun i ↦ if x i < 0 then -1 else 1

/-- Helper for Theorem 7.6: the sign pattern has absolute value `1` in every coordinate. -/
lemma abs_sign_pattern (x : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    |sign_pattern x i| = 1 := by
  -- Each coordinate of the sign pattern is either `-1` or `1`.
  by_cases hxi : x i < 0
  · simp [sign_pattern, hxi]
  · simp [sign_pattern, hxi]

/-- Helper for Theorem 7.6: multiplying the sign pattern by the absolute value recovers the
original coordinate. -/
lemma sign_pattern_mul_abs (x : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    sign_pattern x i * |x i| = x i := by
  -- Split by the sign of the coordinate and simplify the absolute value accordingly.
  by_cases hxi : x i < 0
  · simp [sign_pattern, hxi, abs_of_neg hxi]
  · have hxi_nonneg : 0 ≤ x i := le_of_not_gt hxi
    simp [sign_pattern, hxi, abs_of_nonneg hxi_nonneg]

/-- Helper for Theorem 7.6: the diagonal matrix of the sign pattern is orthogonal. -/
private noncomputable def signDiagonalOrthogonal
    (x : Fin (min m n) → ℝ) : Matrix.orthogonalGroup (Fin (min m n)) ℝ := by
  let s : Fin (min m n) → ℝ := sign_pattern x
  have hsq : ∀ i : Fin (min m n), s i * s i = 1 := by
    intro i
    by_cases hxi : x i < 0
    · simp [s, sign_pattern, hxi]
    · simp [s, sign_pattern, hxi]
  refine ⟨Matrix.diagonal s, ?_⟩
  refine (Matrix.mem_orthogonalGroup_iff (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun i ↦ s i * s i) := by
      rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hsq]
      · simp [hij]

/-- Helper for Theorem 7.6: the sign orthogonal acts by coordinatewise multiplication. -/
private lemma signDiagonalOrthogonal_mulVec
    (x z : Fin (min m n) → ℝ) :
    (((signDiagonalOrthogonal x : Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
        Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z =
      fun i ↦ sign_pattern x i * z i := by
  -- A diagonal matrix acts coordinatewise on vectors.
  ext i
  simp [signDiagonalOrthogonal, Matrix.mulVec_diagonal, sign_pattern]

/-- Helper for Theorem 7.6: extend the sign pattern by `1` outside the common diagonal block on
the row index set. -/
private def rectangularSignPattern
    (x : Fin (min m n) → ℝ) : Fin m → ℝ :=
  fun i ↦
    if h : i.1 < min m n then
      sign_pattern x ⟨i.1, h⟩
    else 1

/-- Helper for Theorem 7.6: the rectangularly extended sign pattern defines an orthogonal row
matrix. -/
private noncomputable def rectangularSignOrthogonal
    (x : Fin (min m n) → ℝ) : Matrix.orthogonalGroup (Fin m) ℝ := by
  let s : Fin m → ℝ := rectangularSignPattern (m := m) (n := n) x
  have hsq : ∀ i : Fin m, s i * s i = 1 := by
    intro i
    by_cases hi : i.1 < min m n
    · have hcoord : sign_pattern x ⟨i.1, hi⟩ * sign_pattern x ⟨i.1, hi⟩ = 1 := by
        -- Coordinates inside the common block still have sign `±1`.
        by_cases hneg : x ⟨i.1, hi⟩ < 0
        · simp [sign_pattern, hneg]
        · simp [sign_pattern, hneg]
      simpa [s, rectangularSignPattern, hi] using hcoord
    · -- Outside the common block, the extension is the identity sign.
      simp [s, rectangularSignPattern, hi]
  refine ⟨Matrix.diagonal s, ?_⟩
  refine (Matrix.mem_orthogonalGroup_iff (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun i ↦ s i * s i) := by
      rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hsq]
      · simp [hij]

/-- Helper for Theorem 7.6: extending the same permutation to the row and column index sets
acts on the rectangular diagonal profile entrywise by the original permutation on the common
diagonal block. -/
private lemma rectangularDiagonalProfile_perm_extension_apply
    (σ : Equiv.Perm (Fin (min m n))) (z : Fin (min m n) → ℝ) (i : Fin m) (j : Fin n) :
    let σm : Equiv.Perm (Fin m) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
    let σn : Equiv.Perm (Fin n) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
    (orthogonalRectangularDiagonalProfileMap
        (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
      if h : i.1 = j.1 then z (σ ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩) else 0 := by
  let σm : Equiv.Perm (Fin m) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
  let σn : Equiv.Perm (Fin n) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
  have hentry :
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
        rectangularDiagonalProfile z (σm i) (σn j) := by
    have hleft :
        ∀ x : Fin n,
          ((((permutationOrthogonalMatrix σm : Matrix.orthogonalGroup (Fin m) ℝ) :
              Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile z) i x) =
            rectangularDiagonalProfile z (σm i) x := by
      intro x
      -- Left multiplication by the extended row permutation just reindexes the row coordinate.
      simpa [permutationOrthogonalMatrix] using
        (show ((σm.permMatrix ℝ * rectangularDiagonalProfile z) i x) =
            rectangularDiagonalProfile z (σm i) x by
          simp [Matrix.mul_apply])
    have htranspose :
        (((permutationOrthogonalMatrix σn : Matrix.orthogonalGroup (Fin n) ℝ) :
            Matrix (Fin n) (Fin n) ℝ)ᵀ) =
          ((σn⁻¹).permMatrix ℝ) := by
      -- The transpose of a permutation matrix is the permutation matrix of the inverse.
      simpa [permutationOrthogonalMatrix] using
        (Matrix.transpose_permMatrix (R := ℝ) (σ := σn))
    have hright :=
      congrFun
        (Matrix.vecMul_permMatrix (R := ℝ) (σ := σn⁻¹)
          (v := fun x : Fin n ↦ rectangularDiagonalProfile z (σm i) x)) j
    -- After normalizing the transpose, the right multiplication is exactly the row action
    -- of the inverse permutation matrix.
    calc
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
          ((fun x : Fin n ↦ rectangularDiagonalProfile z (σm i) x) ᵥ*
            ((σn⁻¹).permMatrix ℝ)) j := by
              rw [orthogonalRectangularDiagonalProfileMap_apply, Matrix.mul_apply, htranspose]
              simp_rw [hleft]
              rfl
      _ = rectangularDiagonalProfile z (σm i) (σn j) := by
            simpa [Matrix.vecMul, dotProduct] using hright
  have hmain :
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
        if h : i.1 = j.1 then z (σ ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩) else 0 := by
    calc
      (orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z) i j =
          rectangularDiagonalProfile z (σm i) (σn j) := hentry
      _ = if h : i.1 = j.1 then z (σ ⟨i.1, Nat.lt_min.mpr ⟨i.2, h ▸ j.2⟩⟩) else 0 := by
            by_cases hij : i.1 = j.1
            · have hi : i.1 < min m n := Nat.lt_min.mpr ⟨i.2, hij ▸ j.2⟩
              have hj : j.1 < min m n := by
                simpa [hij] using hi
              let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
              let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
              have hσm : σm i = eL (σ ⟨i.1, hi⟩) := by
                have hi_cast : eL ⟨i.1, hi⟩ = i := by
                  ext
                  rfl
                -- Inside the common block, the row extension agrees with the original permutation.
                simpa [σm, eL, hi_cast] using
                  (Equiv.Perm.viaFintypeEmbedding_apply_image
                    (e := σ) (f := eL) ⟨i.1, hi⟩)
              have hσn : σn j = eR (σ ⟨j.1, hj⟩) := by
                have hj_cast : eR ⟨j.1, hj⟩ = j := by
                  ext
                  rfl
                -- Inside the common block, the column extension agrees with the same original
                -- permutation.
                simpa [σn, eR, hj_cast] using
                  (Equiv.Perm.viaFintypeEmbedding_apply_image
                    (e := σ) (f := eR) ⟨j.1, hj⟩)
              have hσn' : σn j = eR (σ ⟨i.1, hi⟩) := by
                simpa [hij] using hσn
              -- On the common diagonal block, both extensions hit the same permuted coordinate.
              rw [rectangularDiagonalProfile_apply]
              simpa [eL, eR, hij, hσm, hσn']
            · by_cases hi : i.1 < min m n
              · by_cases hj : j.1 < min m n
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = eL (σ ⟨i.1, hi⟩) := by
                    have hi_cast : eL ⟨i.1, hi⟩ = i := by
                      ext
                      rfl
                    -- Both indices lie in the common block, so each extension is again the
                    -- original permutation on that block.
                    simpa [σm, eL, hi_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eL) ⟨i.1, hi⟩)
                  have hσn : σn j = eR (σ ⟨j.1, hj⟩) := by
                    have hj_cast : eR ⟨j.1, hj⟩ = j := by
                      ext
                      rfl
                    simpa [σn, eR, hj_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eR) ⟨j.1, hj⟩)
                  have hNe : (σ ⟨i.1, hi⟩).1 ≠ (σ ⟨j.1, hj⟩).1 := by
                    intro hEq
                    apply hij
                    exact congrArg Fin.val (σ.injective (Fin.ext hEq))
                  -- Different diagonal coordinates remain different after applying the same
                  -- permutation.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [eL, eR, hNe, hij]
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = eL (σ ⟨i.1, hi⟩) := by
                    have hi_cast : eL ⟨i.1, hi⟩ = i := by
                      ext
                      rfl
                    -- The row index is still in range, so the extension acts by `σ`.
                    simpa [σm, eL, hi_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eL) ⟨i.1, hi⟩)
                  have hσn : σn j = j := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hjRange
                    rcases hjRange with ⟨a, ha⟩
                    have haj : a.1 = j.1 := by
                      simpa [eR] using congrArg Fin.val ha
                    exact hj (haj ▸ a.2)
                  have hNe : (σ ⟨i.1, hi⟩).1 ≠ j.1 := by
                    intro hEq
                    exact hj (hEq ▸ (σ ⟨i.1, hi⟩).2)
                  -- A common-block row cannot land on an out-of-range column index.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [eL, hNe, hij]
              · by_cases hj : j.1 < min m n
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = i := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hiRange
                    rcases hiRange with ⟨a, ha⟩
                    have hai : a.1 = i.1 := by
                      simpa [eL] using congrArg Fin.val ha
                    exact hi (hai ▸ a.2)
                  have hσn : σn j = eR (σ ⟨j.1, hj⟩) := by
                    have hj_cast : eR ⟨j.1, hj⟩ = j := by
                      ext
                      rfl
                    -- The column index is still in range, so the extension acts by `σ`.
                    simpa [σn, eR, hj_cast] using
                      (Equiv.Perm.viaFintypeEmbedding_apply_image
                        (e := σ) (f := eR) ⟨j.1, hj⟩)
                  have hNe : i.1 ≠ (σ ⟨j.1, hj⟩).1 := by
                    intro hEq
                    exact hi (hEq ▸ (σ ⟨j.1, hj⟩).2)
                  -- Symmetrically, an out-of-range row cannot meet a common-block column on the
                  -- diagonal.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [eR, hNe, hij]
                · let eL : Fin (min m n) ↪ Fin m := Fin.castLEEmb (Nat.min_le_left m n)
                  let eR : Fin (min m n) ↪ Fin n := Fin.castLEEmb (Nat.min_le_right m n)
                  have hσm : σm i = i := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hiRange
                    rcases hiRange with ⟨a, ha⟩
                    have hai : a.1 = i.1 := by
                      simpa [eL] using congrArg Fin.val ha
                    exact hi (hai ▸ a.2)
                  have hσn : σn j = j := by
                    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
                    intro hjRange
                    rcases hjRange with ⟨a, ha⟩
                    have haj : a.1 = j.1 := by
                      simpa [eR] using congrArg Fin.val ha
                    exact hj (haj ▸ a.2)
                  -- Outside the common block, both extensions are the identity, so the
                  -- off-diagonal condition is unchanged.
                  rw [hσm, hσn, rectangularDiagonalProfile_apply]
                  simp [hij]
  simpa [σm, σn] using hmain

/-- Helper for Theorem 7.6: extending the same permutation to the row and column index sets
reindexes the rectangular diagonal profile by that permutation. -/
private lemma rectangularDiagonalProfile_perm_extension_eq
    (σ : Equiv.Perm (Fin (min m n))) (z : Fin (min m n) → ℝ) :
    let σm : Equiv.Perm (Fin m) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
    let σn : Equiv.Perm (Fin n) :=
      σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
    orthogonalRectangularDiagonalProfileMap
        (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) z =
      rectangularDiagonalProfile (z ∘ σ) := by
  let σm : Equiv.Perm (Fin m) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
  let σn : Equiv.Perm (Fin n) :=
    σ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
  ext i j
  -- The explicit entrywise owner matches the defining formula of the reindexed diagonal profile.
  simpa [σm, σn, rectangularDiagonalProfile_apply] using
    rectangularDiagonalProfile_perm_extension_apply (m := m) (n := n) σ z i j

/-- Helper for Theorem 7.6: the rectangularly extended sign matrix restores the signs of the
diagonal profile while leaving the column factor trivial. -/
private lemma rectangularDiagonalProfile_left_sign_eq
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalProfileMap (rectangularSignOrthogonal (m := m) (n := n) x) 1
        (fun i ↦ |x i|) =
      rectangularDiagonalProfile x := by
  -- Evaluate the row-sign orthogonal map entrywise and separate the diagonal and off-diagonal
  -- cases of the rectangular profile.
  ext i j
  by_cases hij : i.1 = j.1
  · have hj_m : j.1 < m := hij ▸ i.2
    -- On the common diagonal block, the sign matrix contributes exactly `sign_pattern x i`.
    simp [orthogonalRectangularDiagonalProfileMap_apply, rectangularDiagonalProfile_apply,
      rectangularSignOrthogonal, rectangularSignPattern, hij, hj_m, sign_pattern_mul_abs]
  · -- Off the common diagonal block, both the raw profile and its signed version vanish.
    simp [orthogonalRectangularDiagonalProfileMap_apply, rectangularDiagonalProfile_apply,
      rectangularSignOrthogonal, rectangularSignPattern, hij]

/-- Helper for Theorem 7.6: the raw rectangular diagonal profile is an orthogonal image of the
canonical sorted absolute-value profile `|x|↓`. -/
private lemma rectangularDiagonalProfile_eq_orthogonalRectangularDiagonalProfileMap_abs_descending
    (x : Fin (min m n) → ℝ) :
    ∃ U : Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
        rectangularDiagonalProfile x =
          orthogonalRectangularDiagonalProfileMap U V
            (Function.descendingRearrangement (fun i ↦ |x i|)) := by
  let τ : Equiv.Perm (Fin (min m n)) :=
    (Tuple.sort (fun i ↦ |x i|) * Fin.revPerm).symm
  let xdesc : Fin (min m n) → ℝ :=
    Function.descendingRearrangement (fun i ↦ |x i|)
  let σm : Equiv.Perm (Fin m) :=
    τ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_left m n))
  let σn : Equiv.Perm (Fin n) :=
    τ.viaFintypeEmbedding (Fin.castLEEmb (Nat.min_le_right m n))
  have hsort :
      permutationOrthogonalMatrix τ.symm • (fun i ↦ |x i|) = xdesc := by
    -- The concrete sorting permutation sends `|x|` to its decreasing rearrangement `|x|↓`.
    have hsort_tuple :
        permutationOrthogonalMatrix τ.symm • (fun i ↦ |x i|) =
          _root_.descendingRearrangement (fun i ↦ |x i|) := by
      simpa [τ] using
        (descendingRearrangement_eq_sort_perm_smul (fun i ↦ |x i|))
    dsimp [xdesc]
    rw [function_descendingRearrangement_eq_descendingRearrangement
      (m := m) (n := n) (x := fun i ↦ |x i|)]
    exact hsort_tuple
  have hτmul :
      permutationOrthogonalMatrix τ * permutationOrthogonalMatrix τ.symm =
        (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) := by
    -- The inverse permutation cancels the sorting permutation inside the orthogonal group.
    apply Subtype.ext
    change τ.permMatrix ℝ * (τ⁻¹).permMatrix ℝ = 1
    calc
      τ.permMatrix ℝ * (τ⁻¹).permMatrix ℝ =
          (τ⁻¹ * τ).permMatrix ℝ :=
        (Matrix.permMatrix_mul (R := ℝ) (σ := τ⁻¹) (τ := τ)).symm
      _ = 1 := by simp
  have hunsort_smul :
      permutationOrthogonalMatrix τ • xdesc = (fun i ↦ |x i|) := by
    have happly :=
      congrArg
        (fun v : Fin (min m n) → ℝ ↦ permutationOrthogonalMatrix τ • v)
        hsort
    -- Applying the inverse sorting permutation recovers the original absolute values.
    calc
      permutationOrthogonalMatrix τ • xdesc =
          (permutationOrthogonalMatrix τ * permutationOrthogonalMatrix τ.symm) •
            (fun i ↦ |x i|) := by
              symm
              simpa [smul_smul] using happly
      _ = (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) • (fun i ↦ |x i|) := by
            rw [hτmul]
      _ = (fun i ↦ |x i|) := by
            simp
  have hunsort :
      xdesc ∘ τ = (fun i ↦ |x i|) := by
    -- Rewriting the orthogonal action as coordinate permutation gives the desired vector identity.
    simpa [permutationOrthogonalMatrix_smul] using hunsort_smul
  have hperm :
      orthogonalRectangularDiagonalProfileMap
          (permutationOrthogonalMatrix σm) (permutationOrthogonalMatrix σn) xdesc =
        rectangularDiagonalProfile (fun i ↦ |x i|) := by
    -- The common permutation on rows and columns turns the sorted profile into the raw absolute
    -- diagonal profile.
    simpa [σm, σn, hunsort] using
      (rectangularDiagonalProfile_perm_extension_eq (m := m) (n := n) τ xdesc)
  let U : Matrix.orthogonalGroup (Fin m) ℝ :=
    rectangularSignOrthogonal (m := m) (n := n) x * permutationOrthogonalMatrix σm
  let V : Matrix.orthogonalGroup (Fin n) ℝ := permutationOrthogonalMatrix σn
  refine ⟨U, V, ?_⟩
  -- Route correction: first unsort `|x|↓` to the raw absolute diagonal profile, then restore the
  -- original signs by the row-sign orthogonal.
  calc
    rectangularDiagonalProfile x =
        orthogonalRectangularDiagonalProfileMap
          (rectangularSignOrthogonal (m := m) (n := n) x) 1
          (fun i ↦ |x i|) := by
            symm
            exact rectangularDiagonalProfile_left_sign_eq (m := m) (n := n) x
    _ = orthogonalRectangularDiagonalProfileMap U V xdesc := by
          dsimp [U, V]
          rw [orthogonalRectangularDiagonalProfileMap_apply,
            orthogonalRectangularDiagonalProfileMap_apply]
          rw [orthogonalRectangularDiagonalProfileMap_apply] at hperm
          calc
            ((rectangularSignOrthogonal (m := m) (n := n) x :
                Matrix.orthogonalGroup (Fin m) ℝ) :
                Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile (fun i ↦ |x i|) *
                (((1 : Matrix.orthogonalGroup (Fin n) ℝ) :
                  Matrix (Fin n) (Fin n) ℝ)ᵀ) =
              ((rectangularSignOrthogonal (m := m) (n := n) x :
                  Matrix.orthogonalGroup (Fin m) ℝ) :
                  Matrix (Fin m) (Fin m) ℝ) *
                ((((permutationOrthogonalMatrix σm :
                    Matrix.orthogonalGroup (Fin m) ℝ) :
                    Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile xdesc) *
                  (((permutationOrthogonalMatrix σn :
                      Matrix.orthogonalGroup (Fin n) ℝ) :
                      Matrix (Fin n) (Fin n) ℝ)ᵀ)) := by
                rw [hperm]
                simp [Matrix.mul_assoc]
            _ =
              ((rectangularSignOrthogonal (m := m) (n := n) x *
                  permutationOrthogonalMatrix σm :
                    Matrix.orthogonalGroup (Fin m) ℝ) :
                    Matrix (Fin m) (Fin m) ℝ) * rectangularDiagonalProfile xdesc *
                  (((permutationOrthogonalMatrix σn :
                      Matrix.orthogonalGroup (Fin n) ℝ) :
                      Matrix (Fin n) (Fin n) ℝ)ᵀ) := by
                simp [Matrix.mul_assoc]

/-- Helper for Theorem 7.6: every coordinate of the sorted absolute-value profile is
nonnegative. -/
private lemma descendingRearrangement_abs_nonneg
    (x : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    0 ≤ Function.descendingRearrangement (fun j ↦ |x j|) i := by
  -- Every entry of the merge-sorted list of absolute values comes from an original absolute value.
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

/-- Helper for Theorem 7.6: evaluating the spectral lift on the rectangular diagonal model
recovers the ordered absolute-value profile because the singular values of `dg(x)` are `|x|↓`. -/
private lemma singular_value_function_rectangularDiagonalProfile_eq_abs_descendingRearrangement
    (x : Fin (min m n) → ℝ) :
    singular_value_function (rectangularDiagonalProfile x) =
      Function.descendingRearrangement (fun i ↦ |x i|) := by
  rcases
    rectangularDiagonalProfile_eq_orthogonalRectangularDiagonalProfileMap_abs_descending
      (m := m) (n := n) x with
    ⟨U, V, hUV⟩
  -- The orthogonal packaging reduces the singular values to the canonical sorted absolute profile.
  rw [hUV]
  simpa using
    singular_value_function_orthogonalRectangularDiagonalMap_eq_of_nonneg_antitone
      U V (Function.descendingRearrangement (fun i ↦ |x i|))
      (descendingRearrangement_abs_nonneg (m := m) (n := n) x)
      (antitone_function_descendingRearrangement (m := m) (n := n) (fun i ↦ |x i|))

/-- Helper for Theorem 7.6: evaluating the spectral lift on the rectangular diagonal model
recovers the original vector profile because the singular values of `dg(x)` are `|x|↓`. -/
lemma absolutely_symmetric_rectangular_diagonal_pullback_eq
    (f : (Fin (min m n) → ℝ) → EReal) (hf : IsAbsolutelyPermutationSymmetric f)
    (x : Fin (min m n) → ℝ) :
    (f ∘ singular_value_function) (rectangularDiagonalProfile x) = f x := by
  -- Replace the diagonal model by its ordered absolute-value singular-value vector.
  rw [Function.comp_apply,
    singular_value_function_rectangularDiagonalProfile_eq_abs_descendingRearrangement]
  -- Absolute permutation symmetry identifies the canonical profile with the original vector.
  exact (hf.map_eq_abs_descendingRearrangement x).symm

/-- Helper for Theorem 7.6: if an orthogonal precomposition preserves the canonical
absolute-sorted representative `|x|↓`, then an absolutely permutation symmetric function is
invariant under that precomposition. -/
lemma absolutely_symmetric_precompose_eq_of_preserves_abs_descendingRearrangement
    (f : (Fin (min m n) → ℝ) → EReal) (hf : IsAbsolutelyPermutationSymmetric f)
    (A : Matrix.orthogonalGroup (Fin (min m n)) ℝ)
    (hA :
      ∀ z : Fin (min m n) → ℝ,
        Function.descendingRearrangement
            (fun i ↦
              |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|) =
          Function.descendingRearrangement (fun i ↦ |z i|)) :
    (fun z : Fin (min m n) → ℝ ↦
      f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)) = f := by
  ext z
  -- Replace both inputs by the same canonical representative `|z|↓`.
  calc
    f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) =
        f (Function.descendingRearrangement
          (fun i ↦ |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|)) :=
      hf.map_eq_abs_descendingRearrangement
        (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)
    _ = f (Function.descendingRearrangement (fun i ↦ |z i|)) := by
          rw [hA z]
    _ = f z := (hf.map_eq_abs_descendingRearrangement z).symm

/-- Helper for Theorem 7.6: pulling the conjugate back along `dotProductEquiv` preserves absolute
permutation symmetry. -/
private lemma dotProduct_conjugate_profile_is_absolutely_permutation_symmetric
    (f : (Fin (min m n) → ℝ) → EReal) (hf : IsAbsolutelyPermutationSymmetric f)
    (hfconv : is_convex_function f) :
    IsAbsolutelyPermutationSymmetric
      (fun x : Fin (min m n) → ℝ ↦
        conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) x)) := by
  let hproper : IsProperExtendedRealFunction f := ⟨hf.ne_bot, hf.effective_domain_nonempty⟩
  let hconj := isProperExtendedRealFunction_conjugate_function f hproper hfconv
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_
      map_eq_abs_descendingRearrangement := ?_ }
  · intro x
    -- Properness of the conjugate profile transports through `dotProductEquiv`.
    exact hconj.ne_bot (dotProductEquiv ℝ (Fin (min m n)) x)
  · rcases hconj.effective_domain_nonempty with ⟨y, hy⟩
    refine ⟨(dotProductEquiv ℝ (Fin (min m n))).symm y, ?_⟩
    have hdual :
        dotProductEquiv ℝ (Fin (min m n))
            ((dotProductEquiv ℝ (Fin (min m n))).symm y) = y :=
      (dotProductEquiv ℝ (Fin (min m n))).apply_symm_apply y
    -- The effective-domain witness pulls back through the linear equivalence unchanged.
    simpa [hdual] using hy
  · intro x
    let σ : Equiv.Perm (Fin (min m n)) :=
      (Tuple.sort (fun i ↦ |x i|) * Fin.revPerm).symm
    let A : Matrix.orthogonalGroup (Fin (min m n)) ℝ :=
      signDiagonalOrthogonal x * permutationOrthogonalMatrix σ
    let xdesc : Fin (min m n) → ℝ :=
      Function.descendingRearrangement (fun i ↦ |x i|)
    have hperm :
        (((permutationOrthogonalMatrix σ :
            Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
            Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc =
          (fun i ↦ |x i|) := by
      have hsort :
          permutationOrthogonalMatrix σ.symm • (fun i ↦ |x i|) = xdesc := by
        -- The concrete sorting permutation sends `|x|` to its decreasing rearrangement `|x|↓`.
        rw [show xdesc = Function.descendingRearrangement (fun i ↦ |x i|) by rfl]
        rw [function_descendingRearrangement_eq_descendingRearrangement
            (x := fun i ↦ |x i|)]
        simpa [σ] using
          (descendingRearrangement_eq_sort_perm_smul (fun i ↦ |x i|))
      have hperm_smul :
          permutationOrthogonalMatrix σ • xdesc = (fun i ↦ |x i|) := by
        -- Applying the inverse permutation to the sorted profile recovers the original absolute values.
        have happly :=
          congrArg
            (fun v : Fin (min m n) → ℝ ↦ permutationOrthogonalMatrix σ • v)
            hsort
        have hσmul :
            permutationOrthogonalMatrix σ * permutationOrthogonalMatrix σ.symm =
              (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) := by
          apply Subtype.ext
          -- The inverse permutation matrix cancels the original one inside the orthogonal group.
          change σ.permMatrix ℝ * (σ⁻¹).permMatrix ℝ = 1
          calc
            σ.permMatrix ℝ * (σ⁻¹).permMatrix ℝ =
                (σ⁻¹ * σ).permMatrix ℝ :=
              (Matrix.permMatrix_mul (R := ℝ) (σ := σ⁻¹) (τ := σ)).symm
            _ = 1 := by simp
        calc
          permutationOrthogonalMatrix σ • xdesc =
              (permutationOrthogonalMatrix σ * permutationOrthogonalMatrix σ.symm) •
                (fun i ↦ |x i|) := by
                  symm
                  simpa [smul_smul] using happly
          _ = (1 : Matrix.orthogonalGroup (Fin (min m n)) ℝ) • (fun i ↦ |x i|) := by
                rw [hσmul]
          _ = (fun i ↦ |x i|) := by
                simp
      simpa using hperm_smul
    have hA_to_x :
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc = x := by
      -- Route correction: first unsort `|x|↓` to `|x|`, then restore the signs coordinatewise.
      calc
        ((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc =
            ((signDiagonalOrthogonal x :
              Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
              Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec
                ((((permutationOrthogonalMatrix σ :
                  Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                  Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc) := by
                  simp [A, Matrix.mulVec_mulVec]
        _ = ((signDiagonalOrthogonal x :
              Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
              Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec (fun i ↦ |x i|) := by
                rw [hperm]
        _ = x := by
              ext i
              rw [signDiagonalOrthogonal_mulVec]
              exact sign_pattern_mul_abs x i
    have hA_preserves :
        ∀ z : Fin (min m n) → ℝ,
          Function.descendingRearrangement
              (fun i ↦
                |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|) =
            Function.descendingRearrangement (fun i ↦ |z i|) := by
      intro z
      have hAz :
          ∀ i,
            (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i =
              sign_pattern x i * z (σ i) := by
        intro i
        -- Split the action into the sign diagonal followed by the inverse sorting permutation.
        calc
          (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i =
              (((signDiagonalOrthogonal x :
                Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                Matrix (Fin (min m n)) (Fin (min m n)) ℝ).mulVec
                  ((((permutationOrthogonalMatrix σ :
                    Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                    Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)) i := by
                    simp [A, Matrix.mulVec_mulVec]
          _ = sign_pattern x i *
                ((((permutationOrthogonalMatrix σ :
                  Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                  Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i := by
                  rw [signDiagonalOrthogonal_mulVec]
          _ = sign_pattern x i * z (σ i) := by
                calc
                  sign_pattern x i *
                      ((((permutationOrthogonalMatrix σ :
                        Matrix.orthogonalGroup (Fin (min m n)) ℝ) :
                        Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i =
                      sign_pattern x i * ((z ∘ σ) i) := by
                        congr 1
                        simpa [permutationOrthogonalMatrix] using
                          congrFun (Matrix.permMatrix_mulVec (R := ℝ) (σ := σ) (v := z)) i
                  _ = sign_pattern x i * z (σ i) := by
                        rfl
      have habs :
          (fun i ↦ |(((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z) i|) =
            (fun i ↦ |z i|) ∘ σ := by
        ext i
        rw [hAz i, abs_mul, abs_sign_pattern]
        simp
      -- Absolute values remove the sign diagonal, and permutations preserve decreasing rearrangement.
      rw [habs]
      rw [function_descendingRearrangement_eq_descendingRearrangement
          (((fun i ↦ |z i|) ∘ σ))]
      rw [function_descendingRearrangement_eq_descendingRearrangement
          (fun i ↦ |z i|)]
      exact descendingRearrangement_comp_perm (x := fun i ↦ |z i|) σ
    have hpre :
        (fun z : Fin (min m n) → ℝ ↦
          f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z)) = f :=
      absolutely_symmetric_precompose_eq_of_preserves_abs_descendingRearrangement
        f hf A hA_preserves
    have hconj_transport :
        conjugate_function
            (fun z : Fin (min m n) → ℝ ↦
              f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z))
            (dotProductEquiv ℝ (Fin (min m n)) xdesc) =
          conjugate_function f
            (dotProductEquiv ℝ (Fin (min m n))
              (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc)) := by
      -- The Chapter 7 conjugate transport theorem matches the explicit `mulVec` presentation.
      change conjugate_function (fun z : Fin (min m n) → ℝ ↦ f (A • z))
          (dotProductEquiv ℝ (Fin (min m n)) xdesc) =
        conjugate_function f
          (dotProductEquiv ℝ (Fin (min m n)) (A • xdesc))
      exact theorem7_9_conjugate_function_precompose_orthogonal_eq A f xdesc
    -- The conjugate at `x` is the conjugate at `|x|↓` after the corresponding signed permutation.
    calc
      conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) x) =
          conjugate_function f
            (dotProductEquiv ℝ (Fin (min m n))
              (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec xdesc)) := by
                rw [hA_to_x]
      _ = conjugate_function
            (fun z : Fin (min m n) → ℝ ↦
              f (((A : Matrix (Fin (min m n)) (Fin (min m n)) ℝ)).mulVec z))
            (dotProductEquiv ℝ (Fin (min m n)) xdesc) := by
              symm
              exact hconj_transport
      _ = conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) xdesc) := by
            rw [hpre]

/-- Helper for Theorem 7.6: taking the `dotProductEquiv`-pullback conjugate twice recovers the
Chapter 4 biconjugate of the vector profile. -/
private lemma dotProduct_conjugate_profile_biconjugate_eq
    (f : (Fin (min m n) → ℝ) → EReal) :
    (fun x : Fin (min m n) → ℝ ↦
      conjugate_function
        (fun z : Fin (min m n) → ℝ ↦
          conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) z))
        (dotProductEquiv ℝ (Fin (min m n)) x)) =
      biconjugate_function f := by
  funext x
  -- Compare the two defining suprema by transporting witnesses through `dotProductEquiv`.
  rw [conjugate_function_apply, biconjugate_function_apply]
  congr 1
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dotProductEquiv ℝ (Fin (min m n)) z, ?_⟩
    simp [dotProduct_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨(dotProductEquiv ℝ (Fin (min m n))).symm y, ?_⟩
    have hdual :
        dotProductEquiv ℝ (Fin (min m n))
            ((dotProductEquiv ℝ (Fin (min m n))).symm y) = y :=
      (dotProductEquiv ℝ (Fin (min m n))).apply_symm_apply y
    have hpair' :
        (dotProductEquiv ℝ (Fin (min m n))
            ((dotProductEquiv ℝ (Fin (min m n))).symm y)) x = y x := by
      exact congrArg (fun ψ : Module.Dual ℝ (Fin (min m n) → ℝ) => ψ x) hdual
    have hpair :
        dotProduct x ((dotProductEquiv ℝ (Fin (min m n))).symm y) = y x := by
      simpa [dotProductEquiv, dotProduct_comm] using hpair'
    simp [hdual, hpair]

/-- Helper for Theorem 7.6: if the vector profile is closed and convex, then its rectangular
spectral lift is also closed and convex. This is the textbook conjugate-biconjugate route. -/
lemma absolutely_symmetric_spectral_closed_convex_forward
    (f : (Fin (min m n) → ℝ) → EReal) (hf : IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    LowerSemicontinuous (f ∘ singular_value_function) ∧
      is_convex_function (f ∘ singular_value_function) := by
  let fconj : (Fin (min m n) → ℝ) → EReal :=
    fun x ↦ conjugate_function f (dotProductEquiv ℝ (Fin (min m n)) x)
  have hfconj_symm : IsAbsolutelyPermutationSymmetric fconj :=
    dotProduct_conjugate_profile_is_absolutely_permutation_symmetric f hf hf_convex
  have hmatrix_conj :
      (fun Y : 𝕄 ↦ conjugate_function (f ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
        fconj ∘ singular_value_function := by
    -- The first spectral conjugate formula identifies the matrix conjugate with the vector one.
    simpa [fconj, Function.comp] using matrix_spectral_conjugate_formula f hf
  have hmatrix_conj_conj :
      (fun Y : 𝕄 ↦ conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
        (fun x : Fin (min m n) → ℝ ↦
          conjugate_function fconj (dotProductEquiv ℝ (Fin (min m n)) x)) ∘
          singular_value_function := by
    -- Apply the same spectral formula once more to the conjugate profile.
    simpa [Function.comp] using matrix_spectral_conjugate_formula fconj hfconj_symm
  have hproper : IsProperExtendedRealFunction f := ⟨hf.ne_bot, hf.effective_domain_nonempty⟩
  have hself : biconjugate_function f = f :=
    biconjugate_function_eq_self_of_proper_closed_convex f hproper hf_closed hf_convex
  have hmatrix_self :
      (fun Y : 𝕄 ↦ conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
        f ∘ singular_value_function := by
    -- The second conjugation turns the vector profile into its Chapter 4 biconjugate.
    calc
      (fun Y : 𝕄 ↦ conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) =
          (fun x : Fin (min m n) → ℝ ↦
            conjugate_function fconj (dotProductEquiv ℝ (Fin (min m n)) x)) ∘
            singular_value_function := hmatrix_conj_conj
      _ = biconjugate_function f ∘ singular_value_function := by
            rw [dotProduct_conjugate_profile_biconjugate_eq f]
      _ = f ∘ singular_value_function := by
            rw [hself]
  let G : 𝕄 → EReal :=
    fun Y ↦ conjugate_function (f ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)
  have hdouble : G∗ = f ∘ singular_value_function := by
    -- Rewrite the primal conjugate of `G` through the stabilized matrix-side biconjugate route.
    funext Y
    calc
      (G∗) Y = conjugate_function G ↑(toDualMap ℝ 𝕄 Y) := by
        rw [conjugate_function_primal_apply]
      _ = f (singular_value_function Y) := by
        exact congrFun
          (show (fun Y : 𝕄 ↦ conjugate_function G ↑(toDualMap ℝ 𝕄 Y)) =
              f ∘ singular_value_function by
            calc
              (fun Y : 𝕄 ↦ conjugate_function G ↑(toDualMap ℝ 𝕄 Y)) =
                  (fun Y : 𝕄 ↦
                    conjugate_function (fconj ∘ singular_value_function) ↑(toDualMap ℝ 𝕄 Y)) := by
                      simp [G, hmatrix_conj]
              _ = f ∘ singular_value_function := hmatrix_self) Y
  have hclosedconv := conjugate_function_closed_and_convex G
  -- Theorem 4.1 gives closedness and convexity of the double conjugate, which now equals `F`.
  rw [hdouble] at hclosedconv
  exact hclosedconv

/-- Helper for Theorem 7.6: if the rectangular spectral lift is closed and convex, then pulling it
back along the rectangular diagonal model recovers a closed and convex vector profile. -/
lemma absolutely_symmetric_spectral_closed_convex_reverse
    (f : (Fin (min m n) → ℝ) → EReal) (hf : IsAbsolutelyPermutationSymmetric f)
    (hF_closed : LowerSemicontinuous (f ∘ singular_value_function))
    (hF_convex : is_convex_function (f ∘ singular_value_function)) :
    LowerSemicontinuous f ∧ is_convex_function f := by
  have hpull : ((f ∘ singular_value_function) ∘ rectangularDiagonalProfile) = f := by
    -- The rectangular diagonal pullback converts the matrix-side spectral lift back to `f`.
    ext x
    simpa [Function.comp] using
      absolutely_symmetric_rectangular_diagonal_pullback_eq f hf x
  refine ⟨?_, ?_⟩
  · have hcomp :
        LowerSemicontinuous ((f ∘ singular_value_function) ∘ rectangularDiagonalProfile) :=
      hF_closed.comp continuous_rectangularDiagonal
    -- Closedness descends along the continuous rectangular diagonal embedding.
    rw [hpull] at hcomp
    exact hcomp
  · let _ : IsProperExtendedRealFunction f :=
      ⟨hf.ne_bot, hf.effective_domain_nonempty⟩
    let _ : IsProperExtendedRealFunction (f ∘ singular_value_function) := by
      refine ⟨?_, ?_⟩
      · intro X
        exact hf.ne_bot (singular_value_function X)
      · rcases hf.effective_domain_nonempty with ⟨x, hx⟩
        refine ⟨rectangularDiagonalProfile x, ?_⟩
        have hpullx :
            (f ∘ singular_value_function) (rectangularDiagonalProfile x) = f x := by
          simpa [Function.comp] using
            absolutely_symmetric_rectangular_diagonal_pullback_eq f hf x
        rw [mem_effective_domain, hpullx]
        exact hx
    rw [is_convex_function_iff_segment_ineq] at hF_convex ⊢
    intro x hx y hy t ht
    have hXeq :
        (f ∘ singular_value_function) (rectangularDiagonalProfile x) = f x := by
      -- The diagonal model turns the matrix-side profile back into the vector-side one.
      simpa using absolutely_symmetric_rectangular_diagonal_pullback_eq f hf x
    have hYeq :
        (f ∘ singular_value_function) (rectangularDiagonalProfile y) = f y := by
      simpa using absolutely_symmetric_rectangular_diagonal_pullback_eq f hf y
    have hX :
        rectangularDiagonalProfile x ∈ effective_domain (f ∘ singular_value_function) := by
      rw [mem_effective_domain, hXeq]
      simpa [mem_effective_domain] using hx
    have hY :
        rectangularDiagonalProfile y ∈ effective_domain (f ∘ singular_value_function) := by
      rw [mem_effective_domain, hYeq]
      simpa [mem_effective_domain] using hy
    have hseg :=
      hF_convex (rectangularDiagonalProfile x) hX (rectangularDiagonalProfile y) hY ht
    have hcombo :
        rectangularDiagonalProfile (t • x + (1 - t) • y) =
          t • rectangularDiagonalProfile x + (1 - t) • rectangularDiagonalProfile y :=
      rectangularDiagonal_segment x y t
    have hcomboeq :
        (f ∘ singular_value_function) (rectangularDiagonalProfile (t • x + (1 - t) • y)) =
          f (t • x + (1 - t) • y) := by
      -- The same pullback identity applies to the convex combination.
      simpa using
        absolutely_symmetric_rectangular_diagonal_pullback_eq f hf
          (t • x + (1 - t) • y)
    -- Convexity descends by evaluating the matrix inequality on diagonal matrices.
    rw [← hcombo, hcomboeq, hXeq, hYeq] at hseg
    exact hseg

/- Theorem 7.6 is `source-facing`: its owner abstractions are already present in the project as the
rectangular singular-value map `Matrix.singular_value_function`, the source symmetry condition
`Function.IsAbsolutelyPermutationSymmetric`, Mathlib's `LowerSemicontinuous` for closedness, and
Chapter 2's `is_convex_function` for convexity. The theorem is therefore best stated directly for
the spectral lift `f ∘ singular_value_function`, without introducing a new wrapper API for the
matrix-side function `F`. -/

-- Proof sketch: the forward implication is the conjugate-biconjugate argument already proved in
-- `absolutely_symmetric_spectral_closed_convex_forward`. For the reverse implication, pull the
-- matrix-side closedness and convexity back along the rectangular diagonal embedding and use the
-- source-faithful identity `σ(dg(x)) = |x|↓`.
/-- Theorem 7.6: if `f : ℝ^(min m n) → (-∞, ∞]` is absolutely permutation symmetric and proper,
then its symmetric spectral lift `f ∘ σ` to real `m × n` matrices via the singular-value map
`σ = singular_value_function` is closed and convex if and only if `f` is closed and convex. Here
closedness is expressed by `LowerSemicontinuous` and convexity by `is_convex_function`. -/
theorem absolutely_symmetric_spectral_function_closed_convex_iff
    (f : (Fin (min m n) → ℝ) → EReal) (hf : IsAbsolutelyPermutationSymmetric f) :
    (LowerSemicontinuous (f ∘ singular_value_function) ∧
      is_convex_function (f ∘ singular_value_function)) ↔
        (LowerSemicontinuous f ∧ is_convex_function f) := by
  constructor
  · rintro ⟨hF_closed, hF_convex⟩
    -- The reverse direction is just the diagonal pullback of the matrix-side properties.
    exact absolutely_symmetric_spectral_closed_convex_reverse f hf hF_closed hF_convex
  · rintro ⟨hf_closed, hf_convex⟩
    -- The forward direction is the stabilized conjugate-biconjugate proof skeleton above.
    exact absolutely_symmetric_spectral_closed_convex_forward f hf hf_closed hf_convex

end
