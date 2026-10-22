/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {m n : ℕ}

local notation "PixelIndex" => Fin m × Fin n
local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ

namespace IsotropicTwoDimensionalTotalVariation

/-
Definition 12.22 is `source-facing`: it repartitions the isotropic two-dimensional total
variation into three sums indexed by residue classes of matrix diagonals.

Domain sampling against the nearby Chapter 12 owners gives:
- `source-facing`: the diagonal index sets `D_k`, the residue classes `K_i`, and the
  corresponding component family `ψ_i`;
- `core/canonical`: the existing regularizer `TV_I` from Definition 12.13 on
  `Matrix (Fin m) (Fin n) ℝ`;
- `bridge/view`: a decomposition of `TV_I` into three diagonal-indexed components.

The source does not define a new optimization problem or wrapper structure. The right public API
therefore keeps `TV_I` as the owner and adds the diagonal partition together with the component
functional that realizes the textbook `ψ_i`. -/

/-- The diagonal offset `k = j - i` of a matrix index `(i, j)`, using zero-based indices on
`Fin m × Fin n`. -/
private def diagonalOffset (ij : PixelIndex) : ℤ :=
  (ij.2 : ℤ) - ij.1

/-- The set `D_k` of matrix indices lying on the diagonal with offset `k = j - i`. -/
def D (m n : ℕ) (k : ℤ) : Finset (Fin m × Fin n) :=
  (Finset.univ : Finset (Fin m × Fin n)).filter fun ij ↦ diagonalOffset ij = k

/-- The residue-class block `K_(i+1)` in the partition of diagonal offsets
`{1 - m, ..., n - 1}` consisting of the offsets congruent to `i [ZMOD 3]`, with
`i : Fin 3` representing the textbook labels `1`, `2`, and `3` shifted to `0`, `1`, and `2`. -/
def K (m n : ℕ) (i : Fin 3) : Finset ℤ :=
  (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).filter fun k ↦
    k ≡ (i : ℤ) [ZMOD 3]

/-- Definition 12.22: the diagonal component `ψ_(i+1)` of `TV_I` is the sum of the isotropic cell
terms over all diagonals `D_k` whose offsets belong to the residue class `K_(i+1)`. -/
def isotropic_diagonal_component (m n : ℕ) (i : Fin 3)
    (x : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (K m n i).sum fun k ↦
    (D m n k).sum fun ij ↦
      isotropic_two_dimensional_total_variation_site_term x ij

/-- Expanding the diagonal component `ψ_(i+1)` gives the double sum over the diagonal blocks
`D_k` with `k ∈ K_(i+1)`. -/
@[simp] theorem isotropic_diagonal_component_def
    (i : Fin 3) (x : Mmn) :
    isotropic_diagonal_component m n i x =
      (K m n i).sum fun k ↦
        (D m n k).sum fun ij ↦
          isotropic_two_dimensional_total_variation_site_term x ij := by
  -- The component is definitionally the displayed double sum.
  rfl

end IsotropicTwoDimensionalTotalVariation

open IsotropicTwoDimensionalTotalVariation

local notation "D[" k "]" => D m n k
local notation "K[" i "]" => K m n i
local notation "ψ[" i "]" => isotropic_diagonal_component m n i

/- Semantic search note: `lean_leansearch` was unavailable in this runner, so the repair followed
the local Chapter 12 precedent for the ASCII owner plus source-facing `ψ[i]` notation surface. -/

/-- Helper for Definition 12.22: evaluating the diagonal component `ψ_(i+1)` in the current
context expands it into the defining double sum over the residue-class block `K_(i+1)` and its
diagonals `D_k`. -/
theorem isotropic_diagonal_component_apply
    (i : Fin 3) (x : Mmn) :
    isotropic_diagonal_component m n i x =
      (K[i]).sum fun k ↦
        (D[k]).sum fun ij ↦
          isotropic_two_dimensional_total_variation_site_term x ij := by
  -- This is the same defining formula, rewritten through the local diagonal notation.
  exact
    IsotropicTwoDimensionalTotalVariation.isotropic_diagonal_component_def
      (m := m) (n := n) i x

/-- Helper for Definition 12.22: the integer representative of a residue class `i : Fin 3`
is unchanged by reduction modulo `3`. -/
private lemma fin_cast_emod_three (i : Fin 3) : ((i : ℤ) % 3) = i := by
  -- There are only three residues, so direct case analysis closes the modulo computation.
  fin_cases i <;> norm_num

/-- Helper for Definition 12.22: every matrix index lies on a diagonal whose offset belongs to
the textbook interval `{1 - m, ..., n - 1}`. -/
private lemma diagonalOffset_mem_Icc (ij : PixelIndex) :
    diagonalOffset ij ∈ Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1) := by
  -- The bounds come from `0 ≤ i < m` and `0 ≤ j < n` for a matrix index `(i, j)`.
  rw [Finset.mem_Icc]
  have hi_nonneg : (0 : ℤ) ≤ (ij.1 : ℤ) := by
    exact_mod_cast Nat.zero_le ij.1.1
  have hj_nonneg : (0 : ℤ) ≤ (ij.2 : ℤ) := by
    exact_mod_cast Nat.zero_le ij.2.1
  have hi_lt : (ij.1 : ℤ) < (m : ℤ) := by
    exact_mod_cast ij.1.is_lt
  have hj_lt : (ij.2 : ℤ) < (n : ℤ) := by
    exact_mod_cast ij.2.is_lt
  have hi_le : (ij.1 : ℤ) ≤ (m : ℤ) - 1 := by
    omega
  have hj_le : (ij.2 : ℤ) ≤ (n : ℤ) - 1 := by
    omega
  constructor
  · have h_lower : 1 - (m : ℤ) ≤ (ij.2 : ℤ) - ij.1 := by
      omega
    simpa [diagonalOffset] using h_lower
  · have h_upper : (ij.2 : ℤ) - ij.1 ≤ (n : ℤ) - 1 := by
      omega
    simpa [diagonalOffset] using h_upper

/-- Helper for Definition 12.22: summing over all matrix entries can be regrouped fiberwise by
their diagonal offset `j - i`. -/
private lemma sum_pixels_by_diagonal_offset (F : PixelIndex → ℝ) :
    (Finset.univ : Finset PixelIndex).sum F =
      (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
        (D[k]).sum F := by
  -- Each pixel contributes exactly once, namely on the summand indexed by its own diagonal
  -- offset.
  calc
    (Finset.univ : Finset PixelIndex).sum F =
        (Finset.univ : Finset PixelIndex).sum fun ij ↦
          (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
            if diagonalOffset ij = k then F ij else 0 := by
          refine Finset.sum_congr rfl ?_
          intro ij hij
          simpa [eq_comm] using
            (Finset.sum_ite_eq_of_mem
              (s := Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1))
              (a := diagonalOffset ij)
              (b := fun _ : ℤ ↦ F ij)
              (diagonalOffset_mem_Icc (m := m) (n := n) ij))
    _ =
        (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
          (Finset.univ : Finset PixelIndex).sum fun ij ↦
            if diagonalOffset ij = k then F ij else 0 := by
          rw [Finset.sum_comm]
    _ =
        (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
          (D[k]).sum F := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          -- Repackage the indicator sum as the sum over the filtered diagonal fiber `D[k]`.
          symm
          simpa [D] using
            (Finset.sum_filter
              (s := (Finset.univ : Finset PixelIndex))
              (p := fun ij ↦ diagonalOffset ij = k)
              (f := F))

/-- Helper for Definition 12.22: the textbook block `K_(i+1)` is the filter of diagonal offsets
whose remainder modulo `3` equals the residue representative `i`. -/
private lemma K_eq_filter_emod (i : Fin 3) :
    K[i] = (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).filter fun k ↦ k % 3 = (i : ℤ) := by
  -- `Int.ModEq` is definitionally equality of remainders, and `i : Fin 3` is already reduced.
  ext k
  simp [K, Int.ModEq, fin_cast_emod_three]

/-- Helper for Definition 12.22: every integer remainder modulo `3` lies in the residue interval
`{0, 1, 2}`. -/
private lemma emod_three_mem_Icc (k : ℤ) : k % 3 ∈ Finset.Icc (0 : ℤ) 2 := by
  -- Integer remainders modulo a positive modulus are nonnegative and strictly below the modulus.
  rw [Finset.mem_Icc]
  have h_nonneg : (0 : ℤ) ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h_lt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  constructor <;> omega

/-- Helper for Definition 12.22: the diagonal-offset interval splits into the three residue-class
blocks `K[0]`, `K[1]`, and `K[2]`. -/
private lemma sum_diagonal_offsets_by_residue_class (F : ℤ → ℝ) :
    (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum F =
      (Finset.univ : Finset (Fin 3)).sum fun i ↦
        (K[i]).sum F := by
  -- Each diagonal offset contributes on exactly one residue class modulo `3`.
  calc
    (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum F =
        (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
          (Finset.univ : Finset (Fin 3)).sum fun i ↦
            if k % 3 = (i : ℤ) then F k else 0 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Fin.sum_univ_three]
          have hk_cases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
            have hk_mem := emod_three_mem_Icc k
            rw [Finset.mem_Icc] at hk_mem
            omega
          rcases hk_cases with hk0 | hk1 | hk2
          · simp [hk0]
          · simp [hk1]
          · simp [hk2]
    _ =
        (Finset.univ : Finset (Fin 3)).sum fun i ↦
          (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
            if k % 3 = (i : ℤ) then F k else 0 := by
          rw [Finset.sum_comm]
    _ =
        (Finset.univ : Finset (Fin 3)).sum fun i ↦
          (K[i]).sum F := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          -- Replace the indicator sum with the filtered block `K[i]`.
          rw [K_eq_filter_emod]
          symm
          simpa using
            (Finset.sum_filter
              (s := Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1))
              (p := fun k ↦ k % 3 = (i : ℤ))
              (f := F))

-- Proof sketch: regroup the textbook site-sum for `TV_I` by the three diagonal residue classes
-- `K[0]`, `K[1]`, and `K[2]`; this keeps the same decomposition in the `Fin 3` family form used
-- by the Chapter 12.14 finite-sum owner.
/-- The isotropic total variation is also the finite sum of the family of diagonal components
`i ↦ ψ_(i+1)`. -/
theorem isotropic_two_dimensional_total_variation_eq_sum_diagonal_components
    (x : Mmn) :
    TV_I x = ∑ i : Fin 3, ψ[i] x := by
  -- Route correction: keep the source decomposition by first regrouping pixels by diagonal
  -- offset, then regrouping those offsets by their residue class modulo `3`.
  calc
    TV_I x =
        ∑ ij : PixelIndex, isotropic_two_dimensional_total_variation_site_term x ij := by
          simp
    _ =
        (Finset.Icc (1 - (m : ℤ)) ((n : ℤ) - 1)).sum fun k ↦
          (D[k]).sum fun ij ↦
            isotropic_two_dimensional_total_variation_site_term x ij := by
          simpa using
            sum_pixels_by_diagonal_offset
              (m := m) (n := n)
              (F := fun ij ↦ isotropic_two_dimensional_total_variation_site_term x ij)
    _ =
        ∑ i : Fin 3,
          (K[i]).sum fun k ↦
            (D[k]).sum fun ij ↦
              isotropic_two_dimensional_total_variation_site_term x ij := by
          simpa using
            sum_diagonal_offsets_by_residue_class
              (m := m) (n := n)
              (F := fun k ↦
                (D[k]).sum fun ij ↦
                  isotropic_two_dimensional_total_variation_site_term x ij)
    _ = ∑ i : Fin 3, ψ[i] x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          symm
          exact isotropic_diagonal_component_apply (m := m) (n := n) i x

-- Proof sketch: apply `isotropic_two_dimensional_total_variation_eq_sum_diagonal_components` and
-- expand the
-- three-term `Fin 3` sum with `Fin.sum_univ_three`.
/-- The isotropic total variation splits as the sum of the three diagonal components
`ψ[0] + ψ[1] + ψ[2]`. -/
theorem isotropic_two_dimensional_total_variation_eq_sum_three_diagonal_components
    (x : Mmn) :
    TV_I x = ψ[0] x + ψ[1] x + ψ[2] x := by
  -- Expand the `Fin 3` index set into the three residue-class components.
  calc
    TV_I x = ∑ i : Fin 3, ψ[i] x :=
      isotropic_two_dimensional_total_variation_eq_sum_diagonal_components (m := m) (n := n) x
    _ = ψ[0] x + ψ[1] x + ψ[2] x := by
      rw [Fin.sum_univ_three]

end
