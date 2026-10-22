/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

open Matrix

variable {rows cols : ℕ}

local notation "Mmn" => Matrix (Fin rows) (Fin cols) ℝ
local notation "PixelIndex" => Fin rows × Fin cols

/- Definition 12.13 is `source-facing`: it introduces the two concrete matrix regularizers
`TV_I` and `TV_l1` used in two-dimensional total-variation denoising.

For this item, the public owner is the matrix-side total-variation functional itself, written as a
finite sum of site contributions with the textbook boundary convention absorbed into the site term.
The boundary extensions below are only internal bookkeeping for those site formulas, while the
derived API records the explicit textbook interior/boundary expansions used downstream by
Definitions 12.21 and 12.22. -/

private def rightBoundaryExtension
    (x : Mmn) (i : Fin rows) (j : Fin cols) : ℝ :=
  if h : j.1 + 1 < cols then x i ⟨j.1 + 1, h⟩ else x i j

private def downBoundaryExtension
    (x : Mmn) (i : Fin rows) (j : Fin cols) : ℝ :=
  if h : i.1 + 1 < rows then x ⟨i.1 + 1, h⟩ j else x i j

/-- Helper for Definition 12.13: on an interior column, the right boundary extension advances to
the next column. -/
@[simp] private theorem rightBoundaryExtension_castSucc
    (x : Matrix (Fin rows) (Fin (cols + 1)) ℝ) (i : Fin rows) (j : Fin cols) :
    rightBoundaryExtension x i (Fin.castSucc j) = x i j.succ := by
  -- The interior branch of the boundary extension is active on every `castSucc` column.
  dsimp [rightBoundaryExtension]
  split_ifs with h
  · congr 1
  · exfalso
    exact h j.succ.is_lt

/-- Helper for Definition 12.13: on the last column, the right boundary extension fixes the
current entry. -/
@[simp] private theorem rightBoundaryExtension_last
    (x : Matrix (Fin rows) (Fin (cols + 1)) ℝ) (i : Fin rows) :
    rightBoundaryExtension x i (Fin.last cols) = x i (Fin.last cols) := by
  -- The last column falls into the boundary branch, so no forward step is taken.
  simp [rightBoundaryExtension]

/-- Helper for Definition 12.13: on an interior row, the downward boundary extension advances to
the next row. -/
@[simp] private theorem downBoundaryExtension_castSucc
    (x : Matrix (Fin (rows + 1)) (Fin cols) ℝ) (i : Fin rows) (j : Fin cols) :
    downBoundaryExtension x (Fin.castSucc i) j = x i.succ j := by
  -- The interior branch of the boundary extension is active on every `castSucc` row.
  dsimp [downBoundaryExtension]
  split_ifs with h
  · congr 1
  · exfalso
    exact h i.succ.is_lt

/-- Helper for Definition 12.13: on the last row, the downward boundary extension fixes the
current entry. -/
@[simp] private theorem downBoundaryExtension_last
    (x : Matrix (Fin (rows + 1)) (Fin cols) ℝ) (j : Fin cols) :
    downBoundaryExtension x (Fin.last rows) j = x (Fin.last rows) j := by
  -- The last row falls into the boundary branch, so no downward step is taken.
  simp [downBoundaryExtension]

/-- The isotropic site contribution
`sqrt ((x_(i,j) - x_(i,j+1))^2 + (x_(i,j) - x_(i+1,j))^2)` with the boundary conventions encoded
by the total-variation boundary extensions. -/
def isotropic_two_dimensional_total_variation_site_term
    (x : Mmn) (ij : PixelIndex) : ℝ :=
  let i := ij.1
  let j := ij.2
  let xij := x i j
  let right := rightBoundaryExtension x i j
  let down := downBoundaryExtension x i j
  Real.sqrt ((xij - right) ^ (2 : ℕ) + (xij - down) ^ (2 : ℕ))

/-- The anisotropic `ℓ¹` site contribution
`|x_(i,j) - x_(i,j+1)| + |x_(i,j) - x_(i+1,j)|` with the boundary conventions encoded by the
total-variation boundary extensions. -/
def anisotropic_two_dimensional_total_variation_site_term
    (x : Mmn) (ij : PixelIndex) : ℝ :=
  let i := ij.1
  let j := ij.2
  let xij := x i j
  let right := rightBoundaryExtension x i j
  let down := downBoundaryExtension x i j
  |xij - right| + |xij - down|

/-- Helper for Definition 12.13: at an interior site, the isotropic site term is the Euclidean
norm of the horizontal and vertical forward differences. -/
@[simp] private theorem isotropic_site_term_castSucc_castSucc
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) (j : Fin cols) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.castSucc j) =
      Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
        (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) := by
  -- Both boundary extensions move to the adjacent interior entries.
  simp [isotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: on the last row, the isotropic site term collapses to the
horizontal absolute difference. -/
@[simp] private theorem isotropic_site_term_last_row
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (j : Fin cols) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.castSucc j) =
      |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
  -- The vertical difference vanishes on the last row, leaving a one-dimensional boundary term.
  calc
    isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.castSucc j) =
        Real.sqrt ((x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ) ^ (2 : ℕ)) := by
      simp [isotropic_two_dimensional_total_variation_site_term]
    _ = |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
      simpa using
        Real.sqrt_sq_eq_abs (x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ)

/-- Helper for Definition 12.13: on the last column, the isotropic site term collapses to the
vertical absolute difference. -/
@[simp] private theorem isotropic_site_term_last_col
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.last cols) =
      |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The horizontal difference vanishes on the last column, leaving a one-dimensional boundary
  -- term.
  calc
    isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.last cols) =
        Real.sqrt ((x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)) ^ (2 : ℕ)) := by
      simp [isotropic_two_dimensional_total_variation_site_term]
    _ = |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
      simpa using
        Real.sqrt_sq_eq_abs (x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols))

/-- Helper for Definition 12.13: the isotropic site term at the bottom-right corner is zero. -/
@[simp] private theorem isotropic_site_term_last_last
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.last cols) = 0 := by
  -- Both boundary extensions fix the corner entry, so both forward differences vanish.
  simp [isotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: at an interior site, the anisotropic site term is the sum of the
absolute horizontal and vertical forward differences. -/
@[simp] private theorem anisotropic_site_term_castSucc_castSucc
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) (j : Fin cols) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.castSucc j) =
      (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
        |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) := by
  -- Both boundary extensions move to the adjacent interior entries.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: on the last row, the anisotropic site term keeps only the
horizontal absolute difference. -/
@[simp] private theorem anisotropic_site_term_last_row
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (j : Fin cols) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.castSucc j) =
      |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
  -- The downward boundary extension fixes the last-row entry, so the vertical part is zero.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: on the last column, the anisotropic site term keeps only the
vertical absolute difference. -/
@[simp] private theorem anisotropic_site_term_last_col
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) (i : Fin rows) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, Fin.last cols) =
      |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The rightward boundary extension fixes the last-column entry, so the horizontal part is zero.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Helper for Definition 12.13: the anisotropic site term at the bottom-right corner is zero. -/
@[simp] private theorem anisotropic_site_term_last_last
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, Fin.last cols) = 0 := by
  -- Both forward differences vanish at the corner.
  simp [anisotropic_two_dimensional_total_variation_site_term]

/-- Definition 12.13 (1): the isotropic two-dimensional total variation of a real matrix is the
finite sum of the isotropic site contributions over all pixels. -/
def isotropic_two_dimensional_total_variation (x : Mmn) : ℝ :=
  ∑ ij : PixelIndex, isotropic_two_dimensional_total_variation_site_term x ij

notation "TV_I" => isotropic_two_dimensional_total_variation

-- Proof sketch: unfold `TV_I`; it is definitionally the finite sum of the isotropic site terms.
/-- Evaluating `TV_I` rewrites it as the finite sum of the isotropic site contributions. -/
@[simp] theorem isotropic_two_dimensional_total_variation_apply
    (x : Mmn) :
    TV_I x =
      ∑ ij : PixelIndex, isotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: when there are no rows, the index type is empty, so the isotropic site sum
-- vanishes.
/-- Evaluating `TV_I` on a matrix with no rows gives `0`. -/
@[simp] theorem isotropic_two_dimensional_total_variation_zero_rows
    (x : Matrix (Fin 0) (Fin cols) ℝ) :
    TV_I x = 0 := by
  -- With no rows, the site index set is empty.
  simp [isotropic_two_dimensional_total_variation]

-- Proof sketch: when there are no columns, the index type is empty, so the isotropic site sum
-- vanishes.
/-- Evaluating `TV_I` on a matrix with no columns gives `0`. -/
@[simp] theorem isotropic_two_dimensional_total_variation_zero_cols
    (x : Matrix (Fin rows) (Fin 0) ℝ) :
    TV_I x = 0 := by
  -- With no columns, the site index set is empty.
  simp [isotropic_two_dimensional_total_variation]

/-- Helper for Definition 12.13: on a nonempty matrix, the sum of isotropic site terms equals the
textbook interior-plus-boundary formula. -/
private theorem isotropic_two_dimensional_total_variation_site_sum_nonempty_expansion
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    (∑ ij : Fin (rows + 1) × Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x ij) =
      ∑ i : Fin rows, ∑ j : Fin cols,
        Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
          (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  have h_interior_rows :
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
      (∑ i : Fin rows, ∑ j : Fin cols,
        Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
            (2 : ℕ) +
          (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ))) +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
    -- Split each interior row into its interior columns and its last-column boundary site.
    calc
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
          isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
        ∑ i : Fin rows,
          ((∑ j : Fin cols,
              Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
                  (2 : ℕ) +
                (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^
                  (2 : ℕ))) +
            |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Fin.sum_univ_castSucc]
          simp
      _ =
          (∑ i : Fin rows, ∑ j : Fin cols,
            Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
                (2 : ℕ) +
              (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ))) +
            ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          rw [Finset.sum_add_distrib]
  have h_last_row :
      ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
    -- Split the last row into its interior columns and the vanishing bottom-right corner.
    rw [Fin.sum_univ_castSucc]
    simp
  -- Split the product index set into interior rows and the last row, then split columns inside
  -- the interior rows.
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  calc
    (∑ i : Fin rows, ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j)) +
      ∑ j : Fin (cols + 1),
        isotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ((∑ i : Fin rows, ∑ j : Fin cols,
          Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^
              (2 : ℕ) +
            (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ))) +
          ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
          rw [h_interior_rows, h_last_row]
    _ =
        ∑ i : Fin rows, ∑ j : Fin cols,
          Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
            (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          simp [add_left_comm, add_comm]

-- Proof sketch: unfold `TV_I`; it is exactly the sum over the isotropic site terms.
/-- The isotropic total variation is the finite sum of the isotropic site terms over all matrix
entries, with the boundary conventions absorbed into the site term itself. -/
theorem isotropic_two_dimensional_total_variation_eq_sum_site_terms
    (x : Mmn) :
    TV_I x =
      ∑ ij : Fin rows × Fin cols, isotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: unfold `TV_I` and then split the site sum into interior, last-row, and
-- last-column contributions.
/-- Expanding `TV_I` on a nonempty `(rows + 1) × (cols + 1)` matrix yields the textbook isotropic
two-dimensional total-variation formula in full. -/
theorem isotropic_two_dimensional_total_variation_formula
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    TV_I x =
      ∑ i : Fin rows, ∑ j : Fin cols,
        Real.sqrt ((x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ) ^ (2 : ℕ) +
          (x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)) ^ (2 : ℕ)) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The public formula is exactly the nonempty expansion of the isotropic site sum.
  simpa [isotropic_two_dimensional_total_variation] using
    isotropic_two_dimensional_total_variation_site_sum_nonempty_expansion x

/-- Definition 12.13 (2): the anisotropic `ℓ¹`-based two-dimensional total variation of a real
matrix is the finite sum of the anisotropic site contributions over all pixels. -/
def anisotropic_two_dimensional_total_variation (x : Mmn) : ℝ :=
  ∑ ij : PixelIndex, anisotropic_two_dimensional_total_variation_site_term x ij

notation "TV_l1" => anisotropic_two_dimensional_total_variation

-- Proof sketch: unfold `TV_l1`; it is definitionally the finite sum of the anisotropic site
-- terms.
/-- Evaluating `TV_l1` rewrites it as the finite sum of the anisotropic site contributions. -/
@[simp] theorem anisotropic_two_dimensional_total_variation_apply
    (x : Mmn) :
    TV_l1 x =
      ∑ ij : PixelIndex, anisotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: when there are no rows, the index type is empty, so the anisotropic site sum
-- vanishes.
/-- Evaluating `TV_l1` on a matrix with no rows gives `0`. -/
@[simp] theorem anisotropic_two_dimensional_total_variation_zero_rows
    (x : Matrix (Fin 0) (Fin cols) ℝ) :
    TV_l1 x = 0 := by
  -- With no rows, the site index set is empty.
  simp [anisotropic_two_dimensional_total_variation]

-- Proof sketch: when there are no columns, the index type is empty, so the anisotropic site sum
-- vanishes.
/-- Evaluating `TV_l1` on a matrix with no columns gives `0`. -/
@[simp] theorem anisotropic_two_dimensional_total_variation_zero_cols
    (x : Matrix (Fin rows) (Fin 0) ℝ) :
    TV_l1 x = 0 := by
  -- With no columns, the site index set is empty.
  simp [anisotropic_two_dimensional_total_variation]

/-- Helper for Definition 12.13: on a nonempty matrix, the sum of anisotropic site terms equals
the textbook interior-plus-boundary formula. -/
private theorem anisotropic_two_dimensional_total_variation_site_sum_nonempty_expansion
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    (∑ ij : Fin (rows + 1) × Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x ij) =
      ∑ i : Fin rows, ∑ j : Fin cols,
        (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
          |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  have h_interior_rows :
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
      (∑ i : Fin rows, ∑ j : Fin cols,
        (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
          |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
    -- Split each interior row into its interior columns and its last-column boundary site.
    calc
      ∑ i : Fin rows, ∑ j : Fin (cols + 1),
          anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j) =
        ∑ i : Fin rows,
          ((∑ j : Fin cols,
              (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
                |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
            |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Fin.sum_univ_castSucc]
          simp
      _ =
          (∑ i : Fin rows, ∑ j : Fin cols,
            (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
              |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
            ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          rw [Finset.sum_add_distrib]
  have h_last_row :
      ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
    -- Split the last row into its interior columns and the vanishing bottom-right corner.
    rw [Fin.sum_univ_castSucc]
    simp
  -- Split the product index set into interior rows and the last row, then split columns inside
  -- the interior rows.
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  calc
    (∑ i : Fin rows, ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.castSucc i, j)) +
      ∑ j : Fin (cols + 1),
        anisotropic_two_dimensional_total_variation_site_term x (Fin.last rows, j) =
      ((∑ i : Fin rows, ∑ j : Fin cols,
          (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
            |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|)) +
          ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)|) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| := by
          rw [h_interior_rows, h_last_row]
    _ =
        ∑ i : Fin rows, ∑ j : Fin cols,
          (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
            |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) +
        ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
        ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
          simp [add_assoc, add_comm]

-- Proof sketch: unfold `TV_l1`; it is exactly the sum over the anisotropic site terms.
/-- The anisotropic total variation is the finite sum of the anisotropic site terms over all
matrix entries, with the boundary conventions absorbed into the site term itself. -/
theorem anisotropic_two_dimensional_total_variation_eq_sum_site_terms
    (x : Mmn) :
    TV_l1 x =
      ∑ ij : Fin rows × Fin cols,
        anisotropic_two_dimensional_total_variation_site_term x ij := rfl

-- Proof sketch: unfold `TV_l1` and then split the site sum into interior, last-row, and
-- last-column contributions.
/-- Expanding `TV_l1` on a nonempty `(rows + 1) × (cols + 1)` matrix yields the textbook
anisotropic `ℓ¹`-based two-dimensional total-variation formula in full. -/
theorem anisotropic_two_dimensional_total_variation_formula
    (x : Matrix (Fin (rows + 1)) (Fin (cols + 1)) ℝ) :
    TV_l1 x =
      ∑ i : Fin rows, ∑ j : Fin cols,
        (|x (Fin.castSucc i) (Fin.castSucc j) - x (Fin.castSucc i) j.succ| +
          |x (Fin.castSucc i) (Fin.castSucc j) - x i.succ (Fin.castSucc j)|) +
      ∑ j : Fin cols, |x (Fin.last rows) (Fin.castSucc j) - x (Fin.last rows) j.succ| +
      ∑ i : Fin rows, |x (Fin.castSucc i) (Fin.last cols) - x i.succ (Fin.last cols)| := by
  -- The public formula is exactly the nonempty expansion of the anisotropic site sum.
  simpa [anisotropic_two_dimensional_total_variation] using
    anisotropic_two_dimensional_total_variation_site_sum_nonempty_expansion x

end
