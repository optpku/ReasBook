/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

noncomputable section

section

variable {m n : ℕ}

local notation "Mmn" => Matrix (Fin m) (Fin n) ℝ
local notation "Hmn" => Matrix (Fin m) (Fin (n - 1)) ℝ
local notation "Vmn" => Matrix (Fin (m - 1)) (Fin n) ℝ
local notation "TVSpace" => WithLp 2 (Hmn × Vmn)

/- Proposition 12.6 is `source-facing` in the two-dimensional total-variation denoising
subsection: it gives the operator-norm estimate `‖A‖² ≤ 8` for the discrete gradient map on
matrices with the Frobenius norm.

Domain sampling shows that Proposition 12.4 already owns the relevant operator at exactly the
right abstraction level:
- `core/canonical`: `two_dimensional_total_variation_difference : Mmn →ₗ[ℝ] TVSpace`, with the
  codomain measured in the canonical `WithLp 2` `L²` product norm on the horizontal/vertical
  gradient pair once this file installs the Frobenius matrix norms on `Hmn` and `Vmn` through the
  actual owner codomain `TVSpace`;
- derived API: `two_dimensional_total_variation_difference_fst` /
  `two_dimensional_total_variation_difference_snd` together with the horizontal and vertical
  difference evaluation lemmas from Proposition 12.4, and mathlib's `WithLp` `L²`-product norm
  formula;
- no extra owner is needed here: the previous local reconstruction of the difference operator was a
  duplicate wheel around the Proposition 12.4 owner.

Primitive data are therefore only the matrix `x` and the imported operator owner
`two_dimensional_total_variation_difference`; the local file keeps only the source-facing norm
statements for that owner. -/

/-- The matrix space `ℝ^(m × n)` carries its canonical Frobenius norm. -/
local instance instProposition126NormedAddCommGroupMatrix : NormedAddCommGroup Mmn :=
  Matrix.frobeniusNormedAddCommGroup

/-- Scalar multiplication on `ℝ^(m × n)` is compatible with the Frobenius norm. -/
local instance instProposition126NormedSpaceMatrix : NormedSpace ℝ Mmn :=
  Matrix.frobeniusNormedSpace

/-- The horizontal-difference matrix space carries its canonical Frobenius norm. -/
local instance instProposition126NormedAddCommGroupHorizontalMatrix : NormedAddCommGroup Hmn :=
  Matrix.frobeniusNormedAddCommGroup

/-- Scalar multiplication on the horizontal-difference matrix space is compatible with the
Frobenius norm. -/
local instance instProposition126NormedSpaceHorizontalMatrix : NormedSpace ℝ Hmn :=
  Matrix.frobeniusNormedSpace

/-- The vertical-difference matrix space carries its canonical Frobenius norm. -/
local instance instProposition126NormedAddCommGroupVerticalMatrix : NormedAddCommGroup Vmn :=
  Matrix.frobeniusNormedAddCommGroup

/-- Scalar multiplication on the vertical-difference matrix space is compatible with the
Frobenius norm. -/
local instance instProposition126NormedSpaceVerticalMatrix : NormedSpace ℝ Vmn :=
  Matrix.frobeniusNormedSpace

/-- The codomain `WithLp 2 (Hmn × Vmn)` is measured using the Frobenius norms on the horizontal and
vertical difference spaces. -/
local instance instProposition126NormedAddCommGroupTVSpace : NormedAddCommGroup TVSpace :=
  inferInstance

/-- Scalar multiplication on the `L²` product of horizontal and vertical difference matrices is
compatible with those Frobenius norms. -/
local instance instProposition126NormedSpaceTVSpace : NormedSpace ℝ TVSpace :=
  inferInstance

/-- Addition and negation on the `L²` product are continuous for its transported product
topology. -/
local instance instProposition126IsTopologicalAddGroupTVSpace :
    IsTopologicalAddGroup TVSpace :=
  Topology.IsInducing.topologicalAddGroup
    (WithLp.addEquiv (2 : ENNReal) (Hmn × Vmn))
    (WithLp.homeomorphProd (2 : ENNReal) Hmn Vmn).isInducing

/-- Scalar multiplication is continuous for the transported `L²` product topology. -/
local instance instProposition126ContinuousSMulTVSpace : ContinuousSMul ℝ TVSpace :=
  ContinuousSMul.induced (WithLp.linearEquiv (2 : ENNReal) ℝ (Hmn × Vmn))

/-- Operator norms on maps into the transported `L²` product use the standard supremum norm. -/
local instance instProposition126NormContinuousLinearMap : Norm (Mmn →L[ℝ] TVSpace) :=
  ContinuousLinearMap.hasOpNorm

/-- Helper for Proposition 12.6: squaring the Frobenius norm of a real matrix recovers the sum of
the squares of its entries. -/
lemma matrix_frobenius_norm_sq_eq_sum_sq
    (x : Mmn) :
    ‖x‖ ^ (2 : ℕ) = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
  have hnorm :
      ‖x‖ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) := by
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def x)
  -- Rewrite the Frobenius norm through the matrix-entry formula and square the resulting square
  -- root.
  calc
    ‖x‖ ^ (2 : ℕ) = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    _ = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
      simp_rw [Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.6: the same Frobenius-square identity for horizontal-difference
matrices. -/
lemma horizontal_matrix_frobenius_norm_sq_eq_sum_sq
    (x : Hmn) :
    ‖x‖ ^ (2 : ℕ) = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
  have hnorm :
      ‖x‖ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) := by
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def x)
  -- This is the Frobenius formula specialized to the horizontal edge matrix space.
  calc
    ‖x‖ ^ (2 : ℕ) = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    _ = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
      simp_rw [Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.6: the same Frobenius-square identity for vertical-difference
matrices. -/
lemma vertical_matrix_frobenius_norm_sq_eq_sum_sq
    (x : Vmn) :
    ‖x‖ ^ (2 : ℕ) = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
  have hnorm :
      ‖x‖ = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) := by
    simpa [Real.sqrt_eq_rpow] using (Matrix.frobenius_norm_def x)
  -- This is the Frobenius formula specialized to the vertical edge matrix space.
  calc
    ‖x‖ ^ (2 : ℕ) = Real.sqrt (∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [hnorm]
    _ = ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℕ) := by
      exact Real.sq_sqrt (by positivity)
    _ = ∑ i, ∑ j, x i j ^ (2 : ℕ) := by
      simp_rw [Real.norm_eq_abs, sq_abs]

/-- Helper for Proposition 12.6: each squared difference is bounded by twice the sum of the
endpoint squares. -/
lemma sq_sub_le_two_mul_add_sq (a b : ℝ) :
    (a - b) ^ (2 : ℕ) ≤ 2 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  -- Expand the square and use `2ab ≤ a² + b²`.
  nlinarith [sq_nonneg (a + b)]

/-- Helper for Proposition 12.6: in `Fin (k + 1)`, the truncated index `castLE` is just
`castSucc`. -/
lemma fin_castLE_sub_one_eq_castSucc {k : ℕ} (j : Fin k) :
    Fin.castLE (Nat.sub_le (k + 1) 1) j = j.castSucc := by
  ext
  rfl

/-- Helper for Proposition 12.6: the explicit successor index agrees with `Fin.succ`. -/
lemma fin_add_one_eq_succ {k : ℕ} (j : Fin k) :
    (⟨(j : ℕ) + 1, by omega⟩ : Fin (k + 1)) = j.succ := by
  ext
  simp

/-- Helper for Proposition 12.6: `‖A x‖²` is the sum of the horizontal and vertical edge-square
totals from the textbook formula. -/
lemma two_dimensional_total_variation_difference_norm_sq_eq_edge_sums
    (x : Mmn) :
    ‖A[m, n] x‖ ^ (2 : ℕ) =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        (x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩) ^ (2 : ℕ)) +
      (∑ i : Fin (m - 1), ∑ j : Fin n,
        (x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j) ^ (2 : ℕ)) := by
  -- Expand the `WithLp` norm into the two Frobenius norms and then unfold the difference entries.
  calc
    ‖A[m, n] x‖ ^ (2 : ℕ) = ‖(A[m, n] x).fst‖ ^ (2 : ℕ) + ‖(A[m, n] x).snd‖ ^ (2 : ℕ) := by
      simpa using WithLp.prod_norm_sq_eq_of_L2 (A[m, n] x)
    _ = ‖two_dimensional_total_variation_horizontal_difference x‖ ^ (2 : ℕ) +
          ‖two_dimensional_total_variation_vertical_difference x‖ ^ (2 : ℕ) := by
      simp
    _ =
        (∑ i : Fin m, ∑ j : Fin (n - 1),
          (x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩) ^ (2 : ℕ)) +
        (∑ i : Fin (m - 1), ∑ j : Fin n,
          (x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j) ^ (2 : ℕ)) := by
      rw [horizontal_matrix_frobenius_norm_sq_eq_sum_sq, vertical_matrix_frobenius_norm_sq_eq_sum_sq]
      simp [two_dimensional_total_variation_horizontal_difference_apply,
        two_dimensional_total_variation_vertical_difference_apply]

/-- Helper for Proposition 12.6: the horizontally adjacent endpoint-square sum with the textbook
prefactor is bounded by `4‖x‖²`. -/
lemma horizontal_edge_square_sum_le_four_mul_frobenius_sq
    (x : Mmn) :
    (∑ i : Fin m, ∑ j : Fin (n - 1),
      2 * (x i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ) +
        x i ⟨(j : ℕ) + 1, by omega⟩ ^ (2 : ℕ))) ≤
      4 * ∑ i : Fin m, ∑ j : Fin n, x i j ^ (2 : ℕ) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      -- In the successor case, the left endpoints and right endpoints are each subsums of the full
      -- Frobenius square sum, missing only one nonnegative boundary term per row.
      have h_cast :
          (∑ i : Fin m, ∑ j : Fin n, x i j.castSucc ^ (2 : ℕ)) ≤
            ∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hrow :
            ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) =
              (∑ j : Fin n, x i j.castSucc ^ (2 : ℕ)) + x i (Fin.last n) ^ (2 : ℕ) := by
          simpa using (Fin.sum_univ_castSucc (fun j : Fin (n + 1) ↦ x i j ^ (2 : ℕ)))
        have hnonneg : 0 ≤ x i (Fin.last n) ^ (2 : ℕ) := by positivity
        linarith
      have h_succ :
          (∑ i : Fin m, ∑ j : Fin n, x i j.succ ^ (2 : ℕ)) ≤
            ∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hrow :
            ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) =
              x i 0 ^ (2 : ℕ) + ∑ j : Fin n, x i j.succ ^ (2 : ℕ) := by
          simpa using (Fin.sum_univ_succ (fun j : Fin (n + 1) ↦ x i j ^ (2 : ℕ)))
        have hnonneg : 0 ≤ x i 0 ^ (2 : ℕ) := by positivity
        linarith
      have hsplit :
          (∑ i : Fin m, ∑ j : Fin n, 2 * (x i j.castSucc ^ (2 : ℕ) + x i j.succ ^ (2 : ℕ))) =
            2 * (∑ i : Fin m, ∑ j : Fin n, x i j.castSucc ^ (2 : ℕ)) +
            2 * (∑ i : Fin m, ∑ j : Fin n, x i j.succ ^ (2 : ℕ)) := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have hmain :
          (∑ i : Fin m, ∑ j : Fin n, 2 * (x i j.castSucc ^ (2 : ℕ) + x i j.succ ^ (2 : ℕ))) ≤
            4 * ∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) := by
        have hsum :
            2 * (∑ i : Fin m, ∑ j : Fin n, x i j.castSucc ^ (2 : ℕ)) +
              2 * (∑ i : Fin m, ∑ j : Fin n, x i j.succ ^ (2 : ℕ)) ≤
              2 * (∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ)) +
                2 * (∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ)) := by
          gcongr
        have hfour :
            2 * (∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ)) +
              2 * (∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ)) =
              4 * ∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) := by
          ring
        calc
          (∑ i : Fin m, ∑ j : Fin n, 2 * (x i j.castSucc ^ (2 : ℕ) + x i j.succ ^ (2 : ℕ))) =
              2 * (∑ i : Fin m, ∑ j : Fin n, x i j.castSucc ^ (2 : ℕ)) +
                2 * (∑ i : Fin m, ∑ j : Fin n, x i j.succ ^ (2 : ℕ)) := hsplit
          _ ≤
              2 * (∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ)) +
                2 * (∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ)) := hsum
          _ = 4 * ∑ i : Fin m, ∑ j : Fin (n + 1), x i j ^ (2 : ℕ) := hfour
      -- Transport the simplified successor-indexed estimate back to the original cast-heavy form.
      convert hmain using 1

/-- Helper for Proposition 12.6: the vertically adjacent endpoint-square sum with the textbook
prefactor is bounded by `4‖x‖²`. -/
lemma vertical_edge_square_sum_le_four_mul_frobenius_sq
    (x : Mmn) :
    (∑ i : Fin (m - 1), ∑ j : Fin n,
      2 * (x (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
        x ⟨(i : ℕ) + 1, by omega⟩ j ^ (2 : ℕ))) ≤
      4 * ∑ i : Fin m, ∑ j : Fin n, x i j ^ (2 : ℕ) := by
  cases m with
  | zero =>
      simp
  | succ m =>
      -- The top endpoints and bottom endpoints are each subsums of the full Frobenius square sum,
      -- again leaving only one nonnegative boundary term per column.
      have h_cast :
          (∑ i : Fin m, ∑ j : Fin n, x i.castSucc j ^ (2 : ℕ)) ≤
            ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) := by
        have hrow :
            ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) =
              (∑ i : Fin m, ∑ j : Fin n, x i.castSucc j ^ (2 : ℕ)) +
                ∑ j : Fin n, x (Fin.last m) j ^ (2 : ℕ) := by
          simpa using (Fin.sum_univ_castSucc (fun i : Fin (m + 1) ↦
            ∑ j : Fin n, x i j ^ (2 : ℕ)))
        have hnonneg : 0 ≤ ∑ j : Fin n, x (Fin.last m) j ^ (2 : ℕ) := by positivity
        linarith
      have h_succ :
          (∑ i : Fin m, ∑ j : Fin n, x i.succ j ^ (2 : ℕ)) ≤
            ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) := by
        have hrow :
            ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) =
              (∑ j : Fin n, x 0 j ^ (2 : ℕ)) +
                ∑ i : Fin m, ∑ j : Fin n, x i.succ j ^ (2 : ℕ) := by
          simpa using (Fin.sum_univ_succ (fun i : Fin (m + 1) ↦
            ∑ j : Fin n, x i j ^ (2 : ℕ)))
        have hnonneg : 0 ≤ ∑ j : Fin n, x 0 j ^ (2 : ℕ) := by positivity
        linarith
      have hsplit :
          (∑ i : Fin m, ∑ j : Fin n, 2 * (x i.castSucc j ^ (2 : ℕ) + x i.succ j ^ (2 : ℕ))) =
            2 * (∑ i : Fin m, ∑ j : Fin n, x i.castSucc j ^ (2 : ℕ)) +
            2 * (∑ i : Fin m, ∑ j : Fin n, x i.succ j ^ (2 : ℕ)) := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have hmain :
          (∑ i : Fin m, ∑ j : Fin n, 2 * (x i.castSucc j ^ (2 : ℕ) + x i.succ j ^ (2 : ℕ))) ≤
            4 * ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) := by
        have hsum :
            2 * (∑ i : Fin m, ∑ j : Fin n, x i.castSucc j ^ (2 : ℕ)) +
              2 * (∑ i : Fin m, ∑ j : Fin n, x i.succ j ^ (2 : ℕ)) ≤
              2 * (∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ)) +
                2 * (∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ)) := by
          gcongr
        have hfour :
            2 * (∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ)) +
              2 * (∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ)) =
              4 * ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) := by
          ring
        calc
          (∑ i : Fin m, ∑ j : Fin n, 2 * (x i.castSucc j ^ (2 : ℕ) + x i.succ j ^ (2 : ℕ))) =
              2 * (∑ i : Fin m, ∑ j : Fin n, x i.castSucc j ^ (2 : ℕ)) +
                2 * (∑ i : Fin m, ∑ j : Fin n, x i.succ j ^ (2 : ℕ)) := hsplit
          _ ≤
              2 * (∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ)) +
                2 * (∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ)) := hsum
          _ = 4 * ∑ i : Fin (m + 1), ∑ j : Fin n, x i j ^ (2 : ℕ) := hfour
      -- Transport the simplified successor-indexed estimate back to the original cast-heavy form.
      convert hmain using 1

-- Proof sketch: expand the `WithLp 2` norm on the codomain with
-- `ProdLp.prod_norm_sq_eq_of_L2`, rewrite the horizontal and vertical components of `A[m, n] x`
-- using Proposition 12.4, estimate each difference term by `(a - b)^2 ≤ 2 (a^2 + b^2)`, and use
-- `Matrix.frobenius_norm_def` to identify the remaining sum with `‖x‖^2`.
/-- The discrete two-dimensional TV difference operator satisfies the pointwise bound
`‖A[m, n] x‖² ≤ 8 ‖x‖²`. -/
theorem two_dimensional_total_variation_difference_norm_sq_le_eight_mul_norm_sq
    (x : Mmn) :
    ‖A[m, n] x‖ ^ (2 : ℕ) ≤ 8 * ‖x‖ ^ (2 : ℕ) := by
  -- Expand `‖A x‖²` into the two edge-square sums from the textbook formula.
  calc
    ‖A[m, n] x‖ ^ (2 : ℕ) =
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        (x i (Fin.castLE (Nat.sub_le n 1) j) - x i ⟨(j : ℕ) + 1, by omega⟩) ^ (2 : ℕ)) +
      (∑ i : Fin (m - 1), ∑ j : Fin n,
        (x (Fin.castLE (Nat.sub_le m 1) i) j - x ⟨(i : ℕ) + 1, by omega⟩ j) ^ (2 : ℕ)) := by
      exact two_dimensional_total_variation_difference_norm_sq_eq_edge_sums x
    _ ≤
      (∑ i : Fin m, ∑ j : Fin (n - 1),
        2 * (x i (Fin.castLE (Nat.sub_le n 1) j) ^ (2 : ℕ) +
          x i ⟨(j : ℕ) + 1, by omega⟩ ^ (2 : ℕ))) +
      (∑ i : Fin (m - 1), ∑ j : Fin n,
        2 * (x (Fin.castLE (Nat.sub_le m 1) i) j ^ (2 : ℕ) +
          x ⟨(i : ℕ) + 1, by omega⟩ j ^ (2 : ℕ))) := by
      -- Apply the scalar inequality to each horizontal and vertical edge term separately.
      refine add_le_add ?_ ?_
      · refine Finset.sum_le_sum ?_
        intro i hi
        refine Finset.sum_le_sum ?_
        intro j hj
        exact sq_sub_le_two_mul_add_sq _ _
      · refine Finset.sum_le_sum ?_
        intro i hi
        refine Finset.sum_le_sum ?_
        intro j hj
        exact sq_sub_le_two_mul_add_sq _ _
    _ ≤
      4 * (∑ i : Fin m, ∑ j : Fin n, x i j ^ (2 : ℕ)) +
        4 * (∑ i : Fin m, ∑ j : Fin n, x i j ^ (2 : ℕ)) := by
      -- Each matrix entry participates in at most two horizontal and at most two vertical edge
      -- terms.
      exact add_le_add
        (horizontal_edge_square_sum_le_four_mul_frobenius_sq x)
        (vertical_edge_square_sum_le_four_mul_frobenius_sq x)
    _ = 8 * (∑ i : Fin m, ∑ j : Fin n, x i j ^ (2 : ℕ)) := by
      ring
    _ = 8 * ‖x‖ ^ (2 : ℕ) := by
      rw [← matrix_frobenius_norm_sq_eq_sum_sq x]

-- Proof sketch: divide the pointwise estimate
-- `‖A x‖² ≤ 8 ‖x‖²` by `‖x‖²` for `x ≠ 0`, then apply `ContinuousLinearMap.opNorm_le_bound` to
-- the continuous linear map `A[m, n]`.
/-- Proposition 12.6: the discrete horizontal-vertical first-difference operator `A` on
`ℝ^(m × n)` satisfies the operator-norm bound `‖A‖² ≤ 8`. -/
theorem two_dimensional_total_variation_difference_opNorm_sq_le_eight :
    ‖(A[m, n]).toContinuousLinearMap‖ ^ (2 : ℕ) ≤
      8 := by
  have h_apply :
      ∀ x : Mmn, ‖(A[m, n]).toContinuousLinearMap x‖ ≤ Real.sqrt 8 * ‖x‖ := by
    intro x
    -- Compare squares first, then remove the square using nonnegativity of both sides.
    have hsquare :
        ‖(A[m, n]).toContinuousLinearMap x‖ ^ (2 : ℕ) ≤
          (Real.sqrt 8 * ‖x‖) ^ (2 : ℕ) := by
      calc
        ‖(A[m, n]).toContinuousLinearMap x‖ ^ (2 : ℕ) = ‖A[m, n] x‖ ^ (2 : ℕ) := by
          rfl
        _ ≤ 8 * ‖x‖ ^ (2 : ℕ) :=
          two_dimensional_total_variation_difference_norm_sq_le_eight_mul_norm_sq x
        _ = (Real.sqrt 8 * ‖x‖) ^ (2 : ℕ) := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have hnonneg : 0 ≤ Real.sqrt 8 * ‖x‖ := by
      positivity
    exact (sq_le_sq₀ (norm_nonneg _) hnonneg).mp hsquare
  have hopNorm :
      ‖(A[m, n]).toContinuousLinearMap‖ ≤ Real.sqrt 8 := by
    -- Feed the pointwise norm bound into the operator-norm characterization.
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 8) ?_
    intro x
    simpa [mul_comm] using h_apply x
  -- Square the operator bound and simplify `(\sqrt 8)^2`.
  calc
    ‖(A[m, n]).toContinuousLinearMap‖ ^ (2 : ℕ) ≤ (Real.sqrt 8) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hopNorm 2
    _ = 8 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

end
