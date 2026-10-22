/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators InnerProductSpace

variable {ι : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Lemma 2.14: rewrite the exchanged cross terms as diagonal terms minus the pairwise
correction inner product. -/
-- Proof step: expand `⟪x i - x j, u i - u j⟫_ℝ` and solve the resulting real-valued identity.
private lemma pairwise_inner_exchange_identity
    (x u : ι → H) (i j : ι) :
    ⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ =
      ⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ - ⟪x i - x j, u i - u j⟫_ℝ := by
  have h_expand :
      ⟪x i - x j, u i - u j⟫_ℝ =
        ⟪x i, u i⟫_ℝ - ⟪x i, u j⟫_ℝ - ⟪x j, u i⟫_ℝ + ⟪x j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  nlinarith [h_expand]

/-- Helper for Lemma 2.14: doubling the inner product of two weighted affine combinations produces
the symmetric double sum of exchanged cross terms. -/
-- Proof step: first expand the affine-combination inner product into a double sum, then symmetrize the
-- second copy by swapping the finite summation order.
private lemma two_mul_weighted_inner_eq_sum_cross_terms
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) :
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
      ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
  have h_single :
      ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
        ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ := by
    -- Expand the two weighted sums using bilinearity of the real inner product.
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    ring_nf
  calc
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ)
            + (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) := by
              rw [h_single]
              ring
    _ = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ)
          + (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u i⟫_ℝ) := by
            congr 1
            -- Commute the second double sum so it matches the exchanged cross term.
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_comm (α j) (α i), real_inner_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
          -- Repackage the two double sums into the pointwise sum required by the textbook proof.
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Lemma 2.14: the diagonal double sum collapses to twice the weighted diagonal sum
when the weights add up to `1`. -/
-- Proof step: separate the two diagonal contributions and use the weight-sum hypothesis on each.
private lemma weighted_double_sum_diagonal_eq_two_mul_sum
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ)
    (hα : (∑ i ∈ s, α i) = 1) :
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) =
      2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  calc
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ)
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ)
            + (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u j⟫_ℝ) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) + (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            -- Freeze the `i`-diagonal term and sum the weights over `j`.
            calc
              ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ
                  = α i * ∑ j ∈ s, α j * ⟪x i, u i⟫_ℝ := by
                      simpa [mul_assoc] using
                        (Finset.mul_sum s (fun j ↦ α j * ⟪x i, u i⟫_ℝ) (α i)).symm
              _ = α i * ((∑ j ∈ s, α j) * ⟪x i, u i⟫_ℝ) := by rw [Finset.sum_mul]
              _ = α i * ⟪x i, u i⟫_ℝ := by rw [hα, one_mul]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            -- After commuting the sums, the same collapse applies to the `j`-diagonal term.
            calc
              ∑ i ∈ s, α i * α j * ⟪x j, u j⟫_ℝ
                  = (∑ i ∈ s, α i) * (α j * ⟪x j, u j⟫_ℝ) := by
                      simpa [mul_assoc] using
                        (Finset.sum_mul s (fun i ↦ α i) (α j * ⟪x j, u j⟫_ℝ)).symm
              _ = α j * ⟪x j, u j⟫_ℝ := by rw [hα, one_mul]
    _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by ring

/-- Lemma 2.14 (1): for a finite real-weighted family in a real inner product space whose weights
sum to `1`, the inner product of the two weighted affine combinations plus the half pairwise
correction term equals the weighted sum of the diagonal inner products. -/
-- Proof sketch: expand the left-hand inner product by bilinearity, rewrite
-- `⟪x i - x j, u i - u j⟫_ℝ`, and use the hypothesis `(∑ i ∈ s, α i) = 1` twice to collapse the
-- double sum of diagonal terms to `2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ`.
theorem weighted_inner_eq_sum_inner_add_half_pairwise
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) (hα : (∑ i ∈ s, α i) = 1) :
    ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
      ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  have h_two :
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
        2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
    calc
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ
          = (∑ i ∈ s, ∑ j ∈ s, α i * α j *
                (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ))
              + ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ := by
              -- Replace the doubled affine-combination inner product by its symmetric double-sum expansion.
              rw [two_mul_weighted_inner_eq_sum_cross_terms]
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j *
            ((⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) + ⟪x i - x j, u i - u j⟫_ℝ) := by
              -- Merge the correction term into the same double sum so the pointwise rewrite applies.
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) := by
              -- Rewrite each exchanged pair by the diagonal terms from the previous helper lemma.
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [pairwise_inner_exchange_identity]
              ring
      _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ :=
            weighted_double_sum_diagonal_eq_two_mul_sum s x u α hα
  -- Divide the doubled identity by `2`.
  linarith

/-- Lemma 2.14 (2): for a finite real-weighted family in a real inner product space whose weights
sum to `1`, the squared norm of the weighted affine combination plus the half pairwise correction
term equals the weighted sum of the squared norms. -/
-- Proof sketch: apply part (1) to the same family twice, taking `u = x`, and simplify
-- `⟪y, y⟫_ℝ` to `‖y‖ ^ 2` in a real inner product space.
theorem weighted_norm_sq_eq_sum_norm_sq_add_half_pairwise
    (s : Finset ι) (x : ι → H) (α : ι → ℝ) (hα : (∑ i ∈ s, α i) = 1) :
    ‖∑ i ∈ s, α i • x i‖ ^ (2 : ℕ) +
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ‖x i - x j‖ ^ (2 : ℕ) =
      ∑ i ∈ s, α i * ‖x i‖ ^ (2 : ℕ) := by
  -- Specialize part (1) to `u = x` and rewrite self-inner products as squared norms.
  simpa [real_inner_self_eq_norm_sq] using
    weighted_inner_eq_sum_inner_add_half_pairwise s x x α hα
