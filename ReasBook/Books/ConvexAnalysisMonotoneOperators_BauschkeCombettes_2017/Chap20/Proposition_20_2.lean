/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The four-point squared-norm inequality is exactly the monotonicity inner-product inequality
written through the canonical norm-square expansion. -/
theorem four_point_sq_norm_inequality_iff_inner_nonneg (x u y v : H) :
    0 ≤ ⟪x - y, u - v⟫_ℝ ↔
      ‖y - u‖ ^ 2 + ‖x - v‖ ^ 2 ≥ ‖x - u‖ ^ 2 + ‖y - v‖ ^ 2 := by
  have hinner :
      ⟪x - y, u - v⟫_ℝ = ⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ - ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ := by
    calc
      ⟪x - y, u - v⟫_ℝ = ⟪x, u - v⟫_ℝ - ⟪y, u - v⟫_ℝ := by
        rw [inner_sub_left]
      _ = (⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ) - (⟪y, u⟫_ℝ - ⟪y, v⟫_ℝ) := by
        rw [inner_sub_right, inner_sub_right]
      _ = ⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ - ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ := by ring
  have hnorm :
      ‖y - u‖ ^ 2 + ‖x - v‖ ^ 2 - (‖x - u‖ ^ 2 + ‖y - v‖ ^ 2) =
        2 * ⟪x - y, u - v⟫_ℝ := by
    nlinarith [norm_sub_sq_real y u, norm_sub_sq_real x v, norm_sub_sq_real x u,
      norm_sub_sq_real y v, hinner]
  constructor
  · intro h
    nlinarith [hnorm, h]
  · intro h
    nlinarith [hnorm, h]

-- Proof sketch: combine Definition 20.1 with Lemma 2.13 applied to `x - y` and `v - u`.
/-- Proposition 20.2(ii): a set-valued operator is monotone exactly when every graph pair satisfies
the accretive norm inequality `‖x - y + α • (u - v)‖ ≥ ‖x - y‖` for all `α ∈ [0,1]`. -/
theorem isMonotone_iff_accretive_norm_inequality (A : SetValuedOperator H H) :
    A.IsMonotone ↔
      ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y →
        ∀ α : Set.Icc (0 : ℝ) 1, ‖x - y + (α : ℝ) • (u - v)‖ ≥ ‖x - y‖ := by
  rw [isMonotone_iff]
  constructor
  · intro h x u y v hu hv α
    have hmono : 0 ≤ ⟪x - y, u - v⟫_ℝ := h hu hv
    have hswap : ⟪x - y, v - u⟫_ℝ = -⟪x - y, u - v⟫_ℝ := by
      calc
        ⟪x - y, v - u⟫_ℝ = ⟪x - y, -(u - v)⟫_ℝ := by
          simp [sub_eq_add_neg]
        _ = -⟪x - y, u - v⟫_ℝ := by rw [inner_neg_right]
    have hnonpos : ⟪x - y, v - u⟫_ℝ ≤ 0 := by
      rw [hswap]
      exact neg_nonpos.mpr hmono
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (real_inner_nonpos_iff_norm_le_sub_smul_unitInterval (x - y) (v - u)).mp hnonpos α
  · intro h x u y v hu hv
    have hswap : ⟪x - y, v - u⟫_ℝ = -⟪x - y, u - v⟫_ℝ := by
      calc
        ⟪x - y, v - u⟫_ℝ = ⟪x - y, -(u - v)⟫_ℝ := by
          simp [sub_eq_add_neg]
        _ = -⟪x - y, u - v⟫_ℝ := by rw [inner_neg_right]
    have hnonpos : ⟪x - y, v - u⟫_ℝ ≤ 0 := by
      refine (real_inner_nonpos_iff_norm_le_sub_smul_unitInterval (x - y) (v - u)).mpr
        fun α ↦ ?_
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h hu hv α
    rw [hswap] at hnonpos
    exact neg_nonpos.mp hnonpos

-- Proof sketch: expand the norm-square defect with Lemma 2.12 and compare with Definition 20.1.
/-- Proposition 20.2(iii): a set-valued operator is monotone exactly when every two graph points
satisfy the four-point squared-norm inequality. -/
theorem isMonotone_iff_four_point_sq_norm_inequality (A : SetValuedOperator H H) :
    A.IsMonotone ↔
      ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y →
        ‖y - u‖ ^ 2 + ‖x - v‖ ^ 2 ≥ ‖x - u‖ ^ 2 + ‖y - v‖ ^ 2 := by
  rw [isMonotone_iff]
  constructor
  · intro h x u y v hu hv
    exact (four_point_sq_norm_inequality_iff_inner_nonneg x u y v).mp (h hu hv)
  · intro h x u y v hu hv
    exact (four_point_sq_norm_inequality_iff_inner_nonneg x u y v).mpr (h hu hv)

-- Proof sketch: combine the preceding two characterizations with Definition 20.1, which is clause
-- `(i)` in the textbook formulation.
/-- Proposition 20.2: for a set-valued operator on a real Hilbert space, the following are
equivalent: (i) for every `u ∈ A x` and `v ∈ A y`, one has `0 ≤ ⟪x - y, u - v⟫_ℝ`; (ii) for
every `u ∈ A x`, `v ∈ A y`, and `α ∈ [0,1]`, one has `‖x - y + α • (u - v)‖ ≥ ‖x - y‖`; (iii)
for every `u ∈ A x` and `v ∈ A y`, one has
`‖y - u‖^2 + ‖x - v‖^2 ≥ ‖x - u‖^2 + ‖y - v‖^2`. -/
theorem tfae_monotone_accretive_four_point_sq_norm (A : SetValuedOperator H H) :
    List.TFAE
      [A.IsMonotone,
        (∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y →
          ∀ α : Set.Icc (0 : ℝ) 1, ‖x - y + (α : ℝ) • (u - v)‖ ≥ ‖x - y‖),
        (∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y →
          ‖y - u‖ ^ 2 + ‖x - v‖ ^ 2 ≥ ‖x - u‖ ^ 2 + ‖y - v‖ ^ 2)] := by
  tfae_have 1 ↔ 2 := isMonotone_iff_accretive_norm_inequality A
  tfae_have 1 ↔ 3 := isMonotone_iff_four_point_sq_norm_inequality A
  tfae_finish

end SetValuedOperator
