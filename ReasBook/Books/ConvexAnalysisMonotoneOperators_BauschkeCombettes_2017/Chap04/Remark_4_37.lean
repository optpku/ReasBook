/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_35

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {α : ℝ} {T : D → H}

/-- Remark 4.37: if `T : D → H` is `α`-averaged for some `α ∈ (0, 1 / 2]`, then `T` is firmly
nonexpansive on `D`. -/
theorem firmlyNonexpansiveOn_of_averagedWith_le_half
    (hT : AveragedWith α T) (hα : α ≤ 1 / 2) :
    FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  have hαIoo : α ∈ Set.Ioo (0 : ℝ) 1 := hT.mem_Ioo
  have hresidual :=
    (averagedWith_iff_residual_sqnorm_ineq hαIoo).mp hT
  intro x y
  have hcoeff : 1 ≤ (1 - α) / α := by
    have haux : 0 ≤ (1 - 2 * α) / α := by
      exact div_nonneg (by nlinarith [hα]) hαIoo.1.le
    have hsplit : (1 - α) / α = 1 + (1 - 2 * α) / α := by
      field_simp [hαIoo.1.ne']
      ring
    nlinarith [haux, hsplit]
  have hineq :
      ‖T x - T y‖ ^ (2 : ℕ) ≤
        ‖(x : H) - y‖ ^ (2 : ℕ) -
          ‖((x : H) - T x - (y - T y))‖ ^ (2 : ℕ) := by
    have hxy := hresidual x y
    nlinarith [sq_nonneg ‖((x : H) - T x) - (y - T y)‖, hcoeff]
  have hnorm :
      ‖((x : H) - y) - (T x - T y)‖ ^ (2 : ℕ) =
        ‖(x : H) - y‖ ^ (2 : ℕ) - 2 * inner ℝ ((x : H) - y) (T x - T y) +
          ‖T x - T y‖ ^ (2 : ℕ) := by
    simpa using norm_sub_sq_real ((x : H) - y) (T x - T y)
  have hrewrite :
      ((x : H) - T x) - (y - T y) = ((x : H) - y) - (T x - T y) := by
    abel
  rw [hrewrite] at hineq
  nlinarith [hineq, hnorm]

end
