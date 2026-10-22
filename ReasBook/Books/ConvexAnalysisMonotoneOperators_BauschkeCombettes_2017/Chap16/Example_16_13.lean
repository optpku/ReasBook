/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise Set

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: for `x ∈ C`, unfold `(∂ ι[C]) x`; the indicator is `0` on `C` and `⊤` off `C`,
-- so the subgradient inequality reduces to `⟪y - x, u⟫ ≤ 0` for all `y ∈ C`, which is exactly
-- the defining inequality of `N[C] x`. For `x ∉ C`, nonemptiness of `C` furnishes `y ∈ C`,
-- forcing the subdifferential to be empty, matching `normalCone_of_not_mem`.
/-- Example 16.13: for a nonempty subset `C` of a real Hilbert space, hence in particular for a
nonempty convex subset, the subdifferential of the indicator `ι_C` is exactly the normal cone
mapping `N_C`. -/
theorem subdifferential_setIndicator_eq_normalCone
    (C : Set H) (hC_nonempty : C.Nonempty) :
    ∂ ι[C] = N[C] := by
  ext x u
  by_cases hx : x ∈ C
  · rw [Set.normalCone_of_mem hx, mem_subdifferential_iff]
    have hsup_iff :
        innerSupremumOn (C - ({x} : Set H)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
      exact
        (innerSupremumOn_sub_singleton_le_zero_iff :
          innerSupremumOn (C - ({x} : Set H)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0)
    constructor
    · intro hu
      refine hsup_iff.2 ?_
      intro y hy
      have hy' :
          ((⟪y - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤ (ι[C] y : EReal)) :=
        hu y
      have hinner : (⟪y - x, u⟫_ℝ : EReal) ≤ 0 := by
        simpa [ERealFunction.indicator, hx, hy] using hy'
      exact_mod_cast hinner
    · intro hu y
      by_cases hy : y ∈ C
      · have hinner : ⟪y - x, u⟫_ℝ ≤ 0 := hsup_iff.1 hu y hy
        have hx_zero : (ι[C] x : EReal) = 0 := by
          simp [ERealFunction.indicator, hx]
        have hy_zero : (ι[C] y : EReal) = 0 := by
          simp [ERealFunction.indicator, hy]
        change ((⟪y - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤ (ι[C] y : EReal))
        rw [hx_zero, hy_zero]
        simpa using (show ((⟪y - x, u⟫_ℝ : EReal) ≤ (0 : EReal)) by
          exact_mod_cast hinner)
      · have hx_zero : (ι[C] x : EReal) = 0 := by
          simp [ERealFunction.indicator, hx]
        have hy_top : (ι[C] y : EReal) = ⊤ := by
          simp [ERealFunction.indicator, hy]
        change ((⟪y - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤ (ι[C] y : EReal))
        rw [hx_zero, hy_top]
        simp
  · rw [Set.normalCone_of_not_mem hx, mem_subdifferential_iff]
    constructor
    · intro hu
      have hy :
          ((⟪hC_nonempty.choose - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤
            (ι[C] hC_nonempty.choose : EReal)) :=
        hu hC_nonempty.choose
      have hx_top : (ι[C] x : EReal) = ⊤ := by
        simp [ERealFunction.indicator, hx]
      have hchoose_zero : (ι[C] hC_nonempty.choose : EReal) = 0 := by
        simp [ERealFunction.indicator, hC_nonempty.choose_spec]
      rw [hx_top, hchoose_zero] at hy
      simp at hy
    · simp

end
