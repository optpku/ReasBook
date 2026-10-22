/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

/-- Proposition 10.26: an extended-real-valued function is quasiconvex exactly when every strict
convex combination of two points in its domain has value bounded above by the maximum of the two
endpoint values. -/
-- Proof sketch: compare the textbook formulation with mathlib's canonical
-- `quasiconvexOn_iff_le_max` on `univ`. One direction is immediate by restricting the ambient
-- inequality to points of `dom f` and strict coefficients `0 < α < 1`; for the converse, treat
-- the cases `α = 0` and `α = 1` separately and use that points outside `dom f` contribute the
-- trivial bound `≤ ⊤`.
theorem quasiconvexOn_univ_iff_le_max_on_dom {f : H → EReal} :
    QuasiconvexOn ℝ Set.univ f ↔
      ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → ∀ ⦃α : ℝ⦄, α ∈ Set.Ioo (0 : ℝ) 1 →
        f (α • x + (1 - α) • y) ≤ max (f x) (f y) := by
  constructor
  · intro hf x y _ _ α hα
    rcases quasiconvexOn_iff_le_max.1 hf with ⟨_, hmax⟩
    exact hmax (by simp) (by simp) hα.1.le (sub_nonneg.mpr hα.2.le) (by ring)
  · intro h
    refine quasiconvexOn_iff_le_max.2 ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [ha0, hb1]
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simp [hb0, ha1]
      · by_cases hx : x ∈ dom f
        · by_cases hy : y ∈ dom f
          · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
            have hb_eq : b = 1 - a := by linarith
            have ha_mem : a ∈ Set.Ioo (0 : ℝ) 1 := by
              constructor
              · exact ha_pos
              · linarith
            simpa [hb_eq] using h hx hy ha_mem
          · rw [not_mem_dom_iff] at hy
            simp [hy]
        · rw [not_mem_dom_iff] at hx
          simp [hx]

end ERealFunction
