/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

/-- Helper for Example 10.21: if two extended-real values both lie below the same real level `ξ`,
then every positive convex combination of them also lies below `ξ`. -/
private lemma weighted_sum_le_level_of_le_level (ξ : ℝ) {u v : EReal} {a b : ℝ}
    (hu : u ≤ (ξ : EReal)) (hv : v ≤ (ξ : EReal)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    (a : EReal) * u + (b : EReal) * v ≤ (ξ : EReal) := by
  have hu_weighted :
      (a : EReal) * u ≤ (a : EReal) * (ξ : EReal) :=
    mul_le_mul_of_nonneg_left hu (by exact_mod_cast ha)
  have hv_weighted :
      (b : EReal) * v ≤ (b : EReal) * (ξ : EReal) :=
    mul_le_mul_of_nonneg_left hv (by exact_mod_cast hb)
  calc
    (a : EReal) * u + (b : EReal) * v
        ≤ (a : EReal) * (ξ : EReal) + (b : EReal) * (ξ : EReal) :=
      add_le_add hu_weighted hv_weighted
    _ = ((a * ξ + b * ξ : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    _ = (ξ : EReal) := by
      have hsum : a * ξ + b * ξ = ξ := by
        simpa [add_mul] using congrArg (fun t : ℝ ↦ t * ξ) hab
      simpa using congrArg (fun t : ℝ ↦ (t : EReal)) hsum

/-- Example 10.21: every convex extended-real-valued function on the whole space is quasiconvex
on the whole space. -/
-- Proof sketch: `IsConvex f` is the source-facing Chapter 9 owner. Show directly that each real
-- lower level set is convex, then apply the canonical global quasiconvexity criterion from
-- Definition 10.20.
theorem quasiconvexOn_univ_of_convex
    {H : Type u} [AddCommMonoid H] [Module ℝ H] {f : H → EReal}
    (hf : IsConvex f) :
    QuasiconvexOn ℝ Set.univ f := by
  rw [quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ f]
  intro ξ
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  have ha_le : a ≤ 1 := by linarith
  have hb_eq : b = 1 - a := by linarith
  have hconv :
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
    simpa [hb_eq] using (hf ha.le ha_le)
  rw [mem_lowerLevelSet_iff]
  exact hconv.trans <|
    weighted_sum_le_level_of_le_level ξ
      ((mem_lowerLevelSet_iff f ξ x).mp hx)
      ((mem_lowerLevelSet_iff f ξ y).mp hy)
      ha.le hb.le hab

end ERealFunction
