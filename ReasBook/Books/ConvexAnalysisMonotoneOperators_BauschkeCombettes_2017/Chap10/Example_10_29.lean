/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_27

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open AffineMap

section

variable {f : ℝ → EReal}

private theorem convexCombo_lt_right {x y α : ℝ} (hxy : x < y) (hα0 : 0 < α) :
    α • x + (1 - α) • y < y := by
  rw [show α • x + (1 - α) • y = lineMap x y (1 - α) by simp [lineMap_apply_module]]
  exact (lineMap_lt_right_iff_lt_one hxy).2 (by linarith)

private theorem left_lt_convexCombo {x y α : ℝ} (hxy : x < y) (hα1 : α < 1) :
    x < α • x + (1 - α) • y := by
  rw [show α • x + (1 - α) • y = lineMap x y (1 - α) by simp [lineMap_apply_module]]
  exact (left_lt_lineMap_iff_pos hxy).2 (sub_pos.mpr hα1)

/-- On a convex effective domain, strict monotonicity of an extended-real-valued real function
implies strict quasiconvexity. -/
-- Proof sketch: convexity of `dom f` keeps the strict convex combination in the domain. Split on
-- the order of `x` and `y`; the combination lies strictly between the endpoints, so strict
-- monotonicity compares it with the larger endpoint value, which is exactly the endpoint maximum.
theorem strictlyQuasiconvex_of_strictMonoOn_dom
    (hproper : IsProper f) (hdom : Convex ℝ (dom f)) (hf : StrictMonoOn f (dom f)) :
    StrictlyQuasiconvex f := by
  refine ⟨hproper, ?_⟩
  intro x y hx hy hxy α hα0 hα1
  have hz : α • x + (1 - α) • y ∈ dom f := by
    exact hdom hx hy hα0.le (sub_nonneg.mpr hα1.le) (by ring)
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · have hz_lt_y : α • x + (1 - α) • y < y :=
      convexCombo_lt_right hxy hα0
    have hfx_lt_fy : f x < f y := hf hx hy hxy
    have hfz_lt_fy : f (α • x + (1 - α) • y) < f y := hf hz hy hz_lt_y
    simpa [max_eq_right hfx_lt_fy.le] using hfz_lt_fy
  · have hz_lt_x : α • x + (1 - α) • y < x := by
      simpa [add_comm] using convexCombo_lt_right hxy (sub_pos.mpr hα1)
    have hfy_lt_fx : f y < f x := hf hy hx hxy
    have hfz_lt_fx : f (α • x + (1 - α) • y) < f x := hf hz hx hz_lt_x
    simpa [max_eq_left hfy_lt_fx.le] using hfz_lt_fx

/-- On a convex effective domain, strict antitonicity of an extended-real-valued real function
implies strict quasiconvexity. -/
-- Proof sketch: convexity of `dom f` keeps the strict convex combination in the domain. Split on
-- the order of `x` and `y`; strict antitonicity compares the interior point with the larger
-- function-value endpoint, which again matches the endpoint maximum.
theorem strictlyQuasiconvex_of_strictAntiOn_dom
    (hproper : IsProper f) (hdom : Convex ℝ (dom f)) (hf : StrictAntiOn f (dom f)) :
    StrictlyQuasiconvex f := by
  refine ⟨hproper, ?_⟩
  intro x y hx hy hxy α hα0 hα1
  have hz : α • x + (1 - α) • y ∈ dom f := by
    exact hdom hx hy hα0.le (sub_nonneg.mpr hα1.le) (by ring)
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · have hx_lt_z : x < α • x + (1 - α) • y :=
      left_lt_convexCombo hxy hα1
    have hfy_lt_fx : f y < f x := hf hx hy hxy
    have hfz_lt_fx : f (α • x + (1 - α) • y) < f x := hf hx hz hx_lt_z
    simpa [max_eq_left hfy_lt_fx.le] using hfz_lt_fx
  · have hy_lt_z : y < α • x + (1 - α) • y := by
      simpa [add_comm] using left_lt_convexCombo hxy (sub_lt_self 1 hα0)
    have hfx_lt_fy : f x < f y := hf hy hx hxy
    have hfz_lt_fy : f (α • x + (1 - α) • y) < f y := hf hy hz hy_lt_z
    simpa [max_eq_right hfx_lt_fy.le] using hfz_lt_fy

/-- Example 10.29: for a proper function, strict monotonicity or strict antitonicity on a convex
effective domain implies strict quasiconvexity. -/
-- Proof sketch: split into the strictly increasing and strictly decreasing cases on `dom f`, then
-- apply the corresponding strict-quasiconvexity theorem.
theorem strictlyQuasiconvex_of_strictMonoOn_dom_or_strictAntiOn_dom
    (hproper : IsProper f) (hdom : Convex ℝ (dom f))
    (hf : StrictMonoOn f (dom f) ∨ StrictAntiOn f (dom f)) :
    StrictlyQuasiconvex f := by
  rcases hf with hmono | hanti
  · exact strictlyQuasiconvex_of_strictMonoOn_dom hproper hdom hmono
  · exact strictlyQuasiconvex_of_strictAntiOn_dom hproper hdom hanti

end
