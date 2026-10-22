/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

/-- Text 8.0.3: the Huber function with threshold `ρ ∈ ℝ_{++}` is quadratic on `|x| ≤ ρ` and
affine in `|x|` on `ρ < |x|`. -/
noncomputable def huberFunction (ρ : Ioi (0 : ℝ)) : ℝ → ℝ :=
  {x : ℝ | (ρ : ℝ) < |x|}.piecewise
    (fun x ↦ (ρ : ℝ) * |x| - (ρ : ℝ) ^ 2 / 2)
    (fun x ↦ |x| ^ 2 / 2)

/-- On the region `ρ < |x|`, the Huber function agrees with its affine branch. -/
-- Proof sketch: unfold `huberFunction` and simplify the defining `Set.piecewise` expression using
-- the hypothesis `(ρ : ℝ) < |x|`.
theorem huberFunction_eq_of_lt (ρ : Ioi (0 : ℝ)) {x : ℝ} (hx : (ρ : ℝ) < |x|) :
    huberFunction ρ x = (ρ : ℝ) * |x| - (ρ : ℝ) ^ 2 / 2 := by
  -- The hypothesis places `x` in the threshold set controlling the piecewise definition.
  simpa [huberFunction] using
    Set.piecewise_eq_of_mem
      (s := {y : ℝ | (ρ : ℝ) < |y|})
      (f := fun y ↦ (ρ : ℝ) * |y| - (ρ : ℝ) ^ 2 / 2)
      (g := fun y ↦ y ^ 2 / 2)
      hx

/-- On the region `|x| ≤ ρ`, the Huber function agrees with its quadratic branch. -/
-- Proof sketch: unfold `huberFunction` and simplify the defining `Set.piecewise` expression using
-- `not_lt.mpr hx` to select the quadratic case.
theorem huberFunction_eq_of_le (ρ : Ioi (0 : ℝ)) {x : ℝ} (hx : |x| ≤ (ρ : ℝ)) :
    huberFunction ρ x = |x| ^ 2 / 2 := by
  -- The complementary inequality shows that `x` is outside the threshold set.
  have hx_not_mem : x ∉ {y : ℝ | (ρ : ℝ) < |y|} := not_lt.mpr hx
  -- With the non-membership established, the piecewise definition reduces to the quadratic branch.
  simpa [huberFunction] using
    Set.piecewise_eq_of_notMem
      (s := {y : ℝ | (ρ : ℝ) < |y|})
      (f := fun y ↦ (ρ : ℝ) * |y| - (ρ : ℝ) ^ 2 / 2)
      (g := fun y ↦ y ^ 2 / 2)
      hx_not_mem
