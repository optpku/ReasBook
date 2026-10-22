/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/- Definition 3.1: for a subset `C` of a real `ℝ`-module `E` (hence in particular of a real
vector space), convexity is the canonical predicate `Convex ℝ C`. -/
recall Convex

-- Proof sketch: specialize `convex_iff_pointwise_add_subset` to coefficients `a` and `1 - a`,
-- then use `0 < a` and `a < 1` to obtain the required nonnegativity hypotheses; conversely,
-- recover the textbook one-parameter form from the standard two-parameter characterization.
/-- The textbook pointwise characterization of convexity says that `C` is closed under
combinations `a • x + (1 - a) • y` with `0 < a < 1`, expressed setwise as
`a • C + (1 - a) • C ⊆ C`. -/
theorem convex_iff_smul_add_smul_subset_of_lt_one (C : Set E) :
    Convex ℝ C ↔ ∀ a : ℝ, 0 < a → a < 1 → a • C + (1 - a) • C ⊆ C := by
  constructor
  · intro hC a ha hlt
    exact hC.set_combo_subset ha.le (sub_nonneg.mpr hlt.le) (by ring)
  · intro hC
    refine convex_iff_forall_pos.2 ?_
    intro x hx y hy a b ha hb hab
    have hsubset : a • C + (1 - a) • C ⊆ C := hC a ha (by linarith)
    have hmem : a • x + (1 - a) • y ∈ a • C + (1 - a) • C :=
      Set.add_mem_add ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hb' : b = 1 - a := by linarith
    exact hsubset (by simpa [hb'] using hmem)

/- Companion recall: a convex set is equivalently closed under pointwise convex combinations
`a • C + b • C` with nonnegative coefficients summing to `1`; specializing to `b = 1 - a`
recovers the textbook formula `a C + (1 - a) C ⊆ C` for `0 < a < 1`. -/
recall convex_iff_pointwise_add_subset

/- Companion recall: the textbook open-segment characterization of convexity is the standard theorem
`convex_iff_openSegment_subset`, whose `ℝ`-specialization matches the formulation using
open line segments `]x,y[`. -/
recall convex_iff_openSegment_subset
