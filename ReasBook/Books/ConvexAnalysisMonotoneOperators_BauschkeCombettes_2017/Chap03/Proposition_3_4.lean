/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

variable {𝓗 : Type u} [AddCommGroup 𝓗] [Module ℝ 𝓗]

/- Proposition 3.4: for a subset `C` of a real vector space `𝓗`, the convex hull `convexHull ℝ C`
is exactly the set of finite convex combinations of points of `C`, expressed canonically in
mathlib by `convexHull_eq` using finite centers of mass with nonnegative coefficients summing
to `1`. -/
recall convexHull_eq

/-- Textbook membership form of Proposition 3.4: a point lies in `convexHull ℝ C` exactly when it
is a finite center of mass of points of `C` with nonnegative weights summing to `1`. -/
theorem mem_convexHull_iff_exists_finset_centerMass (C : Set 𝓗) (x : 𝓗) :
    x ∈ convexHull ℝ C ↔
      ∃ ι : Type, ∃ t : Finset ι, ∃ w : ι → ℝ, ∃ z : ι → 𝓗,
        (∀ i ∈ t, 0 ≤ w i) ∧
          ∑ i ∈ t, w i = 1 ∧
          (∀ i ∈ t, z i ∈ C) ∧
          t.centerMass w z = x := by
  rw [convexHull_eq]
  simp only [Set.mem_setOf_eq]
