/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Text 2.0.3: a vector is orthogonal to a subset of a real inner product space if and only if it
is orthogonal to the linear span of that subset. -/
theorem mem_orthogonalComplement_iff {C : Set H} {u : H} :
    u ∈ (Submodule.span ℝ C)ᗮ ↔ ∀ x ∈ C, inner ℝ x u = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hu x hx
    exact hu x (Submodule.subset_span hx)
  · intro hu x hx
    refine Submodule.span_induction
      (fun x hx ↦ hu x hx)
      (by simp)
      (fun x y _ _ hx hy ↦ by simp [inner_add_left, hx, hy])
      (fun a x _ hx ↦ by simp [inner_smul_left, hx])
      hx
