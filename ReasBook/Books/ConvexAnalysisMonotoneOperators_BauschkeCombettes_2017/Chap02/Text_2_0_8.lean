/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The level set of a real linear functional at the scalar `η`. -/
def hyperplane (f : H →ₗ[ℝ] ℝ) (η : ℝ) : Set H :=
  {x | f x = η}

/-- Text 2.0.8: a hyperplane in a real Hilbert space is a level set of a nonzero real linear
functional. -/
def is_hyperplane (s : Set H) : Prop :=
  ∃ f : H →ₗ[ℝ] ℝ, f ≠ 0 ∧ ∃ η : ℝ, s = hyperplane f η

-- Proof sketch: unfold `hyperplane`; membership is definitionally the equation `f x = η`.
/-- Membership in `hyperplane f η` is the defining linear-functional equation. -/
theorem mem_hyperplane_iff {f : H →ₗ[ℝ] ℝ} {η : ℝ} {x : H} :
    x ∈ hyperplane f η ↔ f x = η :=
  Iff.rfl

-- Proof sketch: use `f` and `η` as the witnesses in the defining existential statement for
-- `is_hyperplane`.
/-- The level set of a nonzero real linear functional is a hyperplane. -/
theorem hyperplane_is_hyperplane (f : H →ₗ[ℝ] ℝ) (hf : f ≠ 0) (η : ℝ) :
    is_hyperplane (hyperplane f η) :=
  ⟨f, hf, η, rfl⟩

-- Proof sketch: use `f` and `η` as the witnesses in the defining existential statement for
-- `is_hyperplane`.
/-- The level set of a nonzero real linear functional is a hyperplane. -/
theorem is_hyperplane_setOf_eq (f : H →ₗ[ℝ] ℝ) (hf : f ≠ 0) (η : ℝ) :
    is_hyperplane {x | f x = η} := by
  simpa [hyperplane] using hyperplane_is_hyperplane f hf η
