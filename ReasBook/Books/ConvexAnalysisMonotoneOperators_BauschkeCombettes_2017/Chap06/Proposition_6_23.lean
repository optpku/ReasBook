/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Proposition 6.23: the source-facing orthogonal set of a submodule is exactly its
standard orthogonal complement. -/
theorem orthogonalSet_eq_submodule_orthogonal (C : Submodule ℝ E) :
    orthogonalSet (C : Set E) = (Cᗮ : Set E) := by
  -- Rewrite both set memberships to the same pointwise orthogonality condition.
  ext u
  simpa [mem_orthogonalSet] using (C.mem_orthogonal u).symm

/-- Helper for Proposition 6.23: on a submodule, a nonpositive inner-product condition against
every vector already forces orthogonality. -/
lemma forall_inner_nonpos_iff_mem_orthogonal (C : Submodule ℝ E) {u : E} :
    (∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0) ↔ u ∈ Cᗮ := by
  constructor
  · intro hu
    rw [C.mem_orthogonal u]
    intro x hx
    -- Test the inequality on `x` and `-x` to squeeze the inner product to zero.
    have h_nonpos : ⟪x, u⟫_ℝ ≤ 0 := hu x hx
    have h_neg_nonpos : ⟪-x, u⟫_ℝ ≤ 0 := hu (-x) (C.neg_mem hx)
    have h_nonneg : 0 ≤ ⟪x, u⟫_ℝ := by
      simpa [inner_neg_left] using h_neg_nonpos
    linarith
  · intro hu x hx
    -- Orthogonality immediately gives the required nonpositive inequality.
    have h_zero : ⟪x, u⟫_ℝ = 0 := (C.mem_orthogonal u).mp hu x hx
    linarith

/-- Helper for Proposition 6.23: on a submodule, a nonnegative inner-product condition against
every vector already forces orthogonality. -/
lemma forall_inner_nonneg_iff_mem_orthogonal (C : Submodule ℝ E) {u : E} :
    (∀ x ∈ C, 0 ≤ ⟪x, u⟫_ℝ) ↔ u ∈ Cᗮ := by
  constructor
  · intro hu
    rw [C.mem_orthogonal u]
    intro x hx
    -- Again use both `x` and `-x` in the symmetric submodule to force vanishing.
    have h_nonneg : 0 ≤ ⟪x, u⟫_ℝ := hu x hx
    have h_neg_nonneg : 0 ≤ ⟪-x, u⟫_ℝ := hu (-x) (C.neg_mem hx)
    have h_nonpos : ⟪x, u⟫_ℝ ≤ 0 := by
      simpa [inner_neg_left] using h_neg_nonneg
    linarith
  · intro hu x hx
    -- Orthogonality immediately gives the required nonnegative inequality.
    have h_zero : ⟪x, u⟫_ℝ = 0 := (C.mem_orthogonal u).mp hu x hx
    linarith

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: use `mem_negativePolar`, `mem_positivePolar`, and `Submodule.mem_orthogonal`.
-- Because a submodule is closed under negation, the nonpositive and nonnegative inner-product
-- inequalities force vanishing, and conversely vanishing implies both inequalities.
/-- Proposition 6.23: if `C` is a linear subspace of a real Hilbert space, then its negative and
positive polar cones are both equal to the orthogonal complement `Cᗮ`, hence to each other and to
the textbook orthogonal set `C^⊥`. -/
theorem negativePolar_and_positivePolar_eq_orthogonal_of_submodule (C : Submodule ℝ E) :
    negativePolar (C : Set E) = (Cᗮ : Set E) ∧ positivePolar (C : Set E) = (Cᗮ : Set E) := by
  constructor
  · -- The negative polar condition is exactly the nonpositive helper above.
    ext u
    rw [mem_negativePolar]
    simpa using (forall_inner_nonpos_iff_mem_orthogonal C (u := u))
  · -- The positive polar condition is exactly the nonnegative helper above.
    ext u
    rw [mem_positivePolar]
    simpa using (forall_inner_nonneg_iff_mem_orthogonal C (u := u))

end

end Set
