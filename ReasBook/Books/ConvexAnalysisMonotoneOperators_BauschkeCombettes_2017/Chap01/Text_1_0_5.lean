/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set
open AffineSubspace

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.5: if `C` is a nonempty affine subspace of a real vector space, then the textbook
difference set `C - C` is the carrier of the canonical direction subspace `C.direction`, and `C`
is the translate of this direction through any point of `C`. -/
-- Proof sketch: use `coe_direction_eq_vsub_set` to identify the textbook difference set with
-- `C.direction`, then characterize the translate through `x ∈ C` pointwise using
-- `vsub_mem_direction` and `vadd_mem_of_mem_direction`.
theorem text_1_0_5 (C : AffineSubspace ℝ X) (hC : (C : Set X).Nonempty) :
    (C.direction : Set X) = (C : Set X) -ᵥ (C : Set X) ∧
    ∀ ⦃x : X⦄, x ∈ C → (C : Set X) = (fun v ↦ v +ᵥ x) '' (C.direction : Set X) := by
  refine ⟨?_, ?_⟩
  · -- The textbook difference set `C - C` is exactly the canonical direction set of `C`.
    simpa using coe_direction_eq_vsub_set hC
  · -- Any point of `C` together with the direction determines `C` again.
    intro x hx
    ext y
    constructor
    · intro hy
      refine ⟨y -ᵥ x, vsub_mem_direction hy hx, ?_⟩
      simp
    · rintro ⟨v, hv, rfl⟩
      exact vadd_mem_of_mem_direction hv hx
