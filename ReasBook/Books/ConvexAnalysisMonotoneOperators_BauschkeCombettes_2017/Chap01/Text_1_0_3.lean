/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace Set

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.3: a subset of a real vector space is the nonempty carrier of a real affine
subspace exactly when it is nonempty and equal to its affine span. -/
theorem exists_nonempty_affineSubspace_iff_nonempty_eq_affineSpan (C : Set X) :
    (∃ S : AffineSubspace ℝ X, (S : Set X) = C ∧ (S : Set X).Nonempty) ↔
      C.Nonempty ∧ (affineSpan ℝ C : Set X) = C := by
  constructor
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS, by simp⟩
  · rintro ⟨hC, hCspan⟩
    exact ⟨affineSpan ℝ C, hCspan, hC.affineSpan ℝ⟩

/-- A subset of a real vector space is the nonempty carrier of an affine subspace exactly when it
is nonempty and closed under binary affine combinations. -/
theorem exists_nonempty_affineSubspace_iff_nonempty_lineMap_mem (C : Set X) :
    (∃ S : AffineSubspace ℝ X, (S : Set X) = C ∧ (S : Set X).Nonempty) ↔
      C.Nonempty ∧
        ∀ ⦃x y : X⦄, x ∈ C → y ∈ C → ∀ t : ℝ, AffineMap.lineMap x y t ∈ C := by
  sorry

/-- A subset of a real vector space is the nonempty carrier of an affine subspace exactly when it
is nonempty and stable under binary affine combinations. -/
-- Proof sketch: identify nonempty affine subsets with nonempty carriers of `AffineSubspace ℝ X`
-- and rewrite binary affine combinations with `AffineMap.lineMap_apply_module`.
theorem exists_nonempty_affineSubspace_iff_ne_empty_eq_smul_add (C : Set X) :
    (∃ S : AffineSubspace ℝ X, (S : Set X) = C ∧ (S : Set X).Nonempty) ↔
      C ≠ ∅ ∧ ∀ t : ℝ, C = t • C + (1 - t) • C := by
  sorry

end Set
