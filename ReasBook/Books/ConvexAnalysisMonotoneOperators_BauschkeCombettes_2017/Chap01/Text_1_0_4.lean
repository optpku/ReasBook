/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.4 (1): the span of `C` is the intersection of all linear subspaces of `X`
containing `C`. -/
-- Proof sketch: use the Galois insertion between `Submodule.span ℝ` and coercion from submodules
-- to sets to identify the generated submodule with the infimum of all containing submodules.
theorem span_eq_sInf_submodule (C : Set X) :
    Submodule.span ℝ C = sInf {S : Submodule ℝ X | C ⊆ S} := by
  refine le_antisymm ?_ ?_
  · exact le_sInf fun S hS ↦ Submodule.span_le.2 hS
  · exact sInf_le Submodule.subset_span

/-- Text 1.0.4 (2): the affine hull of `C` is the intersection of all affine subspaces of `X`
containing `C`. -/
-- Proof sketch: apply the existing `AffineSubspace.affineSpan_eq_sInf` characterization of
-- `affineSpan ℝ C` as the infimum of all affine subspaces containing `C`.
theorem affine_hull_eq_sInf_affineSubspace (C : Set X) :
    affineSpan ℝ C = sInf {S : AffineSubspace ℝ X | C ⊆ S} := by
  simpa using AffineSubspace.affineSpan_eq_sInf ℝ X C
