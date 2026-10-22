/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: use `HilbertBasis.mk` for the converse direction and, conversely, identify the
-- range of a `HilbertBasis C ℝ E` with the given set `C`.
/-- Text 2.0.4: for a real Hilbert space, a subset is an orthonormal basis exactly when the
inclusion `C ↪ E` underlies a `HilbertBasis C ℝ E`, equivalently when the subset is orthonormal
and its algebraic span is dense. -/
theorem isOrthonormalBasis_iff [CompleteSpace E] (C : Set E) :
    (∃ b : HilbertBasis C ℝ E, ⇑b = ((↑) : C → E)) ↔
      Orthonormal ℝ ((↑) : C → E) ∧
        (Submodule.span ℝ C).topologicalClosure = ⊤ := sorry

-- Proof sketch: A countable orthonormal basis gives a countable dense subset, and conversely a
-- separable Hilbert space admits a countable orthonormal basis.
/-- `SeparableSpace` is the canonical mathlib formulation of admitting a countable orthonormal
basis, expressed via a countable subtype carrying a `HilbertBasis`. -/
theorem separableSpace_iff_exists_countable_orthonormal_basis [CompleteSpace E] :
    SeparableSpace E ↔
      ∃ C : Set E, C.Countable ∧ ∃ b : HilbertBasis C ℝ E, ⇑b = ((↑) : C → E) := sorry
