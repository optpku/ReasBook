/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-- Text 1.0.2 (1): A subset of a real vector space is a cone when it equals its set of positive
real multiples. -/
def IsCone (C : Set X) : Prop :=
  C = (Ioi (0 : ℝ) : Set ℝ) • C

/-- A cone is exactly a set equal to its positive scalar multiples. -/
theorem isCone_iff {C : Set X} :
    IsCone C ↔ C = (Ioi (0 : ℝ) : Set ℝ) • C :=
  Iff.rfl

/-- Text 1.0.2 (2): A subset of a real vector space is a ray when it is the set of nonnegative
real multiples of some nonzero vector. -/
def IsRay (C : Set X) : Prop :=
  ∃ u : X, u ≠ 0 ∧ C = (Ici (0 : ℝ) : Set ℝ) • ({u} : Set X)

/-- A ray is exactly a set of the form `ℝ_+ • {u}` for some nonzero vector `u`. -/
theorem isRay_iff {C : Set X} :
    IsRay C ↔ ∃ u : X, u ≠ 0 ∧ C = (Ici (0 : ℝ) : Set ℝ) • ({u} : Set X) :=
  Iff.rfl

/-- Text 1.0.2 (3): A subset of a real vector space is a line when it is the set of all real
scalar multiples of some nonzero vector. -/
def IsLine (C : Set X) : Prop :=
  ∃ u : X, u ≠ 0 ∧ C = (↑(ℝ ∙ u) : Set X)

/-- A line is exactly the underlying set of a one-dimensional submodule `ℝ ∙ u`
for some nonzero vector `u`. -/
theorem isLine_iff {C : Set X} :
    IsLine C ↔ ∃ u : X, u ≠ 0 ∧ C = (↑(ℝ ∙ u) : Set X) :=
  Iff.rfl

/-- Textbook formulation of `IsLine`: a line is exactly a set of the form `ℝ • {u}` for some
nonzero vector `u`. -/
theorem isLine_iff_eq_univ_smul_singleton {C : Set X} :
    IsLine C ↔ ∃ u : X, u ≠ 0 ∧ C = (univ : Set ℝ) • ({u} : Set X) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    ext x
    simp [Submodule.mem_span_singleton]
  · rintro ⟨u, hu, hC⟩
    refine ⟨u, hu, hC.trans ?_⟩
    ext x
    simp [Submodule.mem_span_singleton]

end
