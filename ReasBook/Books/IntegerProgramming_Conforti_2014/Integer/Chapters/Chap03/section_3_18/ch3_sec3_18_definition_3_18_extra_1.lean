import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1

open Set
open scoped Matrix

/- Section 3.18 reuses the same facet predicate across multiple exercise files. This support file
keeps reusable dimension and facet owners separate from any one concrete polytope construction. -/

/-- The dimension of a polyhedral set, measured by the direction of its affine span. -/
noncomputable def polyhedronDim {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (P : Set E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ P).direction

/-- The dimension of the recession cone of `P`, measured by the dimension of its linear span. -/
noncomputable def recessionConeDim {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (P : Set E) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (_root_.recessionCone ℝ P))

/-- A facet of a finite-dimensional real polytope is a nonempty exposed face of codimension one. -/
def IsFacetOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P F : Set E) : Prop :=
  F.Nonempty ∧
    IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ P).direction

/-- Unfolding lemma for `IsFacetOf`. -/
theorem isFacetOf_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {P F : Set E} :
    IsFacetOf P F ↔
      F.Nonempty ∧
        IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
            Module.finrank ℝ (affineSpan ℝ P).direction := by
  rfl
