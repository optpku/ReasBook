module

public import stacks_project.Chap07.Proposition_7_14_7
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling for Lemma 7.5.2:
- primary domain: representably flat functors and the filtered/cofiltered structured-arrow
  categories they induce
- core/canonical owner: `RepresentablyFlat`
- relevant owner declarations:
  `representablyFlat_of_terminal_and_pullbacks`,
  `RepresentablyFlat.cofiltered`,
  `isFiltered_of_isCofiltered_op`
- target layer below: `source-facing` bridge from the explicit terminal-object and pullback
  hypotheses in the text to the filtered opposite structured-arrow category `(StructuredArrow V u)ᵒᵖ`

Primitive data are the explicit terminal object and pullback-preservation hypotheses. The
cofilteredness of `StructuredArrow V u` is derived owner API coming from `RepresentablyFlat`, and
`RepresentablyFlat` is already produced upstream in the chapter by the source-facing bridge
`representablyFlat_of_terminal_and_pullbacks`. This file should therefore remain a thin
bridge/view theorem over that owner abstraction.
-/

/-- Lemma 7.5.2 in textbook form: under the same hypotheses, the opposite structured-arrow
category `(StructuredArrow V u)ᵒᵖ`, i.e. `(𝓘^u_V)ᵒᵖ`, is filtered. -/
theorem structuredArrow_op_isFiltered_of_terminal_and_pullbacks
    (u : C ⥤ D) (V : D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsFiltered (StructuredArrow V u)ᵒᵖ := by
  let _ : RepresentablyFlat u := representablyFlat_of_terminal_and_pullbacks u X hX huX
  exact isFiltered_of_isCofiltered_op (StructuredArrow V u)ᵒᵖ

end CategoryTheory
