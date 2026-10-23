module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Opposites
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

/-
Source/core/bridge triage for Definition 4.3.3:
- source-facing owner: a set-valued presheaf on a category `C`
- sampled canonical declarations in this domain:
  the ambient functor category `Cᵒᵖ ⥤ Type w`,
  the topological specialization `TopCat.Presheaf`,
  and the site-level sheaf owner `Sheaf J (Type w)`, whose underlying primitive object is again a
  set-valued presheaf
- core/canonical background: the contravariant functor category `Cᵒᵖ ⥤ Type w`
- primitive data: only the underlying functor
- derived API: natural transformations, the inherited category structure, and later predicates on
  this owner such as representability and the sheaf condition
- owner choice: mathlib does not provide a generic owner alias for arbitrary set-valued
  presheaves, so this file remains the canonical project owner while staying definitionally equal
  to the ambient functor category
-/
/-- Definition 4.3.3: a presheaf of sets on a category `C` is the chapter owner `Presheaf C`,
definitionally equal to the contravariant functor category `Cᵒᵖ ⥤ Type w`. The short owner name
`Presheaf` is kept because it is stable, high-reuse vocabulary throughout the later
chapter/project development. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type w

variable {C : Type u} [Category.{v} C]

/-- For a presheaf on `C`, the restriction map along an identity morphism is the identity on the
section type over that object. -/
-- Proof sketch: this is the `map_id` axiom of the underlying contravariant functor.
theorem Presheaf_map_id (F : Presheaf C) (U : Cᵒᵖ) :
    F.map (𝟙 U) = 𝟙 (F.obj U) := by
  -- A presheaf is definitionally a functor `Cᵒᵖ ⥤ Type w`, so the claim is its identity law.
  exact F.map_id U

end CategoryTheory
