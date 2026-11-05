module

public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 4.2.14:
- primary domain: coslice categories and their canonical forgetful/precomposition functors.
- inspected owner declarations:
  `CategoryTheory.Under`,
  `CategoryTheory.Under.forget`,
  `CategoryTheory.Under.map`,
  `CategoryTheory.Under.mapForget_eq`.
- best owner abstraction: mathlib's coslice-category owner `Under X`; the forgetful functor and
  precomposition functoriality are derived owner API, not separate local structures or wrappers.
- primitive data: the base object `X : C` and, for the functoriality statements, a morphism
  `f : X' ⟶ X`.
- derived API: `Under.forget X`, `Under.map f`, and the coherence `Under.mapForget_eq f`.

Source/core/bridge triage:
- `source-facing`: the four textbook coslice-category constructions recalled in this file.
- `core/canonical`: `Under`, `Under.forget`, `Under.map`, `Under.mapForget_eq`.
- `bridge/view`: none needed here, since the source notions already coincide with the mathlib
  owner declarations. -/

/- Example 4.2.14 (1): for an object `X` of a category `C`, the category of objects under `X` is
the coslice category `Under X`, which in mathlib is the canonical owner for the textbook category
`X/C`. By definition this is `StructuredArrow X (𝟭 C)`, so its objects are morphisms with source
`X` and its morphisms are commutative triangles under `X`. -/
recall Under

/- Example 4.2.14 (2): the forgetful functor from the coslice category `X/C` to `C` is
`Under.forget X`. -/
recall Under.forget

/- Example 4.2.14 (3): a morphism `f : X' ⟶ X` induces the precomposition functor
`Under.map f : Under X ⥤ Under X'`. -/
recall Under.map

/- Example 4.2.14 (4): precomposition along `f : X' ⟶ X` followed by forgetting to `C` agrees
with the forgetful functor from `X/C`, namely `Under.mapForget_eq f`. -/
recall Under.mapForget_eq

end CategoryTheory
