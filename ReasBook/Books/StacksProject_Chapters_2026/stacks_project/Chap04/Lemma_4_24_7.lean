module

public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.7:
- primary domain: adjunctions in category theory;
- sampled owner API:
  `Adjunction`,
  `Adjunction.left_triangle`,
  `Adjunction.right_triangle`,
  `Adjunction.left_triangle_components`;
- best owner abstraction: the owner object `CategoryTheory.Adjunction`, whose canonical public
  triangle-identity API is given by the natural-transformation theorems
  `Adjunction.left_triangle` and `Adjunction.right_triangle`. The componentwise formulas are
  lower-level owner data used to derive these theorems.

Primitive-vs-derived split:
- primitive data: for `adj : u ⊣ v`, the unit, counit, and the objectwise triangle identities
  `Adjunction.left_triangle_components` / `Adjunction.right_triangle_components` are fields of the
  owner structure itself;
- derived API: the natural-transformation identities `Adjunction.left_triangle` and
  `Adjunction.right_triangle`, along with `Adjunction.homEquiv` and its consequences. This lemma
  is a pure recall item and should reuse the canonical owner theorems directly, without a parallel
  local wrapper or a replacement by unpacked component formulas.
-/

/- Source/core/bridge triage for Lemma 4.24.7:
- source-facing: the two triangle identities for a chosen adjunction `u ⊣ v`;
- core/canonical: the natural-transformation theorems `Adjunction.left_triangle` and
  `Adjunction.right_triangle`;
- bridge/view: none needed here, since the source statement is already exactly the owner API.
-/

/- Lemma 4.24.7: the two triangle identities of a chosen adjunction are exactly the canonical
owner theorems `Adjunction.left_triangle` and `Adjunction.right_triangle`. -/
recall Adjunction.left_triangle
recall Adjunction.right_triangle

end CategoryTheory
