module

import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable (x y : B)

/- Domain-style sampling for Definition 4.29.4:
- `Bicategory.Equivalence` is the canonical owner object for equivalences in a
  bicategory, with notation `x ≌ y`.
- `Bicategory.Equivalence.mkOfAdjointifyCounit` is the canonical constructor from a pair of
  quasi-inverse `1`-morphisms and unit/counit `2`-isomorphisms.
- `Bicategory.Equivalence.id` is the canonical identity example of that owner object.
- `Bicategory.Adjunction` is the surrounding owner-level API from which bicategorical
  equivalences inherit their triangle data.
- The fields `hom`, `inv`, `unit`, and `counit` are the primitive bicategorical data; any
  existential “there exist morphisms with invertible `2`-morphisms” formulation is derived API.

Primitive-vs-derived split:
- primitive data: none in this file; the notion is already owned upstream by
  `Bicategory.Equivalence`.
- derived API: the canonical constructor `Equivalence.mkOfAdjointifyCounit`, which assembles the
  textbook quasi-inverse data into the owner object. -/

/- Source/core/bridge triage for Definition 4.29.4:
- `source-facing`: the textbook quasi-inverse formulation of equivalence in a `2`-category.
- `core/canonical`: the owner object `x ≌ y`.
- `bridge/view`: the canonical constructor `Equivalence.mkOfAdjointifyCounit`. -/

/- Definition 4.29.4: for objects `x` and `y` of a `2`-category, the assertion that `x` and `y`
are equivalent is the canonical bicategorical notion `Bicategory.Equivalence x y`, written
`x ≌ y`. This packages `1`-morphisms `x ⟶ y` and `y ⟶ x` together with the required
invertible `2`-morphisms exhibiting the two composites as identities. -/
#check (x ≌ y)

/- Companion bridge: the textbook quasi-inverse data are assembled directly into the canonical
owner object by `Equivalence.mkOfAdjointifyCounit`; no parallel local existence wrapper is
needed. -/
recall Equivalence.mkOfAdjointifyCounit

end CategoryTheory
