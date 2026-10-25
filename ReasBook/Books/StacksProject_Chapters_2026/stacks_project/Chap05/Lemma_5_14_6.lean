module

import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for cofiltered limits of compact Hausdorff spaces in `TopCat`:
- primary domain: categorical limits in `TopCat` and nonemptiness of cofiltered limits of compact
  Hausdorff spaces;
- inspected owner declarations:
  `TopCat.topCat_hasLimits`,
  `TopCat.limitCone`,
  `TopCat.limitConeIsLimit`,
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- best owner abstraction: the chosen limit cone `TopCat.limitCone F`, with nonemptiness expressed
  by the canonical theorem `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`.

Primitive-vs-derived split:
- primitive data: the diagram `F : J ⥤ TopCat`, the chosen limit cone `TopCat.limitCone F`, and
  the typeclass assumptions `[IsCofilteredOrEmpty J]`, `[∀ j, Nonempty (F.obj j)]`,
  `[∀ j, CompactSpace (F.obj j)]`, `[∀ j, T2Space (F.obj j)]`;
- derived API: the theorem that the cone point `(TopCat.limitCone F).pt` is nonempty.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a cofiltered limit of nonempty quasi-compact
  Hausdorff spaces is nonempty;
- `core/canonical`: the theorem
  `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`;
- `bridge/view`: downstream specializations such as
  `CategoryTheory.nonempty_sections_of_finite_cofiltered_system.init`.

This item is recall-only: the source introduces no new object beyond the canonical `TopCat`
limit cone, so refining the file means reusing the owner theorem directly rather than packaging a
parallel local statement.
-/

/- Lemma 5.14.6: a cofiltered limit of nonempty quasi-compact Hausdorff spaces is nonempty.
This is exactly the canonical mathlib theorem
`TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`, where quasi-compact Hausdorff is
expressed by the typeclasses `CompactSpace` and `T2Space`. -/
recall TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system
