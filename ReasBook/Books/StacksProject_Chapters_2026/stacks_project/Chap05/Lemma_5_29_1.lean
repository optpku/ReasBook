module

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for colimits in `TopCat`:
- primary domain: categorical colimits of topological spaces and the forgetful functor to types;
- inspected owner declarations:
  `TopCat.topCat_hasColimitsOfShape`,
  `TopCat.topCat_hasColimitsOfSize`,
  `TopCat.topCat_hasColimits`,
  `TopCat.forget_preservesColimits`.
- best owner abstraction: `HasColimits TopCat`.

Primitive-vs-derived split:
- primitive data: the size-level instance `TopCat.topCat_hasColimitsOfSize`, built from the
  shape-level colimit construction `TopCat.topCat_hasColimitsOfShape`;
- derived API: the exposed global instance `TopCat.topCat_hasColimits` and the companion forgetful
  preservation instance `TopCat.forget_preservesColimits`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the category of topological spaces has all colimits;
- `core/canonical`: the owner instance `TopCat.topCat_hasColimits : HasColimits TopCat`;
- `bridge/view`: the forgetful-functor companion `TopCat.forget_preservesColimits`.

This item is recall-only: the source introduces no extra mathematical data beyond the canonical
`TopCat` colimit instance, so the refined file should reuse the owner declarations directly rather
than duplicate them behind a local wrapper.
-/

/- Lemma 5.29.1: the category of topological spaces has all colimits. The core owner declaration
is the canonical mathlib instance `TopCat.topCat_hasColimits`. -/
recall TopCat.topCat_hasColimits

/- Companion derived API: the forgetful functor from topological spaces to types preserves
colimits. This is exactly the canonical mathlib instance
`TopCat.forget_preservesColimits`. -/
recall TopCat.forget_preservesColimits
