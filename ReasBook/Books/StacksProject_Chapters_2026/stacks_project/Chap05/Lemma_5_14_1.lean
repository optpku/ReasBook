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

/- Domain-style sampling for limits in `TopCat`:
- primary domain: categorical limits of topological spaces and the forgetful functor to types;
- inspected owner declarations:
  `TopCat.topCat_hasLimitsOfSize`,
  `TopCat.topCat_hasLimits`,
  `TopCat.forget_preservesLimitsOfSize`,
  `TopCat.forget_preservesLimits`.
- best owner abstraction: `HasLimits TopCat`.

Primitive-vs-derived split:
- primitive data: the size-level instance `TopCat.topCat_hasLimitsOfSize`, from which the global
  `HasLimits TopCat` instance is obtained;
- derived API: the exposed global instance `TopCat.topCat_hasLimits` and the companion forgetful
  preservation instance `TopCat.forget_preservesLimits`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the category of topological spaces has all limits;
- `core/canonical`: the owner instance `TopCat.topCat_hasLimits : HasLimits TopCat`;
- `bridge/view`: the forgetful-functor companion `TopCat.forget_preservesLimits`, while the
  concrete cone/topology descriptions are handled downstream by Lemmas `5.14.2` and `5.14.3`.

This item is recall-only: there is no additional source-defined data to package, so the refined
file should reuse the canonical owner instances directly rather than introduce a local alias or a
wrapper theorem.
-/

/- Lemma 5.14.1: the category of topological spaces has all limits. This is exactly the canonical
mathlib instance `TopCat.topCat_hasLimits`. -/
recall TopCat.topCat_hasLimits

/- Companion recall: the forgetful functor from topological spaces to types preserves limits. This
is exactly the canonical mathlib instance `TopCat.forget_preservesLimits`. -/
recall TopCat.forget_preservesLimits
