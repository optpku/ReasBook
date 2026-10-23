module

import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Tactic.Recall
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open CategoryTheory Limits

universe u

/- Domain-style sampling for limits in `Profinite`:
- primary domain: categorical limits in the bundled category of profinite spaces;
- inspected owner declarations:
  `Profinite.limitCone`,
  `Profinite.limitConeIsLimit`,
  `Profinite.hasLimits`,
  `Profinite.toTopCat.createsLimits`.
- best owner abstraction: the global instance `Profinite.hasLimits : HasLimits Profinite`.

Primitive-vs-derived split:
- primitive data: for each diagram `F`, the chosen cone `Profinite.limitCone F` and the proof
  `Profinite.limitConeIsLimit F`;
- derived API: the diagramwise instance `HasLimit F`, obtained from the owner instance
  `Profinite.hasLimits`.

Source/core/bridge triage:
- `source-facing`: a limit of profinite spaces is profinite;
- `core/canonical`: the owner instance `Profinite.hasLimits`;
- `bridge/view`: the diagram-specific specialization `HasLimit F`.

This item is recall-only: the file should reuse the canonical owner instance rather than keep a
parallel theorem with the exact same interface as the derived specialization.
-/

/- Lemma 5.22.3: the category of profinite spaces has limits. This is exactly the canonical owner
instance `Profinite.hasLimits`. -/
recall Profinite.hasLimits

section

variable {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u})

/- Companion specialization: for any profinite-valued diagram `F`, the source statement "a limit
of profinite spaces is profinite" is the canonical derived instance `HasLimit F`. -/
#check (inferInstance : HasLimit F)

end
