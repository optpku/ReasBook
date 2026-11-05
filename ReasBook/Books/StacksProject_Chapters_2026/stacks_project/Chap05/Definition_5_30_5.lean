module

import stacks_project.Chap05.Lemma_5_30_4
import Mathlib.Tactic.Recall
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 5.30.5:
- primary domain: profinite topological groups;
- inspected owner declarations:
  `Profinite`,
  `ProfiniteGrp`,
  `ProfiniteGrp.of`,
  `ProfiniteGrp.ofContinuousMulEquiv`.

Best owner abstraction:
- `ProfiniteGrp`; the source-facing profinite-space clause for a topological group is the
  corresponding forgetful view of this bundled owner.

Primitive data vs derived API:
- primitive owner data: a bundled profinite group;
- derived API: the source-facing existence of a homeomorphism to a profinite space, and the
  equivalent existence of a topological-group isomorphism to a bundled profinite group.

Layer triage:
- `source-facing`: the textbook profinite condition for an arbitrary topological group, expressed
  through existence of a topological-group isomorphism to a bundled profinite group;
- `core/canonical`: `ProfiniteGrp`;
- `bridge/view`: `exists_profinite_iff_exists_profiniteGrp`.
-/

/- Lemma 5.30.4: for a topological group, the canonical profinite-space condition is equivalent to
admitting a presentation as a limit of finite discrete groups, and to admitting such a
presentation over a cofiltered index category. -/
recall topologicalGroup_profinite_tfae

/- Companion recall: the bundled owner for profinite spaces. -/
recall Profinite

/- Definition 5.30.5: the canonical owner abstraction for profinite topological groups is the
bundled type `ProfiniteGrp`. The source-text criterion for an arbitrary topological group is the
derived bridge theorem recalled below. -/
recall ProfiniteGrp

/-
Companion source-facing bridge for Definition 5.30.5: a topological group is profinite exactly
when it is topologically isomorphic to a bundled profinite group.
-/
recall exists_profinite_iff_exists_profiniteGrp

/-
Companion form of Definition 5.30.5: a topological group is topologically isomorphic to an object
of `ProfiniteGrp` exactly when it is compact and totally disconnected.
-/
recall exists_profiniteGrp_iff_compact_totallyDisconnected
