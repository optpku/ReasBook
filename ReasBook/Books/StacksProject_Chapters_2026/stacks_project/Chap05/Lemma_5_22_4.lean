module

import Mathlib.Topology.Separation.DisjointCover
import stacks_project.Chap05.Lemma_5_22_2
import Mathlib.Tactic.Recall
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open Set TopologicalSpace

universe u v

section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TotallyDisconnectedSpace X]
  {ι : Type v} {U : ι → Opens X}

/-
Domain-style sampling for profinite open-cover refinements:
- primary domain: refinement of open covers in profinite spaces
- inspected owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `TopologicalSpace.IsOpenCover.exists_finite_clopen_cover`,
  `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`,
  `Profinite`
- best owner abstraction: `TopologicalSpace.IsOpenCover`

Layer triage:
- `source-facing`: Lemma 5.22.4, for a fixed open cover of a profinite space
- `core/canonical`: `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`
- `bridge/view`: none, since the source statement is exactly the canonical owner theorem

Primitive data is only the fixed open cover `U` together with `IsOpenCover U`; the finite disjoint
clopen refinement is derived output of the owner theorem. This file should therefore recall that
canonical theorem directly rather than keep a parallel local alias.
-/

/- Lemma 5.22.4: every open cover of a profinite space admits a refinement by a finite cover by
pairwise disjoint nonempty clopen subsets. This is exactly the canonical owner theorem
`TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`. -/
recall TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover

end
