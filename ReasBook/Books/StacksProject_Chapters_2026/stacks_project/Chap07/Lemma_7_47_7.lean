module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}

/- Domain-style sampling for Lemma 7.47.7:
- primary domain: closure properties of covering sieves in a Grothendieck topology;
- sampled owner API:
  `GrothendieckTopology.superset_covering`,
  `GrothendieckTopology.intersection_covering`,
  `GrothendieckTopology.intersection_covering_iff`,
  `GrothendieckTopology.transitive`;
- best owner abstraction: the covering predicate `S ∈ J U` for sieves on a fixed object;
- primitive data: the Grothendieck-topology axioms bundled in `J`;
- derived API: the order-theoretic closure theorems for covering sieves, including enlargement and
  finite intersection.

Source/core/bridge triage:
- `source-facing`: covering sieves are stable under intersection and passage to larger sieves;
- `core/canonical`: `J.intersection_covering` and `J.superset_covering`;
- `bridge/view`: the lattice/order structure on `Sieve U`, expressed by `⊓` and `≤`.

This item is therefore recall-only: both clauses are already exact owner theorems upstream, so the
file should point to those owners directly rather than restate them through a local wrapper.
-/

/- Lemma 7.47.7 (1): the intersection of two covering sieves on a fixed object is again covering.
This is the canonical mathlib owner theorem `GrothendieckTopology.intersection_covering`, tagged
for the corresponding Stacks clause. -/
recall intersection_covering

/- Lemma 7.47.7 (2): if a sieve `S` on `U` is covering for `J` and `S ≤ S'`, then the larger
sieve `S'` is also covering. This is the canonical mathlib owner theorem
`GrothendieckTopology.superset_covering`. -/
recall superset_covering

end CategoryTheory.GrothendieckTopology
