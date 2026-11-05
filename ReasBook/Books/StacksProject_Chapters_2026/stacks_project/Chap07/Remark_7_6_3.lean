module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Remark_7_48_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 7.6.3:
- primary domain: replacing a proper class of coverings by set-sized site presentations without
  changing the resulting sheaf category;
- sampled owner API:
  `Coverage.toGrothendieck`,
  `topology_eq_iff_same_sheaves`,
  `Coverage.tautologicalEnlargement_toGrothendieck`,
  `isSheaf_iff_of_common_ambient_pretopology`;
- source/core/bridge triage:
  `source-facing`: the remark that several natural set-sized replacements for a proper class of
    coverings lead to the same sheaf category, even though the chapter chooses one presentation
    for later development;
  `core/canonical`: `GrothendieckTopology C` and the sheaf predicate on it;
  `bridge/view`: equal-topology comparisons between different set-sized presentations, especially
    `Coverage.tautologicalEnlargement_toGrothendieck`, whose source-facing owner is now
    `Precoverage.tautologicalEnlargement`, and which matches the later chapter route of replacing
    a coverage by the canonical set of tautologically equivalent coverings while keeping the
    associated topology unchanged.

Primitive data in Lean are the chosen set-sized presentations such as `Coverage C`. The associated
Grothendieck topology and the induced sheaf predicate are derived API, so the main public entry
here should be the canonical same-sheaf owner theorem rather than a presentation-specific wrapper.
For the remark's stated alternative route, the faithful bridge is the later tautological
enlargement theorem; the choice-based comparison route is already available separately via
Lemma 7.8.8.
-/

/- Remark 7.6.3, core/canonical recall: two Grothendieck topologies define the same sheaf theory
exactly when they are equal. This is the owner-level invariance statement behind the remark that
different set-sized replacements for a proper-class covering relation give the same sheaf
category. -/
recall topology_eq_iff_same_sheaves

/- Companion bridge recall: replacing a coverage by the later canonical set of tautologically
equivalent coverings does not change the associated Grothendieck topology. This matches the
remark's cited route through the associated topology and the later covering-family modification. -/
recall Coverage.tautologicalEnlargement_toGrothendieck (K : Coverage C) :
    K.toPrecoverage.tautologicalEnlargement.toGrothendieck = K.toGrothendieck

end CategoryTheory
