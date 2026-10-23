module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.47.8:
- primary domain: Grothendieck topologies on a fixed category, ordered by inclusion of covering
  sieves;
- sampled canonical declarations:
  `GrothendieckTopology.instPartialOrder`,
  `GrothendieckTopology.le_def`,
  `GrothendieckTopology.discrete_eq_top`,
  `GrothendieckTopology.trivial_eq_bot`;
- layer triage for this item:
  `source-facing`: the finer/coarser order on Grothendieck topologies together with the finest and
  coarsest topologies;
  `core/canonical`: `GrothendieckTopology C` with its upstream order/lattice structure;
  `bridge/view`: the pointwise characterization `GrothendieckTopology.le_def`.

Primitive data are only the category `C`. The order relation and the extreme topologies are
derived owner API on `GrothendieckTopology C`, so this file should recall that owner directly and
keep only the pointwise order description as companion API.
-/

/- Definition 7.47.8: the Grothendieck topologies on `C` carry the canonical partial order in
which `J' ≤ J` means that `J` is finer/stronger than `J'`, equivalently that `J'` is
coarser/weaker than `J`. -/
recall GrothendieckTopology.instPartialOrder

/- Companion recall: the order relation is pointwise inclusion of covering sieves, so `J' ≤ J`
exactly when `J' U ⊆ J U` for every object `U` of `C`. -/
recall GrothendieckTopology.le_def

/- Definition 7.47.8: the finest Grothendieck topology on `C` is the discrete topology, which is
the top element of the partial order. -/
recall GrothendieckTopology.discrete_eq_top

/- Definition 7.47.8: the coarsest Grothendieck topology on `C` is the chaotic or indiscrete
topology, which is the bottom element of the partial order. -/
recall GrothendieckTopology.trivial_eq_bot

end
