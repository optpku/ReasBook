module

public import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.48.2:
- primary domain: sites presented by a `Coverage` and the associated Grothendieck topology;
- sampled owner API:
  `Coverage.toGrothendieck`,
  `Coverage.toGrothendieck_eq_sInf`,
  `Coverage.toGrothendieck_toPrecoverage`,
  `Precoverage.toGrothendieck`;
- source/core/bridge triage:
  `source-facing`: the textbook passage from a site given by covering presieves to its associated
  topology;
  `core/canonical`: `Coverage.toGrothendieck`;
  `bridge/view`: `Coverage.toGrothendieck_toPrecoverage` and `Coverage.toGrothendieck_eq_sInf`,
  relating the coverage presentation to precoverages and the Grothendieck-topology lattice.

Primitive data are only the coverage `K`. The associated Grothendieck topology is derived canonical
API from that owner abstraction, so this file should stay at direct recall/use rather than
introducing a parallel local alias or wrapper.
-/

/- Definition 7.48.2: for a site presented by its covering presieves, the associated topology is
the canonical Grothendieck topology `Coverage.toGrothendieck`, i.e. the topology
constructed in Lemma 7.48.1 from those coverings. -/
recall Coverage.toGrothendieck

end CategoryTheory
