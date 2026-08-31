module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Domain-style sampling and source/core/bridge triage for Definition 7.32.2:
- primary domain: points of Grothendieck sites and their associated stalk/fiber functors;
- sampled owner API:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.toToposPoint`;
- source-facing notion: a point of the site `(C, J)`;
- core/canonical owner: `GrothendieckTopology.Point`, instantiated at the topology `J` as `J.Point`;
- bridge/view: the textbook clauses are the owner fields, while the associated presheaf and sheaf
  fiber functors and the induced topos point are downstream derived API.

Primitive data are the fields `fiber`, `isCofiltered`, `initiallySmall`, and
`jointly_surjective`. The functors `presheafFiber` and `sheafFiber`, together with their
exactness/comparison lemmas, are derived from that owner abstraction and should not be repackaged
locally.
-/
/- Definition 7.32.2: a point of the site `(C, J)` is the canonical mathlib owner `J.Point`.
This owner already packages exactly the textbook fiber functor, cofiltered-neighborhood, and
covering-surjectivity data. -/
#check J.Point

end CategoryTheory
