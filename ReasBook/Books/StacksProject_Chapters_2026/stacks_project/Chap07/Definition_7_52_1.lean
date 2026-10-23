module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Definition 7.52.1:
- primary domain: points of a Grothendieck topology and the associated stalk functor on sheaves;
- sampled owner declarations:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.sheafFiber`,
  the exactness instances on `p.sheafFiber`,
  `ExactFunctor.of`;
- source/core/bridge triage:
  `source-facing`: a point of `J` and the exactness of the associated stalk functor on
    sheaves of sets;
  `core/canonical`: `GrothendieckTopology.Point`;
  `bridge/view`: the bundled exact functor `ExactFunctor.of p.sheafFiber`.

The primitive data are only the topology `J` and a point `p : J.Point`. The stalk functor
`p.sheafFiber` and its exactness are derived API of that owner abstraction, so this file should
reuse the owner directly and package the textbook exactness clause at the canonical exact owner
level `ExactFunctor.of`, without introducing any parallel local definition.
-/

/- Definition 7.52.1 (1): a point of the topology `J` is the canonical mathlib notion
`GrothendieckTopology.Point J`, i.e. a set-valued fiber functor on `C` whose
category of neighborhoods is cofiltered and initially small, and whose fibers are jointly
surjective along every covering sieve. -/
#check J.Point

variable [LocallySmall C]
variable (p : J.Point)

/- Definition 7.52.1 (2): for a point `p` of `J`, the textbook exactness clause for the stalk
functor on sheaves of sets is recalled in mathlib by the canonical bundled exact functor
`ExactFunctor.of p.sheafFiber`, specialized to set-valued sheaves. -/
#check
  (ExactFunctor.of p.sheafFiber :
    Sheaf J (Type (max u v)) ⥤ₑ Type (max u v))

end CategoryTheory
