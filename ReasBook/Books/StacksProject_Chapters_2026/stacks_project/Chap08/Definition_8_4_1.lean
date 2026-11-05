module

public import Mathlib
public import stacks_project.Chap04.CanonicalFiberPseudofunctor


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 8.4.1:
- primary domain: stack conditions on a site for a category over the base, expressed through the
  canonical fiber pseudofunctor;
- inspected owner-level declarations:
  `Pseudofunctor.IsStack`,
  `canonicalFiberPseudofunctor`,
  `Pseudofunctor.sheafHom`,
  `Pseudofunctor.isEquivalence_toDescentData`;
- best owner abstraction: the source-facing owner `IsStackOnSite J p` should extend the canonical
  owner `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`, with `p.IsFibered` as the
  only additional primitive data needed to talk about the canonical fibers;
- primitive data: a fibred projection `p : S ⥤ C` and the stack condition on its canonical fiber
  pseudofunctor;
- derived API: the canonical Hom-sheaf object
  `(canonicalFiberPseudofunctor p).sheafHom J x y`; effective descent for covering families is
  reused directly from the parent owner
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`; the introduction theorem from these
  two parent owners to `IsStackOnSite J p` is derived and should not be rebuilt manually
  downstream.

Source/core/bridge triage:
- `source-facing`: `IsStackOnSite J p`;
- `core/canonical`: `p.IsFibered` and
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`;
- `bridge/view`: direct reuse of the canonical fiberwise Hom sheaf
  `(canonicalFiberPseudofunctor p).sheafHom J x y`. -/

/-- Definition 8.4.1: a stack over the site `(C, J)` is a category over `C` whose projection is
fibred and whose canonical pseudofunctor of fibers is a stack for `J`; this packages both the
sheaf condition on the presheaves `Mor(x, y)` and the effectiveness of descent data. -/
class IsStackOnSite (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends p.IsFibered, Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J

/-- A fibred category whose canonical fiber pseudofunctor is already a stack for `J` is
canonically a stack over the site `(C, J)`. -/
instance isStackOnSite_of_isStack (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered]
    [Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J] : IsStackOnSite J p where
  toIsFibered := inferInstance
  toIsStack := inferInstance

end CategoryTheory
