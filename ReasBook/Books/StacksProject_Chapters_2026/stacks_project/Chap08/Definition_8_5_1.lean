module

public import Mathlib
public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap08.Definition_8_4_1


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Definition 8.5.1:
- primary domain: stacks over sites and categories fibred in groupoids.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Pseudofunctor.IsStack`,
  `IsStackOnSite`.
- best owner abstraction: the source-facing notion should remain the reusable property
  `IsStackInGroupoids J p`, but its parent owner should be the Chapter 8 stack condition
  `IsStackOnSite J p`; the extra source-facing primitive datum is then the Chapter 4 owner
  `IsFibredInGroupoids p`.
- primitive data: `IsStackOnSite J p` together with `IsFibredInGroupoids p`.
- derived API: the inherited `IsStackOnSite J p` owner, its `p.IsFibered` instance, and the
  Chapter 4 groupoid-fibration owner recovered from the extra field.

Source/core/bridge triage:
- `source-facing`: `IsStackInGroupoids J p`.
- `core/canonical`: `IsFibredInGroupoids p`, `IsStackOnSite J p`,
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`.
- `bridge/view`: no extra public bridge is needed, since `IsStackOnSite J p` is the parent
  owner of `IsStackInGroupoids J p`. -/

/-- Definition 8.5.1: a category over the site `(C, J)` is a stack in groupoids when its
projection functor is fibred in groupoids and, for every `U : C` and objects `x y` in the fiber
over `U`, the presheaf of isomorphisms `Isom(x, y)` on `C / U` is a sheaf and every descent datum
for a covering of `U` is effective. Equivalently, it is a category fibred in groupoids that is a
stack over `(C, J)` in the canonical site-theoretic sense of Definition `8.4.1`. -/
class IsStackInGroupoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsStackOnSite J p where
  toIsFibredInGroupoids : IsFibredInGroupoids p

attribute [instance] IsStackInGroupoids.toIsFibredInGroupoids

/-- A fibred-in-groupoids functor that is already a stack over `(C, J)` is a stack in groupoids. -/
instance (J : GrothendieckTopology C) [IsFibredInGroupoids p] [IsStackOnSite J p] :
    IsStackInGroupoids J p where
  toIsStackOnSite := inferInstance
  toIsFibredInGroupoids := inferInstance

end

end CategoryTheory
