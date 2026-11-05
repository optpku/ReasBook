module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.«7_32_1_1»

@[expose] public section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 7.33.1:
- primary domain: stalk/fiber functors on sites, built from cofiltered categories of elements;
- sampled owner API:
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.sheafFiber`,
  `comp_preservesFiniteLimits`;
- source-facing layer: the restriction of the raw presheaf fiber functor `u.presheafFiber`
  to sheaves;
- core/canonical owner: the canonical `PreservesFiniteLimits` instance on `u.presheafFiber`,
  together with the composite instance for `sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber`;
- bridge/view: none; this item is a direct recall of the owner-level finite-limit-preservation
  instance after restricting from presheaves to sheaves.

Primitive data here are only the topology `J`, the functor `u : C ⥤ Type (max u v)`, and the
cofilteredness hypothesis `[IsCofiltered u.Elements]`, together with the size control on
`u.Elements` needed to form the defining colimit of `u.presheafFiber`. The
covering-surjectivity data needed for `GrothendieckTopology.Point` are absent, so this item
should stay at the more general source-facing `Functor.presheafFiber` layer rather than be
collapsed to `Point.sheafFiber`. Finite-limit preservation is derived API of that owner, so the
main entry should be a direct owner recall rather than a parallel wrapper theorem.
-/
variable (J : GrothendieckTopology C) (u : C ⥤ Type (max u v))
variable [InitiallySmall.{max u v} u.Elements] [IsCofiltered u.Elements]

-- Proof sketch: `u.presheafFiber` is the canonical filtered-colimit fiber functor from
-- `(7.32.1.1)`, hence it preserves finite limits under the cofilteredness hypothesis on
-- `u.Elements`; composing with the sheaf inclusion `sheafToPresheaf` preserves that left
-- exactness statement on sheaves.
/-- Lemma 7.33.1 (Stacks, Section 7.33, tag `05UZ`): if the category of neighbourhoods of the
set-valued functor `u : C ⥤ Type (max u v)` is cofiltered, then the stalk functor of `(7.32.1.1)`
on set-valued sheaves is left exact, equivalently it preserves finite limits. Here the stalk
functor is `sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber`. -/
theorem sheafToPresheaf_comp_presheafFiber_preservesFiniteLimits :
    PreservesFiniteLimits (sheafToPresheaf J (Type (max u v)) ⋙ u.presheafFiber) := by
  -- The source proof factors the stalk functor through presheaves, so we use the canonical
  -- finite-limit-preservation instances for `sheafToPresheaf` and for `u.presheafFiber`.
  infer_instance

end CategoryTheory
