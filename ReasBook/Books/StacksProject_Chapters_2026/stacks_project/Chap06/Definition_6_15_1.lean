module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Stalks


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe w v u

/- Domain-style sampling for Definition 6.15.1:
- primary domain: concrete-category forgetful functors to `Type` whose behavior on limits,
  filtered colimits, and isomorphisms drives the sheaf and stalk API for algebraic structures;
- inspected owner declarations:
  `CategoryTheory.ConcreteCategory`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`,
  `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction:
  the source fixes a pair `(C, F)` with `F : C ⥤ Type w`, so the right public owner here is a
  bundled `Prop`-valued predicate on that pair, while the primitive data are the six canonical
  mathlib classes
  `F.Faithful`, `HasLimits C`, `PreservesLimits F`, `HasFilteredColimits C`,
  `PreservesFilteredColimits F`, and `F.ReflectsIsomorphisms`;
- bridge/view:
  `CategoryTheory.ConcreteCategory` is only a view induced by the faithful functor `F`, not the
  owner abstraction itself, because the source does not start from a pre-existing concrete-category
  structure on `C`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project predicate saying that the fixed pair `(C, F)` is a type of
  algebraic structures;
- `core/canonical`: the six existing mathlib classes listed above;
- `bridge/view`: any concrete-category structure induced from the faithful functor `F`.

Primitive data are exactly those six owner classes, so this definition should bundle them directly
and add no auxiliary wrapper data.
-/
/-- Definition 6.15.1: once the category `C` and the functor `F : C ⥤ Type w` are fixed, the
remaining axioms for a type of algebraic structure form a property of the pair `(C, F)`. -/
class IsAlgebraicStructure (C : Type u) [Category.{v} C] (F : C ⥤ Type w) : Prop
    extends F.Faithful, HasLimits C, PreservesLimits F, HasFilteredColimits C,
      PreservesFilteredColimits F, F.ReflectsIsomorphisms

section

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

instance [F.Faithful] [HasLimits C] [PreservesLimits F] [HasFilteredColimits C]
    [PreservesFilteredColimits F] [F.ReflectsIsomorphisms] : IsAlgebraicStructure C F where

instance [IsAlgebraicStructure C F] (X : TopCat.{w}) :
    (Opens.grothendieckTopology X).HasSheafCompose F := by
  exact hasSheafCompose_of_preservesLimitsOfSize (Opens.grothendieckTopology X)

end
