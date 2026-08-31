module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

section

variable {X : TopCat.{u}} (ℱ : X.Presheaf AddCommGrpCat)
variable {x : X} {U : Opens X} (hx : x ∈ U)

/- Domain-style sampling for Lemma 6.12.1:
- primary domain: stalks and germs of `AddCommGrpCat`-valued presheaves on `TopCat`;
- inspected owner declarations:
  `TopCat.Presheaf.stalk`,
  `TopCat.Presheaf.germ`,
  `TopCat.Presheaf.germ_res`,
  `TopCat.Presheaf.stalkFunctor`;
- best owner abstraction: the mathlib owner is `TopCat.Presheaf.stalk`, with
  `TopCat.Presheaf.germ` as the canonical cocone morphism into that colimit;

Primitive-vs-derived split:
- primitive data: a presheaf `ℱ`, a point `x`, an open `U`, and `hx : x ∈ U`;
- derived API: the germ morphism and, in `AddCommGrpCat`, the additive map carried by its
  underlying group homomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks-project assertions that germ maps of abelian-group-valued presheaves
  are additive and that stalks are colimits over neighborhoods;
- `core/canonical`: `TopCat.Presheaf.stalk` and `TopCat.Presheaf.germ`;
- `bridge/view`: the `AddCommGrpCat` specialization exposing the additive structure through
  `(ℱ.germ U x hx).hom.map_add`.

This file should therefore stay in direct recall/use form and avoid any parallel local wrapper for
stalks or germs. -/

/- Lemma 6.12.1 (1): for an `AddCommGrpCat`-valued presheaf, the germ map is already the canonical
owner morphism `ℱ.germ U x hx : ℱ.obj (op U) ⟶ ℱ.stalk x`. Its additivity is therefore just the
standard `map_add` property of morphisms in `AddCommGrpCat`. -/
recall TopCat.Presheaf.germ
#check (ℱ.germ U x hx).hom.map_add

/- Lemma 6.12.1 (2): the stalk `ℱ_x` is the colimit of the diagram of sections over open
neighborhoods of `x` in the category of abelian groups. In Lean this owner construction is the
canonical mathlib declaration `TopCat.Presheaf.stalk`, defined as that colimit. -/
recall TopCat.Presheaf.stalk

end
