module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

section

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u)) (x : X)

/- Domain-style sampling for Lemma 6.17.2:
- primary domain: sheafification and stalks of set-valued presheaves on a topological space;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.stalkToFiber`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- best owner abstraction: the canonical stalk isomorphism
  `TopCat.Presheaf.sheafifyStalkIso`;
- primitive data: the space `X`, the presheaf `ℱ`, and the point `x : X`;
- derived API: the map on stalks induced by `toSheafify` and its inverse `stalkToFiber`.

Source/core/bridge triage:
- `source-facing`: the Stacks Project statement identifying the stalk of `ℱ^#` at `x` with `ℱ_x`;
- `core/canonical`: `TopCat.Presheaf.sheafifyStalkIso`;
- `bridge/view`: the intermediate morphism `TopCat.Presheaf.stalkToFiber` and the isomorphism on
  stalks induced by `toSheafify`. -/

/- Lemma 6.17.2: the canonical comparison between the stalk of the sheafification `ℱ^#` at `x`
and the original stalk `ℱ_x` is exactly the owner isomorphism `TopCat.Presheaf.sheafifyStalkIso`.
-/
recall TopCat.Presheaf.sheafifyStalkIso

/- Source-facing specialization: for `x : X`, the stalk of `ℱ^#` at `x` is canonically
isomorphic to the original stalk `ℱ_x`. -/
#check (ℱ.sheafifyStalkIso x : ℱ.sheafify.presheaf.stalk x ≅ ℱ.stalk x)

end
