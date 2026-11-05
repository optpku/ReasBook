module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace

universe u

section

variable {X : TopCat} (ℱ : TopCat.Sheaf (Type u) X) (U : Opens X)

/- Domain-style sampling for Lemma 6.11.1:
- primary domain: sheaf sections and the sheafification-unit comparison with stalk families on a
  topological space;
- sampled owner declarations:
  `TopCat.Presheaf.section_ext`,
  `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- best owner abstraction: the canonical sheaf extensionality theorem `section_ext`; the other
  sampled declarations are adjacent owner API for deriving sectionwise injectivity from stalk maps,
  but the present source-facing statement is directly about equality of stalk germs;
- primitive data: the sheaf `ℱ` and the open subset `U`;
- derived API: the map `ℱ.presheaf.toSheafify.app (op U)` and its underlying stalk-family
  function.

Source/core/bridge triage:
- `source-facing`: injectivity of the canonical map from sections on `U` to the family of stalks
  over points of `U`;
- `core/canonical`: `TopCat.Presheaf.section_ext`;
- `bridge/view`: `ℱ.presheaf.toSheafify.app (op U)`. -/
/-- Lemma 6.11.1: for every open subset `U` of `X`, the canonical map from sections of `ℱ` on
`U` to the family of stalks `(ℱ_x)_{x ∈ U}` is injective. -/
theorem sectionToStalkFamily_injective :
    Function.Injective (fun s ↦ (ℱ.presheaf.toSheafify.app (op U) s).1) := by
  intro s t hst
  exact section_ext ℱ U s t fun x hx ↦ congrFun hst ⟨x, hx⟩

end
