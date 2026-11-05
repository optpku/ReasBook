module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Definition_6_11_2
public import stacks_project.Chap06.Definition_6_16_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.17.5:
- primary domain: separated presheaves of sets and sheafification on a topological space;
- inspected owner declarations:
  `TopCat.Presheaf.isSeparated_iff_injective_toStalkFamily`,
  `presheaf_mono_iff_app_injective`;
- best owner abstraction: the categorical predicate `Mono` on the canonical unit
  `ℱ.toSheafify : ℱ ⟶ ℱ^#`, with objectwise injectivity as derived API;
- primitive data: the separatedness predicate and the sheafification unit;
- derived API: sectionwise injectivity and the passage between injectivity into the sheafification
  subtype and injectivity of the underlying stalk-family map.

Source/core/bridge triage:
- `source-facing`: the Stacks Project comparison between separatedness and the canonical map to
  sheafification;
- `core/canonical`: `Mono ℱ.toSheafify`;
- `bridge/view`: Definition 6.11.2 and Definition 6.16.2, which express the source statement via
  injectivity on sections. -/

-- Proof sketch: combine the source-facing separatedness criterion from Definition 6.11.2 with the
-- chapter owner theorem that identifies monomorphisms of presheaves of sets with objectwise
-- injectivity, then bridge the subtype-valued sheafification sections with their underlying
-- stalk-family functions.
/-- Lemma 6.17.5: a set-valued presheaf on `X` is separated if and only if the canonical map
`ℱ ⟶ ℱ^#` to its sheafification is a monomorphism. -/
theorem isSeparated_iff_mono_toSheafify :
    Presieve.IsSeparated J ℱ ↔ Mono ℱ.toSheafify := by
  rw [isSeparated_iff_injective_toStalkFamily, presheaf_mono_iff_app_injective]
  constructor
  · intro h U s t hst
    exact h U (congrArg Subtype.val hst)
  · intro h U s t hst
    exact h U (Subtype.ext hst)

end TopCat.Presheaf
