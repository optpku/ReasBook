module

import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_31_7

@[expose] public section

open TopCat

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.4:
- primary domain: extension by the initial object along the inclusion `j : U ↪ X` of an open
  subset, specialized to presheaves and sheaves of sets;
- sampled owner declarations:
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`;
- owner abstraction: the Chapter 6 owner is `OpenSubsetExtensionByInitial`; this file should stay
  `source-facing` and reuse that owner directly rather than restating set-specific wrappers;
- primitive data: the open subset `U`, the point `x`, and the upstream owner functors on
  `extensionByZeroOpenSubsetSpace U`;
- derived API: the `Type u` specialization of the adjunctions, stalk description, and unit
  isomorphisms.

Source/core/bridge triage:
- `source-facing`: the five Stacks-project statements about extension by the empty set on
  presheaves and sheaves of sets;
- `core/canonical`: the owner declarations in `OpenSubsetExtensionByInitial`;
- `bridge/view`: the specialization `C = Type u`, where the initial object is the empty type.
-/

section

variable {X : TopCat.{u}}

/- Lemma 6.31.4 (1): on presheaves of sets over an open subset `U ⊆ X`, extension by the empty
set is left adjoint to restriction to `U`. This is the specialization of the canonical
presheaf-level extension-by-initial-object adjunction to `Type u`, where the initial object is the
empty type. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction

/- Lemma 6.31.4 (2): on sheaves of sets over an open subset `U ⊆ X`, extension by the empty set
is left adjoint to restriction to `U`. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction

/- Lemma 6.31.4 (3): for a point `x` of `X`, the stalk of the extension-by-empty sheaf `j_! ℱ`
is canonically identified with the stalk of `ℱ` when `x ∈ U`, and with the empty set when
`x ∉ U`. The owner stalk-description theorem is `sheafExtensionByInitial_stalkIso` (the canonical
by-cases stalk iso), with branch identifications `_stalkIso_comp_eq_of_mem` / `_of_not_mem`. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso

/- Lemma 6.31.4 (4): on presheaves over `U`, the unit
`𝟭 ⟶ j_p j_{p!}` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialUnitIso

/- Lemma 6.31.4 (5): on sheaves over `U`, the unit
`𝟭 ⟶ j⁻¹ j_!` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso

end
