module

import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_31_7

@[expose] public section

open CategoryTheory TopCat
open TopologicalSpace.Opens

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.6:
- primary domain: extension by zero / extension by the initial object for presheaves and sheaves of
  abelian groups along an open immersion;
- sampled owner declarations:
  `OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`;
- owner abstraction: the Chapter 6 owner is the generic
  `OpenSubsetExtensionByInitial` API for extension by the initial object along
  `extensionByZeroOpenSubsetInclusion U`;
- primitive data: the open subset `U`, the point `x`, and the abelian sheaf or presheaf on the
  open subspace `extensionByZeroOpenSubsetSpace U`;
- derived API: the abelian-group specialization of the owner adjunction, stalk description, and
  unit isomorphisms.

Source/core/bridge triage:
- `source-facing`: the five Stacks-project statements about extension by zero for abelian sheaves
  and presheaves;
- `core/canonical`: the owner declarations in `OpenSubsetExtensionByInitial`;
- `bridge/view`: this file’s `AddCommGrpCat` specialization of those owner declarations.

The file should therefore reuse the owner declarations directly and avoid keeping a second public
stalk-isomorphism wrapper with the same interface.
-/

section Presheaf

variable {X : TopCat.{u}}

/- Lemma 6.31.6 (1): for an open subset `U ⊆ X`, extension by zero on presheaves of abelian
groups is left adjoint to restriction to `U`. This is the `AddCommGrpCat` specialization of the
canonical extension-by-initial-object adjunction. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialAdjunction

/- Lemma 6.31.6 (4): on presheaves of abelian groups over `U`, the unit
`𝟭 ⟶ j_p j_{p!}` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.presheafExtensionByInitialUnitIso

end Presheaf

section Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Lemma 6.31.6 (2): for an open subset `U ⊆ X`, extension by zero on sheaves of abelian groups
is left adjoint to restriction to `U`. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction

/- Lemma 6.31.6 (3): for a point `x` of `X`, the stalk of the extension-by-zero sheaf `j_! ℱ`
is canonically identified with the stalk of `ℱ` when `x ∈ U`, and with the zero object when
`x ∉ U`. This is the `AddCommGrpCat` specialization of the owner stalk iso
`OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso` (branch identifications
`_stalkIso_comp_eq_of_mem` / `_of_not_mem`). -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso

/- Lemma 6.31.6 (5): on sheaves of abelian groups over `U`, the unit
`𝟭 ⟶ j⁻¹ j_!` is a natural isomorphism. -/
recall OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso

end Sheaf
