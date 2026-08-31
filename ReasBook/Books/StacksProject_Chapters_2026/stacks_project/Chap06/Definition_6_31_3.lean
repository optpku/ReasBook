module

import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Extension_by_zero_by_the_initial_object

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe v

/-
Domain-style sampling for Definition 6.31.3:
- primary domain: extension by zero / by the initial object along the inclusion `j : U ↪ X` of an
  open subset, specialized to set-valued presheaves and sheaves;
- sampled owner declarations:
  `extensionByZeroOpenSubsetSpace`,
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`;
- owner abstraction: the canonical owners are the presheaf and sheaf functors above on the open
  subspace `extensionByZeroOpenSubsetSpace U`; this file should specialize those owners to
  `Type v` rather than introduce a parallel set-specific wrapper;
- primitive data versus derived API: the primitive input is the open subset `U`, together with the
  canonical open-subspace object and the upstream extension-by-initial-object owners. The
  set-valued “extension by the empty set” phrasing is derived from the fact that the initial object
  of `Type v` is the empty type, and the sheaf-level construction is derived by sheafifying the
  presheaf-level owner.

Source/core/bridge triage:
- `source-facing`: the Stacks set-valued phrasing “extension by the empty set” on an open subset;
- `core/canonical`: `openSubsetPresheafExtensionByInitialObject` and
  `openSubsetSheafExtensionByInitialObject`;
- `bridge/view`: the specialization `C = Type v`, where the initial object is the empty type.
-/

section

variable {X : TopCat.{v}}

section PresheafCase

variable (U : Opens X)

/- Definition 6.31.3, core/canonical recall: the owner construction for extension by zero along an
open subset is `openSubsetPresheafExtensionByInitialObject`. -/
recall openSubsetPresheafExtensionByInitialObject

/- Definition 6.31.3, source-facing specialization: for presheaves of sets on an open subset
`U ⊆ X`, extension by the empty set is the `Type v` specialization `jₚ! U`; in `Type v`, the
initial object is the empty type. -/
#check
  (jₚ! U :
    (extensionByZeroOpenSubsetSpace U).Presheaf (Type v) ⥤ X.Presheaf (Type v))

end PresheafCase

section SheafCase

variable (U : Opens X)

/- Definition 6.31.3, core/canonical recall: the owner construction for sheaf-level extension by
the initial object along an open subset is `openSubsetSheafExtensionByInitialObject`. -/
recall openSubsetSheafExtensionByInitialObject

/- Definition 6.31.3, source-facing specialization: for sheaves of sets on an open subset
`U ⊆ X`, extension by the empty set is the `Type v` specialization `j! U`; by definition it is
obtained by sheafifying the presheaf-level construction. -/
#check
  (j! U :
    (extensionByZeroOpenSubsetSpace U).Sheaf (Type v) ⥤ X.Sheaf (Type v))

end SheafCase

end
