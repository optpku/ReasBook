module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section

variable [HasWeakSheafify J (Type (max u v))]
variable (E : Type (max u v)) (F : Sheaf J (Type (max u v)))

/- Domain-style sampling for Example 7.10.13:
- primary domain: constant sheaves and global sections on a site;
- sampled owner API:
  `CategoryTheory.constantSheaf`,
  `CategoryTheory.HasGlobalSectionsFunctor`,
  `CategoryTheory.Sheaf.Γ`,
  `CategoryTheory.constantSheafΓAdj`;
- best owner abstraction: the adjunction `constantSheafΓAdj J (Type (max u v))`
  between the constant-sheaf functor and the global-sections functor;
- primitive data: the site `(C, J)`, the value `E : Type (max u v)`, and the sheaf `F`;
- derived API: the Hom-set bijection exported by
  `(constantSheafΓAdj J (Type (max u v))).homEquiv`.

Source/core/bridge triage:
- `source-facing`: the constant sheaf with value `E` and the bijection
  `Mor(underline E, F) = Mor_Sets(E, Γ(C, F))`;
- `core/canonical`: `constantSheaf` and `Γ`, organized by the adjunction
  `constantSheafΓAdj`;
- `bridge/view`: the source-text bijection is the `homEquiv` of `constantSheafΓAdj`.

This file therefore targets the `bridge/view` layer: the source statement carries no extra data
past the canonical constant-sheaf/global-sections adjunction, so the correct refinement is direct
recall of the owner declarations and their `homEquiv`, not a local duplicate wrapper.
-/

/- Example 7.10.13: for a site `(C, J)`, the constant sheaf with value `E` is the canonical
mathlib construction `CategoryTheory.constantSheaf J (Type (max u v))` specialized at `E`; by
definition this is the sheafification of the constant presheaf with value `E`. -/
recall constantSheaf

/- Example 7.10.13: the global-sections functor on `Type`-valued sheaves is the canonical owner
`CategoryTheory.Sheaf.Γ J (Type (max u v))`, defined whenever the constant-sheaf functor admits a
right adjoint; for `Type`, this exists from the standard limits-based instance. -/
recall Sheaf.Γ

/- Example 7.10.13: the mathematical core of the characterization of the constant sheaf is the
constant-sheaf/global-sections adjunction. Specializing `constantSheafΓAdj.homEquiv` for
`constantSheafΓAdj J (Type (max u v))` recovers the source-text bijection
`Mor(underline E, F) = Mor_Sets(E, Γ(C, F))`. -/
recall constantSheafΓAdj

#check ((constantSheafΓAdj J (Type (max u v))).homEquiv E F :
  ((constantSheaf J (Type (max u v))).obj E ⟶ F) ≃
    (E ⟶ (Γ J (Type (max u v))).obj F))

end

end CategoryTheory
