module

import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_4_4
public import stacks_project.Chap06.Definition_6_8_1
public import stacks_project.Chap06.Lemma_6_21_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TopCat

/-
Domain-style sampling for Lemma 6.22.1:
- primary domain: stalks of inverse-image presheaves and sheaves along a continuous map of
  topological spaces;
- inspected owner declarations:
  `TopCat.Presheaf.stalkPullbackIso`,
  `TopCat.Sheaf.stalkPullbackIso`,
  `TopCat.Presheaf.pullback`,
  `TopCat.Sheaf.pullback`;
- owner abstraction:
  the presheaf statement is owned upstream by the mathlib declaration
  `TopCat.Presheaf.stalkPullbackIso`,
  while the sheaf statement is owned in this chapter by the bridge declaration
  `TopCat.Sheaf.stalkPullbackIso`;
- primitive data: a continuous map `f : X ⟶ Y`, a point `x : X`, and a presheaf or sheaf `𝒢` on
  `Y`;
- derived API: only the `AddCommGrpCat` specializations displayed below as thin companion checks.

Source/core/bridge triage:
- `source-facing`: the abelian-specialized stalk identification for inverse image;
- `core/canonical`: `TopCat.Presheaf.stalkPullbackIso`;
- `bridge/view`: `TopCat.Sheaf.stalkPullbackIso`, which transports the presheaf owner to sheaf
  pullback.

The file therefore should not introduce any local `...Iso` wrapper: the correct refinement is
direct recall of the existing owners, with only thin `AddCommGrpCat` specialization companions.
-/

universe u

/- Lemma 6.22.1 (1): for a continuous map `f : X ⟶ Y`, an abelian presheaf `𝒢` on `Y`, and a
point `x : X`, the canonical stalk identification is exactly the `AddCommGrpCat` specialization of
the owner `TopCat.Presheaf.stalkPullbackIso`. -/
recall TopCat.Presheaf.stalkPullbackIso

namespace TopCat.Presheaf

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
variable (𝒢 : PAb(Y))

/- Companion specialization of `TopCat.Presheaf.stalkPullbackIso` to abelian presheaves. -/
#check
  (show 𝒢.stalk (f x) ≅
      ((pullback AddCommGrpCat f).obj 𝒢).stalk x from
    stalkPullbackIso AddCommGrpCat f 𝒢 x)

end

end TopCat.Presheaf

/- Lemma 6.22.1 (2): for a continuous map `f : X ⟶ Y`, an abelian sheaf `𝒢` on `Y`, and a point
`x : X`, the canonical stalk identification is exactly the chapter bridge owner
`TopCat.Sheaf.stalkPullbackIso`. -/
recall TopCat.Sheaf.stalkPullbackIso

namespace TopCat.Sheaf

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
variable (𝒢 : Ab(Y))

/- Companion specialization of `TopCat.Sheaf.stalkPullbackIso` to abelian sheaves. -/
#check
  (show 𝒢.presheaf.stalk (f x) ≅
      ((f⁻¹).obj 𝒢).presheaf.stalk x from
    stalkPullbackIso f 𝒢 x)

end

end TopCat.Sheaf
