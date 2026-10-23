module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

section

variable {X : TopCat.{u}} (𝒪 : X.Presheaf RingCat) (ℱ : PresheafOfModules 𝒪) (x : X)

/- Domain-style sampling for Lemma 6.14.1:
- primary domain: stalks of ring-valued presheaves and their module-valued presheaves on
  topological spaces;
- sampled owner declarations:
  `Presheaf.stalk`,
  the canonical instance `Module (𝒪.stalk x) ↑(Presheaf.stalk ℱ.presheaf x)`,
  `PresheafOfModules.germ_ringCat_smul`,
  `PresheafOfModules.germ_smul`;
- owner abstraction: the canonical owner is the stalk of the underlying presheaf together with the
  mathlib-provided `𝒪_x`-module instance on that stalk;
- primitive data: a ring-valued presheaf `𝒪`, a presheaf of `𝒪`-modules `ℱ`, and a point `x`;
- derived API: the induced module structure on `ℱ_x` and the germ compatibility formula for scalar
  multiplication.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that the stalk `ℱ_x` is naturally an `𝒪_x`-module;
- `core/canonical`: `Presheaf.stalk` plus the canonical instance
  `Module (𝒪.stalk x) ↑(Presheaf.stalk ℱ.presheaf x)`;
- `bridge/view`: `PresheafOfModules.germ_ringCat_smul`, which exposes the module structure through
  the germ formula.

This file should therefore stay in direct recall/use form and avoid introducing any parallel local
wrapper for stalk modules. -/

/- Lemma 6.14.1 (Tag 007J): for a presheaf of modules over a presheaf of rings, the stalk carries
the canonical `𝒪_x`-module structure already provided by mathlib. -/
#check (inferInstance : Module (𝒪.stalk x) ↑(Presheaf.stalk ℱ.presheaf x))

/- Companion recall: the canonical stalk module structure is characterized by compatibility of
germs with scalar multiplication. -/
recall PresheafOfModules.germ_ringCat_smul

end
