module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

notation:max "Mod(" 𝒪 ")" => SheafOfModules 𝒪

open CategoryTheory

universe u

variable {X : TopCat.{u}}
variable (𝒪 : TopCat.Sheaf RingCat.{u} X)

/- Domain-style sampling for Definition 6.10.1:
- primary domain: sheaves of modules over a sheaf of rings on a topological space;
- sampled owner abstractions:
  `TopCat.Sheaf`,
  `SheafOfModules`,
  `SheafOfModules.forget`,
  `SheafOfModules.toSheaf`;
- source-facing layer: the Stacks notation `Mod(𝒪)` for the category of sheaves of `𝒪`-modules
  on `X`;
- core/canonical owner: `SheafOfModules 𝒪`;
- bridge/view layer: the notation `Mod(𝒪)` on top of the owner `SheafOfModules 𝒪`;
- derived API: the forgetful functors `SheafOfModules.forget 𝒪` and
  `SheafOfModules.toSheaf 𝒪`.

Primitive data are already owned by the mathlib structure `SheafOfModules`, so this file should
recall that canonical owner directly and expose only the source-facing notation `Mod(𝒪)`, rather
than introduce any local alias or wrapper.
-/

/- Definition 6.10.1 (Tag 0077): for a topological space `X` and a sheaf of rings `𝒪` on `X`,
the canonical owner for the category of sheaves of `𝒪`-modules is `SheafOfModules 𝒪`. By
definition, its objects are presheaves of `𝒪`-modules whose underlying presheaves of abelian
groups are sheaves, and its morphisms are morphisms of presheaves of `𝒪`-modules. -/
recall SheafOfModules

/- Source-facing bridge: Stacks writes the same category as `Mod(𝒪)`. -/
#check Mod(𝒪)

variable (ℱ 𝒢 : Mod(𝒪))

/- Companion recall: morphisms in `Mod(𝒪)` are morphisms in the canonical owner category. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: the underlying presheaf of `𝒪`-modules of a sheaf of `𝒪`-modules is
obtained by the canonical forgetful functor `SheafOfModules.forget`. -/
#check (SheafOfModules.forget 𝒪)

/- Companion recall: the underlying sheaf of abelian groups of a sheaf of `𝒪`-modules is
obtained by the canonical functor `SheafOfModules.toSheaf`. -/
#check (SheafOfModules.toSheaf 𝒪)
