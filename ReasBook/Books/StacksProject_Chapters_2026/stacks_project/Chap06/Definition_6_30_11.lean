module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_6_1
public import stacks_project.Chap06.Definition_6_30_2
public import stacks_project.Chap06.Definition_6_10_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]
variable {B : Set (Opens X)}

/- Domain-style sampling for Definition 6.30.11:
- primary domain: presheaves and sheaves of modules over a ring-valued presheaf or sheaf on the
  basis site attached to a topological basis;
- sampled owner abstractions:
  `PMod(𝒪)`,
  `PresheafOfModules`,
  `PresheafOfModules.presheaf`,
  `SheafOfModules`,
  `SheafOfModules.forget`;
- source-facing layer: the Stacks categories of presheaves and sheaves of `𝒪`-modules on the
  basis `B`;
- core/canonical owner: `PresheafOfModules 𝒪` in the presheaf case and `SheafOfModules 𝒪` in the
  sheaf case;
- bridge/view layer: the notation `PMod(𝒪)` from Definition 6.6.1 in the presheaf case and
  `Mod(𝒪)` from Definition 6.10.1 in the sheaf case;
- primitive data versus derived API: `PresheafOfModules` already owns the module objects and
  semilinear restriction maps, while `SheafOfModules` adds only the sheaf condition on the
  underlying abelian presheaf. This file should therefore recall those owners directly, rather
  than introduce a basis-site-specific wrapper.
-/

section PresheafCase

variable (𝒪 : (BasisOpen B)ᵒᵖ ⥤ RingCat.{u})

/- Definition 6.30.11 (1): for a ring-valued presheaf `𝒪` on the basis site `B`, the canonical
owner for presheaves of `𝒪`-modules is `PresheafOfModules`. Specialized to the basis site, the
source-facing category is written `PMod(𝒪)` and has canonical owner `PresheafOfModules 𝒪`. -/
recall PresheafOfModules

/- Source-facing Stacks notation for the same owner on the basis site. -/
#check PMod(𝒪)

variable (ℱ 𝒢 : PMod(𝒪))

/- Definition 6.30.11 (2): a morphism of presheaves of `𝒪`-modules on `B` is a morphism in the
category `PMod(𝒪)`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: restriction maps in a presheaf of `𝒪`-modules are semilinear, and the
underlying presheaf of abelian groups is the canonical `PresheafOfModules.presheaf`. -/
recall PresheafOfModules.map_smul
recall PresheafOfModules.presheaf

end PresheafCase

section SheafCase

variable {hB : Opens.IsBasis B}
variable (𝒪 : BasisSiteSheaf RingCat.{u} B hB)

/- Definition 6.30.11 (3): for a sheaf of rings `𝒪` on the basis site `B`, the canonical owner
for sheaves of `𝒪`-modules is `SheafOfModules`. On the source-facing surface from
Definition 6.10.1, the same category is written `Mod(𝒪)`. -/
recall SheafOfModules

/- Source-facing Stacks notation for the same owner. -/
#check Mod(𝒪)

variable (ℱ 𝒢 : Mod(𝒪))

/- A morphism of sheaves of `𝒪`-modules on the basis site is a morphism in `Mod(𝒪)`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recalls: the underlying presheaf of modules and the underlying sheaf of abelian
groups of a sheaf of `𝒪`-modules are obtained by the canonical functors
`SheafOfModules.forget 𝒪` and `SheafOfModules.toSheaf 𝒪`. -/
#check (SheafOfModules.forget 𝒪)
#check (SheafOfModules.toSheaf 𝒪)

end SheafCase
