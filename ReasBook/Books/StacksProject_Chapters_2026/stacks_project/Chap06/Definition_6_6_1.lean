module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

notation:max "PMod(" 𝒪 ")" => PresheafOfModules 𝒪

open CategoryTheory

universe u

variable {X : TopCat.{u}}
variable (𝒪 : X.Presheaf RingCat.{u})

/- Domain-style sampling for Definition 6.6.1:
- primary domain: presheaves of modules over a ring-valued presheaf on a topological space;
- sampled owner abstractions:
  `PresheafOfModules`,
  `PresheafOfModules.presheaf`,
  `PresheafOfModules.map_smul`,
  `SheafOfModules`;
- source-facing layer: the Stacks category `PMod(𝒪)` of presheaves of `𝒪`-modules on `X`;
- core/canonical owner: `PresheafOfModules 𝒪`;
- bridge/view layer: the notation `PMod(𝒪)` on top of the canonical owner
  `PresheafOfModules 𝒪`;
- primitive data versus derived API: `PresheafOfModules` already owns the module objects and
  semilinear restriction maps as primitive data, while the underlying presheaf of abelian groups
  and the semilinearity lemma are derived API. This file should therefore recall the canonical
  owner directly and expose the source-facing notation `PMod(𝒪)`, rather than introduce a local
  alias or wrapper.
-/

/- Definition 6.6.1 (Tag 006P): for a presheaf of rings `𝒪` on a topological space `X`, the
Stacks Project category `PMod(𝒪)` of presheaves of `𝒪`-modules with `𝒪`-linear morphisms is the
canonical mathlib category `PresheafOfModules 𝒪`. -/
recall PresheafOfModules

/- Source-facing bridge: Stacks writes the same category as `PMod(𝒪)`. -/
#check PMod(𝒪)

variable (ℱ 𝒢 : PMod(𝒪))

/- Companion recall: morphisms in `PMod(𝒪)` are precisely the morphisms in the canonical category
`PresheafOfModules 𝒪`. -/
#check (ℱ ⟶ 𝒢)

/- Companion recall: a presheaf of `𝒪`-modules carries its canonical underlying presheaf of
abelian groups, given by `PresheafOfModules.presheaf`. -/
recall PresheafOfModules.presheaf

/- Companion recall: the restriction maps in a presheaf of `𝒪`-modules are semilinear. -/
recall PresheafOfModules.map_smul
