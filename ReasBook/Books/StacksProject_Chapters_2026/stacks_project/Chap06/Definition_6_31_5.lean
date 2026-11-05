module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Extension_by_zero_by_the_initial_object

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u v

/-
Domain-style sampling for Definition 6.31.5:
- primary domain: extension by zero / extension by the initial object along the inclusion
  `j : U ↪ X` of an open subset, for presheaves, sheaves, and modules;
- sampled owner declarations:
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`,
  `openSubsetModulePresheafExtensionByZero`,
  `openSubsetModuleSheafExtensionByZero`;
- source/core/bridge triage:
  `source-facing`: the six Stacks variants of extension by zero along an open immersion;
  `core/canonical`: the owner functors above, built on `extensionByZeroOpenSubsetSpace U` and the
  canonical pullback functors along `extensionByZeroOpenSubsetInclusion U`;
  `bridge/view`: the abelian specialization `C = AddCommGrpCat` of extension by the initial
  object, and the module-valued specializations obtained from the ambient ring object on `X`;
- primitive data versus derived API: the primitive inputs are the open subset `U`, the target
  category together with the initial-object and sheafification hypotheses needed by the owner
  functors, and in the module case the ambient ring-valued presheaf or sheaf `𝒪`. The abelian and
  module statements here are derived specializations of those owners, so this file should recall or
  check the canonical upstream declarations directly rather than keep parallel local wrappers.
-/

section

variable {X : TopCat.{u}}

section AbelianExtensionByZero

variable (U : Opens X)

/- Definition 6.31.5 (1), source-facing specialization: for an abelian presheaf `ℱ` on `U`,
extension by zero is the `AddCommGrpCat` specialization `jₚ! U` of the canonical presheaf owner
`openSubsetPresheafExtensionByInitialObject`. -/
#check
  (jₚ! U :
    (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u})

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Definition 6.31.5 (2), source-facing specialization: for an abelian sheaf `ℱ` on `U`,
extension by zero is the `AddCommGrpCat` specialization `j! U` of the canonical sheaf owner
`openSubsetSheafExtensionByInitialObject`. -/
#check
  (j! U :
    (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u})

end AbelianExtensionByZero

section PresheafExtensionByInitial

variable {C : Type v} [Category.{v} C] [HasInitial C]
variable (U : Opens X)

/- Definition 6.31.5 (3): for a category `C` with an initial object, extension by the initial
object along `U ↪ X` is the canonical presheaf functor
`openSubsetPresheafExtensionByInitialObject U`. -/
recall openSubsetPresheafExtensionByInitialObject

end PresheafExtensionByInitial

section SheafExtensionByInitial

variable {C : Type v} [Category.{v} C] [HasInitial C]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]
variable (U : Opens X)

/- Definition 6.31.5 (4): for sheaves valued in a category with an initial object and
sheafification, extension by the initial object along `U ↪ X` is the canonical sheaf functor
`openSubsetSheafExtensionByInitialObject U`. -/
recall openSubsetSheafExtensionByInitialObject

end SheafExtensionByInitial

section ModulePresheafExtensionByZero

variable (U : Opens X)
variable (𝒪 : X.Presheaf RingCat.{u})

/- Definition 6.31.5 (5): for a presheaf of rings `𝒪` on `X`, extension by zero on
`𝒪|_U`-modules is the canonical module-valued presheaf functor
`openSubsetModulePresheafExtensionByZero U 𝒪`. -/
recall openSubsetModulePresheafExtensionByZero

/- Companion specialization to the ambient ring-valued presheaf `𝒪`. -/
#check
  ((openSubsetModulePresheafExtensionByZero U 𝒪) :
    PresheafOfModules
        ((Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      PresheafOfModules 𝒪)

end ModulePresheafExtensionByZero

section ModuleSheafExtensionByZero

variable (U : Opens X)
variable (𝒪 : X.Sheaf RingCat.{u})

/- Definition 6.31.5 (6): for a sheaf of rings `𝒪` on `X`, extension by zero on `𝒪|_U`-modules
is the canonical module-valued sheaf functor `openSubsetModuleSheafExtensionByZero U 𝒪`. -/
recall openSubsetModuleSheafExtensionByZero

/- Companion specialization to the ambient ring-valued sheaf `𝒪`. -/
#check
  ((openSubsetModuleSheafExtensionByZero U 𝒪) :
    SheafOfModules
        ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      SheafOfModules 𝒪)

end ModuleSheafExtensionByZero

end
