module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_26_1
public import stacks_project.Chap06.Lemma_6_26_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] Classical.propDecidable

/-
Domain-style sampling for Lemma 6.27.3:
- primary domain: stalk/skyscraper adjunctions for sheaves on topological spaces and the
  pullback/pushforward adjunction for sheaves of modules on ringed spaces;
- sampled owner declarations:
  `stalkSkyscraperSheafAdjunction`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSpace.Hom.pullbackStalkIso`;
- best owner abstraction: the sheaf-of-sets statement is already owned by
  `stalkSkyscraperSheafAdjunction`, and the module statement is the specialization of the
  canonical pullback/pushforward adjunction to the point inclusion `i_x`, with
  `RingedSpace.Hom.pullbackStalkIso` providing the bridge back to the source-facing stalk module.
-/

/- Lemma 6.27.3: let `X` be a topological space and let `x : X` be a point. Then the functors
`ℱ ↦ ℱ_x` and `A ↦ i_{x, *} A` are adjoint. The canonical mathlib declaration is the generic
adjunction `stalkSkyscraperSheafAdjunction`; specializing to sheaves of sets recovers the
Stacks-style bijection `Mor_Sets(ℱ_x, A) ≃ Mor_Sh(X)(ℱ, i_{x, *} A)`. -/
recall stalkSkyscraperSheafAdjunction

namespace AlgebraicGeometry

section

variable {Y : TopCat.{u}} (y : Y)
variable (ℱ : TopCat.Sheaf (Type u) Y) (A : Type u)

/- Lemma 6.27.3, sheaf-of-sets owner form: specialize the canonical stalk/skyscraper adjunction
at the point `y`. -/
#check
  (((stalkSkyscraperSheafAdjunction (C := Type u) y).homEquiv ℱ A) :
    (ℱ.presheaf.stalk y ⟶ A) ≃ (ℱ ⟶ skyscraperSheaf y A))

end

section

variable {X : RingedSpace.{u}}
variable (x : X)

/-- Helper for Lemma 6.27.3: the presheaf map defining the point inclusion
`({x}, \mathcal O_{X, x}) \to (X, \mathcal O_X)`. -/
private noncomputable def pointInclusionPresheafMap (x : X) :
    X.presheaf ⟶
      (ofHom (ContinuousMap.const (TopCat.of PUnit) x)) _*
        (skyscraperSheaf PUnit.unit (X.presheaf.stalk x)).obj :=
  ((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom ≫
    eqToHom (skyscraperPresheaf_eq_pushforward x (X.presheaf.stalk x))

/-- Helper for Lemma 6.27.3: the one-point ringed space `({x}, \mathcal O_{X, x})`. -/
private noncomputable def pointRingedSpace (x : X) : RingedSpace :=
  let pointSheaf := skyscraperSheaf PUnit.unit (X.presheaf.stalk x)
  { carrier := TopCat.of PUnit
    presheaf := pointSheaf.obj
    IsSheaf := pointSheaf.property }

/-- Helper for Lemma 6.27.3: the canonical point inclusion `i_x`. -/
private noncomputable def pointInclusion (x : X) : pointRingedSpace x ⟶ X :=
  InducedCategory.homMk
    { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
      c := pointInclusionPresheafMap x }

section

variable (ℱ : X.Modules)
variable (G : RingedSpace.Modules (pointRingedSpace x))

/- Lemma 6.27.3, module owner form: specialize the canonical pullback/pushforward adjunction for
sheaves of modules to the point inclusion `i_x`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom (pointInclusion x))).homEquiv ℱ G) :
    (((pointInclusion x)^*).obj ℱ ⟶ G) ≃
      (ℱ ⟶ ((pointInclusion x) _*).obj G))

/- Lemma 6.27.3, stalk bridge: the source-facing stalk-module formulation is obtained from the
owner adjunction above by the canonical stalk comparison at the unique point of `({x}, \mathcal
O_{X, x})`. -/
#check RingedSpace.Hom.pullbackStalkIso (pointInclusion x) ℱ PUnit.unit

end

end

end AlgebraicGeometry
