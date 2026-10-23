module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
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

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace Opposite
open scoped AlgebraicGeometry

attribute [local instance] Classical.propDecidable

universe u v w

section

variable {X : TopCat.{u}}
variable {C : Type v} [CategoryTheory.Category C] [CategoryTheory.Limits.HasTerminal C]

/- Domain-style sampling for Definition 6.27.1:
- primary domain: skyscraper sheaves on topological spaces and pushforward of module sheaves along
  morphisms of ringed spaces;
- sampled owner declarations:
  `TopCat.skyscraperSheaf`,
  `TopCat.stalkSkyscraperSheafAdjunction`,
  `AlgebraicGeometry.RingedSpace.Hom.pushforward`,
  `SheafOfModules.pushforward`;
- owner abstraction: `skyscraperSheaf` on the sheaf side and
  `((pointInclusion x) _*).obj` on the module-sheaf side;
- source/core/bridge triage:
  `source-facing`: the point ringed space `({x}, \mathcal O_{X, x})`, its inclusion `i_x`, and the
    skyscraper module sheaf `i_{x, *} M`;
  `core/canonical`: `skyscraperSheaf` and `RingedSpace.Hom.pushforward`;
  `bridge/view`: the concrete realization of `({x}, \mathcal O_{X, x})` on `TopCat.of PUnit`.

Primitive data are only the point `x`, the value `A`, and the stalk module `M`. The one-point
space, its unique point, and the auxiliary skyscraper sheaf on that space are implementation
choices, not separate owners, so the file should use the canonical declarations directly instead of
introducing parallel aliases.
-/

/- Definition 6.27.1 (1)–(3): for a point `x : X` and a value `A`, the skyscraper sheaf at `x`
with value `A` is the canonical mathlib sheaf `skyscraperSheaf x A`. In the classical Stacks
Project cases, `A` may be a set, an abelian group, or another algebraic structure. -/
recall skyscraperSheaf

/-- A sheaf is a skyscraper sheaf if it is isomorphic to `skyscraperSheaf x A` for some point
`x` and some value `A`. -/
def IsSkyscraperSheaf (ℱ : TopCat.Sheaf C X) : Prop :=
  ∃ (x : X) (A : C), IsIsomorphic ℱ (skyscraperSheaf x A)

@[simp] theorem isSkyscraperSheaf_skyscraperSheaf (x : X) (A : C) :
    IsSkyscraperSheaf (skyscraperSheaf x A) :=
  ⟨x, A, ⟨Iso.refl _⟩⟩

end

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}

open CategoryTheory.Limits

public noncomputable def pointInclusionPresheafMap (x : X) :
    X.presheaf ⟶
      (ofHom (ContinuousMap.const (TopCat.of PUnit) x)) _*
        (skyscraperSheaf PUnit.unit (X.presheaf.stalk x)).obj :=
  ((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom ≫
    eqToHom (skyscraperPresheaf_eq_pushforward x (X.presheaf.stalk x))

/-- The one-point ringed space `({x}, \mathcal O_{X, x})`, modeled on `TopCat.of PUnit` with
structure sheaf the skyscraper sheaf at its unique point valued in `\mathcal O_{X, x}`. -/
noncomputable def pointRingedSpace (x : X) : RingedSpace :=
  let pointSheaf := skyscraperSheaf PUnit.unit (X.presheaf.stalk x)
  { carrier := TopCat.of PUnit
    presheaf := pointSheaf.obj
    IsSheaf := pointSheaf.property }

/-- Definition 6.27.1 (1): the canonical morphism of ringed spaces
`i_x : ({x}, \mathcal O_{X, x}) \to (X, \mathcal O_X)`. -/
noncomputable def pointInclusion (x : X) : pointRingedSpace x ⟶ X :=
  InducedCategory.homMk
    { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
      c := pointInclusionPresheafMap x }

-- Proof sketch: unfold `pointInclusion`; the induced-category morphism was defined by the
-- constant base map together with the presheaf morphism `pointInclusionPresheafMap x`.
/-- Unfolding `pointInclusion` identifies its underlying morphism of presheafed spaces. -/
theorem pointInclusion_def (x : X) :
    (pointInclusion x).hom =
      { base := ofHom (ContinuousMap.const (TopCat.of PUnit) x)
        c := pointInclusionPresheafMap x } := by
  -- The induced-category morphism stores exactly the presheafed-space morphism used to build it.
  rfl

-- Proof sketch: unfold `pointInclusion`; the induced-category morphism was defined with base map
-- `ContinuousMap.const (TopCat.of PUnit) x`, so the underlying continuous map is definitionally
-- that constant map.
/-- The underlying continuous map of `pointInclusion x` is the constant map to `x`. -/
@[simp] theorem pointInclusion_hom_base (x : X) :
    (pointInclusion x).hom.base = ofHom (ContinuousMap.const (TopCat.of PUnit) x) := by
  -- Read off the base map from the defining presheafed-space morphism.
  rw [pointInclusion_def]

-- Proof sketch: apply `pointInclusion_hom_base` and evaluate the resulting equality of continuous
-- maps at the unique point `PUnit.unit`.
/-- Evaluating `pointInclusion x` at the unique point of `({x}, \mathcal O_{X, x})` returns `x`. -/
@[simp] theorem pointInclusion_hom_base_apply (x : X) :
    (pointInclusion x).hom.base PUnit.unit = x := by
  -- After identifying the base map, evaluation is just the constant map at `x`.
  rw [pointInclusion_hom_base]
  rfl

public theorem pointOpen_eq_top {U : Opens (TopCat.of PUnit)} (h : PUnit.unit ∈ U) :
    U = ⊤ := by
  ext y
  cases y
  simp [h]

private theorem pointOpen_eq_bot {U : Opens (TopCat.of PUnit)} (h : PUnit.unit ∉ U) :
    U = ⊥ := by
  ext y
  cases y
  constructor
  · intro hy
    exact (h hy).elim
  · intro hy
    exact False.elim hy

public noncomputable abbrev pointRingCatSheaf (x : X) :=
  RingedSpace.ringCatSheaf (pointRingedSpace x)

theorem pointRingedSpace_ringCatSheaf_obj_top (x : X) :
    (RingedSpace.ringCatSheaf (pointRingedSpace x)).obj.obj (op ⊤) =
      RingCat.of (X.presheaf.stalk x) := by
  let pointSheaf : Sheaf CommRingCat (TopCat.of PUnit) :=
    skyscraperSheaf PUnit.unit (X.presheaf.stalk x)
  change
    (forget₂ CommRingCat RingCat).obj
        (pointSheaf.obj.obj
          (op ⊤)) =
      RingCat.of (X.presheaf.stalk x)
  simp [pointSheaf, skyscraperSheaf, skyscraperPresheaf]
  rfl

public noncomputable def pointModulePresheafObj
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (U : (Opens (TopCat.of PUnit))ᵒᵖ) →
    ModuleCat.{u} ((pointRingCatSheaf x).obj.obj U) :=
  fun U ↦ by
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op ⊤ := by
        simpa using congrArg op (pointOpen_eq_top hU)
      subst hU'
      exact
        (ModuleCat.restrictScalars (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M
    · exact ⊤_ ModuleCat.{u} ((pointRingCatSheaf x).obj.obj U)

/-- Helper for Definition 6.27.1: on the top open of the one-point space,
`pointModulePresheafObj x M` is the stalk module `M` with scalars restricted along the canonical
identification of the top ring with `\mathcal O_{X, x}`. -/
private theorem pointModulePresheafObj_op_top
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    pointModulePresheafObj x M (op (⊤ : Opens (TopCat.of PUnit))) =
      (ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M := by
  -- On the unique nonempty open, the positive branch of `pointModulePresheafObj` is forced.
  simp [pointModulePresheafObj]

/-- Helper for Definition 6.27.1: on the bottom open of the one-point space,
`pointModulePresheafObj x M` is the terminal module. -/
private theorem pointModulePresheafObj_op_bot
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    pointModulePresheafObj x M (op (⊥ : Opens (TopCat.of PUnit))) =
      ⊤_ ModuleCat.{u} ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit)))) := by
  -- The empty open triggers the terminal-object branch of `pointModulePresheafObj`.
  dsimp [pointModulePresheafObj]
  split_ifs with h
  · exact (by simpa using h : False).elim
  · rfl

/-- Helper for Definition 6.27.1: the restriction map of the point-module presheaf is the explicit
top-branch restriction-of-scalars map, and otherwise the zero map into the terminal bottom value.
-/
public noncomputable def pointModulePresheafMap
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    {U V : (Opens (TopCat.of PUnit))ᵒᵖ} (i : U ⟶ V) :
    pointModulePresheafObj x M U ⟶
      (ModuleCat.restrictScalars ((pointRingCatSheaf x).obj.map i).hom).obj
        (pointModulePresheafObj x M V) := by
  by_cases hV : PUnit.unit ∈ unop V
  · have hU : PUnit.unit ∈ unop U := i.unop.le hV
    have hU' : U = op ⊤ := by
      simpa using congrArg op (pointOpen_eq_top hU)
    have hV' : V = op ⊤ := by
      simpa using congrArg op (pointOpen_eq_top hV)
    subst hU'
    subst hV'
    have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
    exact
      (ModuleCat.restrictScalarsId'
        ((pointRingCatSheaf x).obj.map i).hom
        (by
          subst hi
          exact congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_id (op ⊤)))).inv.app
        (pointModulePresheafObj x M (op ⊤))
  · simpa [pointModulePresheafObj, hV] using
      (0 :
        pointModulePresheafObj x M U ⟶
          (ModuleCat.restrictScalars
            ((pointRingCatSheaf x).obj.map i).hom).obj
              (pointModulePresheafObj x M V))

/-- Helper for Definition 6.27.1: on the top open, the point-module presheaf restriction map is
the explicit identity restriction-of-scalars isomorphism. -/
private theorem pointModulePresheafMap_op_top
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (i : op (⊤ : Opens (TopCat.of PUnit)) ⟶ op ⊤) :
    pointModulePresheafMap x M i =
      (ModuleCat.restrictScalarsId'
        ((pointRingCatSheaf x).obj.map i).hom
        (by
          have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
          subst hi
          exact congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_id (op ⊤)))).inv.app
        (pointModulePresheafObj x M (op ⊤)) := by
  -- On the unique top-open map, the helper definition lands in its explicit top branch.
  have hi : i = 𝟙 (op ⊤) := Subsingleton.elim _ _
  subst hi
  simp [pointModulePresheafMap]

/-- Helper for Definition 6.27.1: every point-module presheaf restriction map landing in the
bottom open is zero. -/
private noncomputable def pointModulePresheaf_restrictScalars_obj_op_bot_isTerminal
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    {U : (Opens (TopCat.of PUnit))ᵒᵖ}
    (i : U ⟶ op (⊥ : Opens (TopCat.of PUnit))) :
    IsTerminal
      ((ModuleCat.restrictScalars (RingCat.Hom.hom ((pointRingCatSheaf x).obj.map i))).obj
        (pointModulePresheafObj x M (op (⊥ : Opens (TopCat.of PUnit))))) := by
  -- Restricting scalars preserves the terminal bottom-open value.
  let F := ModuleCat.restrictScalars (RingCat.Hom.hom ((pointRingCatSheaf x).obj.map i))
  have hterminalTop :
      IsTerminal
        (F.obj (⊤_ ModuleCat ↑((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit)))))) := by
    exact
      IsTerminal.ofIso
        (terminalIsTerminal : IsTerminal (⊤_ ModuleCat ↑((pointRingCatSheaf x).obj.obj U)))
        (PreservesTerminal.iso F).symm
  exact
    IsTerminal.ofIso hterminalTop
      (Functor.mapIso F (eqToIso (pointModulePresheafObj_op_bot x M))).symm

/-- Helper for Definition 6.27.1: every point-module presheaf restriction map landing in the
bottom open is zero. -/
private theorem pointModulePresheafMap_to_op_bot
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    {U : (Opens (TopCat.of PUnit))ᵒᵖ}
    (i : U ⟶ op (⊥ : Opens (TopCat.of PUnit))) :
    pointModulePresheafMap x M i = 0 := by
  -- The empty open forces the bottom branch of `pointModulePresheafMap`.
  dsimp [pointModulePresheafMap]
  split_ifs with hV hU
  · exact (by simpa using hV : False).elim
  · exact (pointModulePresheaf_restrictScalars_obj_op_bot_isTerminal x M i).hom_ext _ _
  · exact (pointModulePresheaf_restrictScalars_obj_op_bot_isTerminal x M i).hom_ext _ _

/-- Helper for Definition 6.27.1: when all opens are the top open of the one-point space, the
composition law for `pointModulePresheafMap` is exactly the standard composition law for
restriction of scalars. -/
private theorem pointModulePresheafMap_comp_op_top
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (i j : op (⊤ : Opens (TopCat.of PUnit)) ⟶ op ⊤) :
    pointModulePresheafMap x M (i ≫ j) =
      pointModulePresheafMap x M i ≫
        (ModuleCat.restrictScalars ((pointRingCatSheaf x).obj.map i).hom).map
          (pointModulePresheafMap x M j) ≫
        (ModuleCat.restrictScalarsComp'
            ((pointRingCatSheaf x).obj.map i).hom
            ((pointRingCatSheaf x).obj.map j).hom
            ((pointRingCatSheaf x).obj.map (i ≫ j)).hom
            (congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_comp i j))).inv.app
          (pointModulePresheafObj x M (op (⊤ : Opens (TopCat.of PUnit)))) := by
  -- Route correction: once the two-open space is normalized to `⊤`, both arrows are identities,
  -- so the remaining coherence is the explicit restriction-of-scalars composition formula.
  have hi : i = 𝟙 (op (⊤ : Opens (TopCat.of PUnit))) := Subsingleton.elim _ _
  have hj : j = 𝟙 (op (⊤ : Opens (TopCat.of PUnit))) := Subsingleton.elim _ _
  subst hi
  subst hj
  -- After replacing both maps by identities, all three restriction maps are the explicit
  -- identity restriction-of-scalars isomorphism.
  rw [pointModulePresheafMap_op_top, pointModulePresheafMap_op_top]
  -- Their underlying linear maps all act as the identity on elements.
  ext m
  convert (rfl : m = m) using 1 <;> simp

public noncomputable def pointModulePresheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    PresheafOfModules.{u} (pointRingCatSheaf x).obj where
  obj := pointModulePresheafObj x M
  map {U V} i := pointModulePresheafMap x M i
  map_id := by
    intro U
    -- Normalize the open to `⊤` or `⊥` so the identity map becomes an explicit restriction map.
    by_cases hU : PUnit.unit ∈ unop U
    · have hU' : U = op (⊤ : Opens (TopCat.of PUnit)) := by
        simpa using congrArg op (pointOpen_eq_top hU)
      subst hU'
      -- On the top open, `map_id` is the standard restriction-of-scalars identity naturality.
      have hmap :
          RingCat.Hom.hom
              ((pointRingCatSheaf x).obj.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit))))) =
            RingHom.id ↑((pointRingCatSheaf x).obj.obj (op ⊤)) := by
        change
          RingCat.Hom.hom ((pointRingCatSheaf x).obj.map (𝟙 (op ⊤))) =
            RingCat.Hom.hom (𝟙 ((pointRingCatSheaf x).obj.obj (op ⊤)))
        simpa using
          congrArg RingCat.Hom.hom
            ((pointRingCatSheaf x).obj.map_id (op (⊤ : Opens (TopCat.of PUnit))))
      simpa [pointModulePresheafMap_op_top] using
        (ModuleCat.restrictScalarsId'App_inv_naturality
          (RingCat.Hom.hom
            ((pointRingCatSheaf x).obj.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit))))))
          hmap
          (𝟙 (pointModulePresheafObj x M (op (⊤ : Opens (TopCat.of PUnit)))))).symm
    · have hU' : U = op (⊥ : Opens (TopCat.of PUnit)) := by
        simpa using congrArg op (pointOpen_eq_bot hU)
      subst hU'
      -- On the bottom open, `map_id` is unique because the codomain is terminal.
      rw [pointModulePresheafMap_to_op_bot]
      exact
        (pointModulePresheaf_restrictScalars_obj_op_bot_isTerminal x M
          (𝟙 (op (⊥ : Opens (TopCat.of PUnit))))).hom_ext _ _
  map_comp := by
    intro U V W i j
    -- Normalize the codomain open first: the bottom branch is terminal, while the top branch is
    -- the unique nontrivial restriction-of-scalars computation on the one-point space.
    by_cases hW : PUnit.unit ∈ unop W
    · have hW' : W = op (⊤ : Opens (TopCat.of PUnit)) := by
        simpa using congrArg op (pointOpen_eq_top hW)
      subst hW'
      have hV : PUnit.unit ∈ unop V := j.unop.le hW
      have hV' : V = op (⊤ : Opens (TopCat.of PUnit)) := by
        simpa using congrArg op (pointOpen_eq_top hV)
      subst hV'
      have hU : PUnit.unit ∈ unop U := i.unop.le hV
      have hU' : U = op (⊤ : Opens (TopCat.of PUnit)) := by
        simpa using congrArg op (pointOpen_eq_top hU)
      subst hU'
      -- The only nonterminal branch is the explicit top/top/top compatibility.
      simpa using pointModulePresheafMap_comp_op_top x M i j
    · have hW' : W = op (⊥ : Opens (TopCat.of PUnit)) := by
        simpa using congrArg op (pointOpen_eq_bot hW)
      subst hW'
      -- Every map into the bottom-open value is unique because that value is terminal.
      exact (pointModulePresheaf_restrictScalars_obj_op_bot_isTerminal x M (i ≫ j)).hom_ext _ _

/-- Helper for Definition 6.27.1: the underlying abelian group of `pointModulePresheaf x M`
on the bottom open is terminal. -/
private noncomputable def pointModulePresheaf_presheaf_obj_bot_isTerminal
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    IsTerminal (((pointModulePresheaf x M).presheaf).obj (op (⊥ : Opens (TopCat.of PUnit)))) :=
  by
    let F :
        ModuleCat.{u} ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit)))) ⥤ Ab :=
      forget₂ _ Ab
    let _ :
        PreservesLimit
          (Functor.empty.{0}
            (ModuleCat.{u} ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit))))))
          F :=
      CategoryTheory.Functor.preservesTerminalObject_of_preservesZeroMorphisms F
    let T :=
      F.obj (⊤_ ModuleCat.{u}
        ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit)))))
    have hT : IsTerminal T := by
      -- Forgetting the terminal module yields a terminal abelian group.
      simpa [T] using
        (IsTerminal.ofIso
        (terminalIsTerminal : IsTerminal (⊤_ Ab))
        (PreservesTerminal.iso F).symm)
    have hobj :
        ((pointModulePresheaf x M).presheaf).obj (op (⊥ : Opens (TopCat.of PUnit))) = T := by
      have hobjMod :
          pointModulePresheafObj x M (op (⊥ : Opens (TopCat.of PUnit))) =
            (⊤_ ModuleCat.{u}
              ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit))))) := by
        -- The bottom-open value has already been normalized to the terminal module.
        simpa using pointModulePresheafObj_op_bot x M
      change AddCommGrpCat.of ↑(pointModulePresheafObj x M (op (⊥ : Opens (TopCat.of PUnit)))) = T
      rw [hobjMod]
      simp [T, F]
    -- Transport terminality across the explicit identification of the bottom-open value.
    exact IsTerminal.ofIso hT (eqToIso hobj).symm

noncomputable def pointModuleSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} (RingedSpace.ringCatSheaf (pointRingedSpace x)) where
  val := pointModulePresheaf x M
  isSheaf := by
    -- On the one-point space, sheafiness reduces to terminality on the empty open.
    exact TopCat.Presheaf.isSheaf_on_punit_of_isTerminal _
      (pointModulePresheaf_presheaf_obj_bot_isTerminal x M)

/-- Helper for Definition 6.27.1: the module sheaf value on the top open is the restricted stalk
module. -/
private theorem pointModuleSheaf_obj_op_top
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (pointModuleSheaf x M).val.obj (op (⊤ : Opens (TopCat.of PUnit))) =
      (ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M := by
  -- The sheaf has the point-module presheaf as underlying presheaf.
  simpa [pointModuleSheaf, pointModulePresheaf] using pointModulePresheafObj_op_top x M

/-- Helper for Definition 6.27.1: the module sheaf value on the bottom open is terminal. -/
private theorem pointModuleSheaf_obj_op_bot
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (pointModuleSheaf x M).val.obj (op (⊥ : Opens (TopCat.of PUnit))) =
      ⊤_ ModuleCat.{u} ((pointRingCatSheaf x).obj.obj (op (⊥ : Opens (TopCat.of PUnit)))) := by
  -- The bottom-open value is inherited unchanged from the presheaf normalization.
  simpa [pointModuleSheaf, pointModulePresheaf] using pointModulePresheafObj_op_bot x M

/-- The value of `pointModuleSheaf x M` on the top open is the module `M`, viewed through the
canonical identification of the top ring of `({x}, \mathcal O_{X, x})` with `\mathcal O_{X, x}`.
-/
noncomputable def pointModuleSheaf_objTopIso
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (pointModuleSheaf x M).val.obj (op (⊤ : Opens (TopCat.of PUnit))) ≅
      (ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M := by
  refine eqToIso ?_
  -- On `⊤`, the defining branch of `pointModulePresheafObj` is exactly the restricted module `M`.
  simp [pointModuleSheaf, pointModulePresheaf, pointModulePresheafObj]

/-
On the one-point ringed space `({x}, \mathcal O_{X, x})`, a morphism into the point module sheaf
`pointModuleSheaf x M` is determined by its component on the top open.
-/
/-- Helper for Definition 6.27.1: reconstruct a candidate morphism into `pointModuleSheaf x M`
from its prescribed component on the top open, using the zero map on the bottom open. -/
public noncomputable def pointModuleSheafHomReconstructApp
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (φ : G.val.obj (op (⊤ : Opens (TopCat.of PUnit))) ⟶ (pointModuleSheaf x M).val.obj (op ⊤)) :
    ∀ U : (Opens (TopCat.of PUnit))ᵒᵖ, G.val.obj U ⟶ (pointModuleSheaf x M).val.obj U
  | U => by
      by_cases hU : PUnit.unit ∈ unop U
      · have hU' : U = op ⊤ := by
          simpa using congrArg op (pointOpen_eq_top hU)
        subst hU'
        exact φ
      · exact 0

/-- Helper for Definition 6.27.1: the reconstructed component family is exactly `φ` on the top
open and exactly `0` on the bottom open. -/
private theorem pointModuleSheaf_hom_reconstruct_app_cases
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (φ : G.val.obj (op (⊤ : Opens (TopCat.of PUnit))) ⟶ (pointModuleSheaf x M).val.obj (op ⊤)) :
    pointModuleSheafHomReconstructApp x G M φ (op (⊤ : Opens (TopCat.of PUnit))) = φ ∧
      pointModuleSheafHomReconstructApp x G M φ (op (⊥ : Opens (TopCat.of PUnit))) = 0 := by
  constructor
  · -- The nonempty open lands in the prescribed top component.
    simp [pointModuleSheafHomReconstructApp]
  · -- The empty open lands in the zero component.
    dsimp [pointModuleSheafHomReconstructApp]
    split_ifs with hbot
    · exact (by simpa using hbot : False).elim
    · rfl

/-- Helper for Definition 6.27.1: on the top open, the reconstructed morphism satisfies the
expected naturality relation because both restriction maps are the identity restriction-of-scalars
isomorphism. -/
public theorem pointModuleSheaf_hom_reconstruct_naturality_op_top
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    (φ : G.val.obj (op (⊤ : Opens (TopCat.of PUnit))) ⟶ (pointModuleSheaf x M).val.obj (op ⊤))
    (f : op (⊤ : Opens (TopCat.of PUnit)) ⟶ op ⊤) :
    G.val.map f ≫
        (ModuleCat.restrictScalars ((pointRingCatSheaf x).obj.map f).hom).map φ =
      φ ≫ pointModulePresheafMap x M f := by
  -- On the top open there is only the identity map, so naturality reduces to the standard
  -- restriction-of-scalars identity naturality.
  have hf : f = 𝟙 (op (⊤ : Opens (TopCat.of PUnit))) := Subsingleton.elim _ _
  subst hf
  have hmap :
      RingCat.Hom.hom
          ((pointRingCatSheaf x).obj.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit))))) =
        RingHom.id ↑((pointRingCatSheaf x).obj.obj (op (⊤ : Opens (TopCat.of PUnit)))) := by
    change
      RingCat.Hom.hom ((pointRingCatSheaf x).obj.map (𝟙 (op ⊤))) =
        RingCat.Hom.hom (𝟙 ((pointRingCatSheaf x).obj.obj (op ⊤)))
    simpa using
      congrArg RingCat.Hom.hom ((pointRingCatSheaf x).obj.map_id (op (⊤ : Opens (TopCat.of PUnit))))
  have hG :
      G.val.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit)))) =
        (ModuleCat.restrictScalarsId'App
          (RingCat.Hom.hom
            ((pointRingCatSheaf x).obj.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit))))))
          hmap
          (G.val.obj (op (⊤ : Opens (TopCat.of PUnit))))).inv := by
    convert (G.val.map_id (op (⊤ : Opens (TopCat.of PUnit)))) using 1
  have hM :
      pointModulePresheafMap x M (𝟙 (op (⊤ : Opens (TopCat.of PUnit)))) =
        (ModuleCat.restrictScalarsId'App
          (RingCat.Hom.hom
            ((pointRingCatSheaf x).obj.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit))))))
          hmap
          (pointModulePresheafObj x M (op (⊤ : Opens (TopCat.of PUnit))))).inv := by
    simpa [hmap] using
      (pointModulePresheafMap_op_top x M (𝟙 (op (⊤ : Opens (TopCat.of PUnit)))))
  rw [hG, hM]
  exact
    (ModuleCat.restrictScalarsId'App_inv_naturality
      (RingCat.Hom.hom
        ((pointRingCatSheaf x).obj.map (𝟙 (op (⊤ : Opens (TopCat.of PUnit))))))
      hmap
      φ).symm

/-- Helper for Definition 6.27.1: a morphism into `pointModuleSheaf x M` is determined by its
component on the top open, because the bottom-open value is terminal. -/
private theorem pointModuleSheaf_hom_ext_top
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
    {f g : G ⟶ pointModuleSheaf x M}
    (h_top : f.val.app (op (⊤ : Opens (TopCat.of PUnit))) =
      g.val.app (op (⊤ : Opens (TopCat.of PUnit)))) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  by_cases hU : PUnit.unit ∈ unop U
  · have hU' : U = op (⊤ : Opens (TopCat.of PUnit)) := by
      simpa using congrArg op (pointOpen_eq_top hU)
    subst hU'
    simpa using h_top
  · have hU' : U = op (⊥ : Opens (TopCat.of PUnit)) := by
      simpa using congrArg op (pointOpen_eq_bot hU)
    subst hU'
    have hterminal : IsTerminal ((pointModuleSheaf x M).val.obj (op (⊥ : Opens (TopCat.of PUnit)))) := by
      rw [pointModuleSheaf_obj_op_bot x M]
      exact terminalIsTerminal
    exact hterminal.hom_ext _ _

noncomputable def pointModuleSheaf_homEquivTop
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    (G ⟶ pointModuleSheaf x M) ≃
      (G.val.obj (op (⊤ : Opens (TopCat.of PUnit))) ⟶ (pointModuleSheaf x M).val.obj (op ⊤)) where
  toFun f := f.val.app (op ⊤)
  invFun φ :=
    { val :=
        { app := pointModuleSheafHomReconstructApp x G M φ
          naturality := by
            intro U V f
            -- Normalize the codomain open: the bottom-open target is terminal, and the top-open
            -- target is the unique nontrivial naturality check on the one-point space.
            by_cases hV : PUnit.unit ∈ unop V
            · have hV' : V = op (⊤ : Opens (TopCat.of PUnit)) := by
                simpa using congrArg op (pointOpen_eq_top hV)
              subst hV'
              have hU : PUnit.unit ∈ unop U := f.unop.le hV
              have hU' : U = op (⊤ : Opens (TopCat.of PUnit)) := by
                simpa using congrArg op (pointOpen_eq_top hU)
              subst hU'
              -- The top branch is exactly the packaged identity restriction-of-scalars naturality.
              simpa [pointModuleSheaf, pointModulePresheaf,
                (pointModuleSheaf_hom_reconstruct_app_cases x G M φ).1] using
                pointModuleSheaf_hom_reconstruct_naturality_op_top x G M φ f
            · have hV' : V = op (⊥ : Opens (TopCat.of PUnit)) := by
                simpa using congrArg op (pointOpen_eq_bot hV)
              subst hV'
              -- The bottom-open codomain is terminal, so the two candidate maps are equal.
              let hterminal :
                  IsTerminal
                    ((ModuleCat.restrictScalars (RingCat.Hom.hom ((pointRingCatSheaf x).obj.map f))).obj
                      ((pointModuleSheaf x M).val.obj (op (⊥ : Opens (TopCat.of PUnit))))) := by
                simpa [pointModuleSheaf, pointModulePresheaf] using
                  (pointModulePresheaf_restrictScalars_obj_op_bot_isTerminal x M f)
              exact hterminal.hom_ext _ _ } }
  left_inv f := by
    -- Extensionality on opens reduces the inverse law to agreement on the top component.
    apply pointModuleSheaf_hom_ext_top x G M
    -- The reconstructed morphism was defined to recover exactly the chosen top component.
    simpa using (pointModuleSheaf_hom_reconstruct_app_cases x G M (f.val.app (op ⊤))).1
  right_inv φ := by
    -- Evaluating the reconstructed morphism on the top open returns the chosen top component.
    simpa using (pointModuleSheaf_hom_reconstruct_app_cases x G M φ).1

/-- Definition 6.27.1 (2): for a point `x : X` and an `\mathcal O_{X, x}`-module `M`,
`skyscraperModuleSheaf x M` is the canonical pushforward `i_{x, *} M` along the inclusion
`i_x : ({x}, \mathcal O_{X, x}) \to (X, \mathcal O_X)`. -/
noncomputable def skyscraperModuleSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    SheafOfModules.{u} ((RingedSpace.ringCatSheaf X)) :=
  ((pointInclusion x) _*).obj (pointModuleSheaf x M)

/-- Definition 6.27.1 (3): an `\mathcal O_X`-module sheaf is a skyscraper module sheaf if it is
isomorphic to `i_{x, *} M` for some point `x : X` and some `\mathcal O_{X, x}`-module `M`. -/
def IsSkyscraperModuleSheaf
    (ℱ : SheafOfModules.{u} ((RingedSpace.ringCatSheaf X))) : Prop :=
  ∃ (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))),
    IsIsomorphic ℱ (skyscraperModuleSheaf x M)

/-- The canonical skyscraper module sheaf `i_{x, *} M` is a skyscraper module sheaf. -/
theorem isSkyscraperModuleSheaf_skyscraperModuleSheaf
    (x : X) (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x))) :
    IsSkyscraperModuleSheaf (skyscraperModuleSheaf x M) :=
  ⟨x, M, ⟨Iso.refl _⟩⟩

end

end AlgebraicGeometry
