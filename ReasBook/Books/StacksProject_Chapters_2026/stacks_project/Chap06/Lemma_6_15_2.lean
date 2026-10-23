module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.Algebra.Category.MonCat.Colimits
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import stacks_project.Chap06.Definition_6_15_1
public import stacks_project.Chap06.LieAlgebraCat

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

private abbrev pointedBase : Type u := ULift.{u} PUnit

private noncomputable def pointedEquivUnder : Pointed.{u} ≌ Under (pointedBase.{u}) where
  functor :=
    { obj := fun X ↦ Under.mk (fun _ : pointedBase ↦ X.point)
      map := fun {X Y} f ↦ Under.homMk f.toFun (by
        funext x
        exact f.map_point) }
  inverse :=
    { obj := fun X ↦ Pointed.of (X.hom (ULift.up PUnit.unit))
      map := fun {X Y} f ↦ ⟨f.right, by
        simpa using congr_fun (Under.w f) (ULift.up PUnit.unit)⟩ }
  unitIso := NatIso.ofComponents (fun X ↦ Pointed.Iso.mk (Equiv.refl _) rfl)
  counitIso := NatIso.ofComponents (fun X ↦ Under.isoMk (Iso.refl _))

/-- The category of pointed sets has all limits. -/
instance : HasLimits Pointed :=
  Adjunction.has_limits_of_equivalence pointedEquivUnder.functor

/-- The forgetful functor from pointed sets to types preserves limits. -/
instance : PreservesLimits (forget Pointed) :=
  typeToPointedForgetAdjunction.rightAdjoint_preservesLimits

/-- The category of pointed sets has all colimits. -/
instance : HasColimits Pointed :=
  HasColimitsOfSize.mk (C := Pointed) fun J [Category J] ↦ by
    letI : HasColimits (Under pointedBase) := inferInstance
    letI : HasColimitsOfShape J (Under pointedBase) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence pointedEquivUnder.functor

/-- The category of pointed sets has filtered colimits. -/
instance : HasFilteredColimits Pointed := by
  let h : HasColimits (Under pointedBase) := inferInstance
  letI : HasFilteredColimits (Under pointedBase) :=
    { HasColimitsOfShape := fun J _ _ ↦ h.has_colimits_of_shape J }
  exact ⟨fun J _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence pointedEquivUnder.functor⟩

/-- The forgetful functor from pointed sets to types preserves filtered colimits. -/
instance : PreservesFilteredColimits (forget Pointed) where
  preserves_filtered_colimits J _ _ := by
    change PreservesColimitsOfShape J (pointedEquivUnder.functor ⋙ Under.forget pointedBase)
    letI : PreservesColimitsOfShape J pointedEquivUnder.functor := inferInstance
    letI : PreservesColimitsOfShape J (Under.forget pointedBase) := inferInstance
    infer_instance

private theorem pointed_isIso_of_bijective {X Y : Pointed} (f : X ⟶ Y)
    (hf : Function.Bijective f) : IsIso f := by
  simpa using
    (Pointed.Iso.mk (Equiv.ofBijective f hf) (by simpa using f.map_point)).isIso_hom

/-- The forgetful functor from pointed sets to types reflects isomorphisms. -/
instance : (forget Pointed).ReflectsIsomorphisms where
  reflects f :=
    pointed_isIso_of_bijective f <|
      (CategoryTheory.isIso_iff_bijective ((forget Pointed).map f)).mp inferInstance

/-- The category of groups has filtered colimits. -/
instance : HasFilteredColimits GrpCat where
  HasColimitsOfShape _ _ _ :=
    ⟨fun F ↦ ⟨GrpCat.FilteredColimits.colimitCocone F,
      GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩

-- Proof sketch: limits of Lie algebras are constructed on the corresponding limits of the
-- underlying vector spaces, with bracket defined pointwise.

/-- Lemma 6.15.2 (1): the category of pointed sets, with its forgetful functor to sets, defines a
type of algebraic structures. -/
instance pointed_sets_algebraic_structure_type :
    IsAlgebraicStructure Pointed (forget Pointed) :=
  inferInstance

/-- Lemma 6.15.2 (2): the category of abelian groups, with its forgetful functor to sets, defines
a type of algebraic structures. -/
instance abelian_groups_algebraic_structure_type :
    IsAlgebraicStructure AddCommGrpCat (forget AddCommGrpCat) :=
  inferInstance

/-- Lemma 6.15.2 (3): the category of groups, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance groups_algebraic_structure_type :
    IsAlgebraicStructure GrpCat (forget GrpCat) :=
  inferInstance

/-- Lemma 6.15.2 (4): the category of monoids, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance monoids_algebraic_structure_type :
    IsAlgebraicStructure MonCat (forget MonCat) := by
  letI : HasLimits MonCat := inferInstance
  letI : PreservesLimits (forget MonCat) := inferInstance
  let h : HasColimits MonCat := inferInstance
  letI : HasFilteredColimits MonCat :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget MonCat) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget MonCat).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (5): the category of rings, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance rings_algebraic_structure_type :
    IsAlgebraicStructure RingCat (forget RingCat) := by
  letI : HasLimits RingCat := inferInstance
  letI : PreservesLimits (forget RingCat) := inferInstance
  let h : HasColimits RingCat := inferInstance
  letI : HasFilteredColimits RingCat :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget RingCat) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget RingCat).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (6): for a fixed ring `R`, the category of `R`-modules with its forgetful functor
to sets defines a type of algebraic structures. -/
instance modules_algebraic_structure_type (R : Type u) [Ring R] :
    IsAlgebraicStructure (ModuleCat.{u} R) (forget (ModuleCat.{u} R)) := by
  letI : HasLimits (ModuleCat.{u} R) := inferInstance
  letI : PreservesLimits (forget (ModuleCat.{u} R)) := inferInstance
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} R) := inferInstance
  letI : HasFilteredColimits (ModuleCat.{u} R) :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget (ModuleCat.{u} R)).ReflectsIsomorphisms := inferInstance
  infer_instance

namespace LieAlgebraCat

section Limits

variable {R : Type u} [CommRing R]

namespace Shrink

variable {L : Type v} [LieRing L] [LieAlgebra R L] [Small.{u} L]

/-- Helper for Lemma 6.15.2: the bracket on a shrunk Lie algebra is transported along
`equivShrink`. -/
instance instBracket : Bracket (Shrink.{u} L) (Shrink.{u} L) where
  bracket x y := equivShrink L ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆

/-- Helper for Lemma 6.15.2: unshrinking a transported bracket recovers the original bracket. -/
@[simp] theorem equivShrink_symm_lie (x y : Shrink.{u} L) :
    (equivShrink L).symm ⁅x, y⁆ = ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆ :=
  by
    change
      (equivShrink L).symm ((equivShrink L) ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆) =
        ⁅(equivShrink L).symm x, (equivShrink L).symm y⁆
    simp

/-- Helper for Lemma 6.15.2: shrinking preserves the Lie bracket. -/
@[simp] theorem equivShrink_lie (x y : L) :
    equivShrink L ⁅x, y⁆ = ⁅equivShrink L x, equivShrink L y⁆ := by
  change equivShrink L ⁅x, y⁆ =
    equivShrink L ⁅(equivShrink L).symm (equivShrink L x), (equivShrink L).symm (equivShrink L y)⁆
  simp

/-- Helper for Lemma 6.15.2: shrinking a small Lie algebra preserves its Lie ring structure. -/
instance instLieRing : LieRing (Shrink.{u} L) := by
  -- Transport each Lie-ring axiom along `equivShrink.symm`.
  refine
    { add_lie := ?_
      lie_add := ?_
      lie_self := ?_
      leibniz_lie := ?_ }
  · intro x y z
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie, equivShrink_symm_add] using
        (add_lie ((equivShrink L).symm x) ((equivShrink L).symm y) ((equivShrink L).symm z))
  · intro x y z
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie, equivShrink_symm_add] using
        (lie_add ((equivShrink L).symm x) ((equivShrink L).symm y) ((equivShrink L).symm z))
  · intro x
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie] using lie_self ((equivShrink L).symm x)
  · intro x y z
    exact (equivShrink L).symm.injective <| by
      simpa [equivShrink_symm_lie, equivShrink_symm_add] using
        (leibniz_lie ((equivShrink L).symm x) ((equivShrink L).symm y) ((equivShrink L).symm z))

/-- Helper for Lemma 6.15.2: shrinking a small Lie algebra preserves its scalar-compatible
Lie bracket. -/
instance instLieAlgebra : LieAlgebra R (Shrink.{u} L) := by
  -- Transport scalar compatibility of the bracket through `equivShrink.symm`.
  refine
    { lie_smul := ?_ }
  intro t x y
  exact (equivShrink L).symm.injective <| by
    simpa [equivShrink_symm_lie, equivShrink_symm_smul] using
      (LieAlgebra.lie_smul t ((equivShrink L).symm x) ((equivShrink L).symm y))

/-- Helper for Lemma 6.15.2: the shrink equivalence upgrades to a Lie algebra equivalence. -/
def lieEquiv : Shrink.{u} L ≃ₗ⁅R⁆ L := by
  -- Package the transported linear equivalence together with bracket preservation.
  exact
    { Shrink.linearEquiv R L with
      map_lie' := fun {x y} ↦ equivShrink_symm_lie x y }

end Shrink

namespace HasLimits

variable {J : Type u} [Category J] (F : J ⥤ LieAlgebraCat.{u} R)

/-- Helper for Lemma 6.15.2: the pointwise product of the diagram carries the induced Lie ring
structure. -/
instance piLieRing : LieRing (∀ j, F.obj j) where
  bracket x y j := ⁅x j, y j⁆
  add_lie x y z := by
    funext j
    exact add_lie (x j) (y j) (z j)
  lie_add x y z := by
    funext j
    exact lie_add (x j) (y j) (z j)
  lie_self x := by
    funext j
    exact lie_self (x j)
  leibniz_lie x y z := by
    funext j
    exact leibniz_lie (x j) (y j) (z j)

/-- Helper for Lemma 6.15.2: the pointwise product of the diagram carries the induced Lie algebra
structure. -/
instance piLieAlgebra : LieAlgebra R (∀ j, F.obj j) where
  lie_smul t x y := by
    funext j
    exact lie_smul t (x j) (y j)

/-- Helper for Lemma 6.15.2: the compatible families in a Lie algebra diagram should form the
source-faithful limit Lie subalgebra of the pointwise product. -/
def sectionsLieSubalgebra : LieSubalgebra R (∀ j, F.obj j) :=
  { ModuleCat.sectionsSubmodule (R := R)
      (F := F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) with
    lie_mem' := by
      intro x y hx hy
      intro j j' f
      -- Compatible sections remain compatible after taking the pointwise bracket.
      change F.map f ⁅x j, y j⁆ = ⁅x j', y j'⁆
      rw [← hx f, ← hy f]
      exact (F.map f).map_lie (x j) (y j) }

/-- Helper for Lemma 6.15.2: smallness of compatible families can be read from the type-theoretic
limit sections. -/
instance sectionsLieSubalgebra_small [Small.{u} (sectionsLieSubalgebra F)] :
    Small.{u} ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| Small.{u} (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the additive structure carried by
the Lie-subalgebra of compatible families. -/
instance sectionsAddCommMonoid : AddCommMonoid ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| AddCommMonoid (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the module structure carried by
the Lie-subalgebra of compatible families. -/
instance sectionsModule : Module R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| Module R (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the Lie-ring structure carried by
the Lie-subalgebra of compatible families. -/
instance sectionsLieRing : LieRing ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| LieRing (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: the raw compatible sections inherit the Lie-algebra structure carried
by the Lie-subalgebra of compatible families. -/
instance sectionsLieAlgebra : LieAlgebra R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections) :=
  inferInstanceAs <| LieAlgebra R (sectionsLieSubalgebra F)

/-- Helper for Lemma 6.15.2: shrinking the compatible-sections Lie subalgebra should induce the
Lie ring structure on the underlying type-theoretic limit. -/
instance limitLieRing [Small.{u} (sectionsLieSubalgebra F)] :
    LieRing (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
  inferInstanceAs <| LieRing (Shrink.{u} (sectionsLieSubalgebra F))

/-- Helper for Lemma 6.15.2: shrinking the compatible-sections Lie subalgebra should induce the
Lie algebra structure on the underlying type-theoretic limit. -/
instance limitLieAlgebra [Small.{u} (sectionsLieSubalgebra F)] :
    LieAlgebra R (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
  inferInstanceAs <| LieAlgebra R (Shrink.{u} (sectionsLieSubalgebra F))

set_option synthInstance.maxHeartbeats 200000 in
/-- Helper for Lemma 6.15.2: the underlying module projection from the explicit Lie limit. -/
def limitπLinearMap [Small.{u} (sectionsLieSubalgebra F)] (j : J) :
    (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt →ₗ[R]
      ((F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).obj j) := by
  -- Route correction: define the projection directly on the type-valued limit carrier, rather
  -- than first comparing carriers with the module limit.
  refine
    { toFun := (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).π.app j
      map_smul' := ?_
      map_add' := ?_ }
  · intro x y
    -- Addition is handled by the same pointwise evaluation argument.
    simpa [Shrink.linearEquiv_apply, Types.Small.limitCone_π_app] using
      congrArg (fun s : (F ⋙ forget (LieAlgebraCat.{u} R)).sections => s.1 j)
        ((Shrink.linearEquiv R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections)).map_add x y)
  · intro m x
    -- The projection is linear because evaluation of a compatible family commutes with scalars.
    simpa [Shrink.linearEquiv_apply, Types.Small.limitCone_π_app] using
      congrArg (fun s : (F ⋙ forget (LieAlgebraCat.{u} R)).sections => s.1 j)
        ((Shrink.linearEquiv R ((F ⋙ forget (LieAlgebraCat.{u} R)).sections)).map_smul m x)

/-- Helper for Lemma 6.15.2: the projections from the compatible-sections limit should be Lie
algebra morphisms. -/
def limitπLieHom [Small.{u} (sectionsLieSubalgebra F)] (j : J) :
    (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt →ₗ⁅R⁆ F.obj j := by
  -- Once the projection is explicit, bracket preservation is pointwise.
  exact
    { limitπLinearMap F j with
      map_lie' := by
        intro x y
        simpa [limitπLinearMap, Types.Small.limitCone_π_app, LieHom.coe_mk, LinearMap.coe_mk,
          LieAlgebraCat.Shrink.lieEquiv] using
          congrArg (fun s : (F ⋙ forget (LieAlgebraCat.{u} R)).sections => s.1 j)
            ((LieAlgebraCat.Shrink.lieEquiv
              (R := R) (L := (F ⋙ forget (LieAlgebraCat.{u} R)).sections)).map_lie x y) }

/-- Helper for Lemma 6.15.2: the explicit cone of compatible families in `LieAlgebraCat`. -/
def limitCone [Small.{u} (sectionsLieSubalgebra F)] : Cone F := by
  -- Package the pointwise projections into the candidate Lie-algebra limit cone.
  refine
    { pt := LieAlgebraCat.of R ((Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt)
      π :=
        { app := fun j ↦ limitπLieHom F j
          naturality := ?_ } }
  intro j j' f
  apply LieAlgebraCat.hom_ext
  intro x
  exact congr_fun ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) x

/-- Helper for Lemma 6.15.2: the compatible-sections cone should satisfy the universal property of
the limit in `LieAlgebraCat`. -/
def limitConeIsLimit [Small.{u} (sectionsLieSubalgebra F)] :
    IsLimit (limitCone F) := by
  -- Route correction: inherit the linear universal property from the module-valued limit cone,
  -- and only prove bracket preservation pointwise on the compatible-family projections.
  let hModule :
      IsLimit ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCone (limitCone F)) := by
    simpa [limitCone, limitπLieHom, limitπLinearMap] using
      (ModuleCat.HasLimits.limitConeIsLimit
        (F := F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)))
  refine IsLimit.ofFaithful (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) hModule
    (fun s ↦
      show s.pt →ₗ⁅R⁆ LieAlgebraCat.of R ((Types.Small.limitCone (F ⋙ forget _)).pt) from
        { toLinearMap := (hModule.lift ((forget₂ _ _).mapCone s)).hom
          map_lie' := ?_ })
    (fun _ ↦ rfl)
  intro x y
  let liftLinear : s.pt →ₗ[R] (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
    (hModule.lift ((forget₂ _ _).mapCone s)).hom
  let xy : s.pt := ⁅x, y⁆
  let liftxy : (Types.Small.limitCone (F ⋙ forget (LieAlgebraCat.{u} R))).pt :=
    ⁅liftLinear x, liftLinear y⁆
  -- Compare the two candidate brackets after projecting to every component of the section.
  apply Types.Small.limitCone_pt_ext
  ext j
  change
    (limitπLieHom F j) (liftLinear xy) =
      (limitπLieHom F j) liftxy
  have hfac_lie :
      (limitπLieHom F j) (liftLinear xy) = (s.π.app j) xy := by
    simpa [limitπLieHom, limitπLinearMap] using
      (ConcreteCategory.congr_hom (hModule.fac ((forget₂ _ _).mapCone s) j)) xy
  have hfac_x : (limitπLieHom F j) (liftLinear x) = (s.π.app j) x := by
    simpa [limitπLieHom, limitπLinearMap] using
      (ConcreteCategory.congr_hom (hModule.fac ((forget₂ _ _).mapCone s) j)) x
  have hfac_y : (limitπLieHom F j) (liftLinear y) = (s.π.app j) y := by
    simpa [limitπLieHom, limitπLinearMap] using
      (ConcreteCategory.congr_hom (hModule.fac ((forget₂ _ _).mapCone s) j)) y
  calc
    (limitπLieHom F j) (liftLinear xy) = (s.π.app j) xy := hfac_lie
    _ = ⁅(s.π.app j) x, (s.π.app j) y⁆ := by
      simpa [xy] using LieHom.map_lie (s.π.app j) x y
    _ = ⁅(limitπLieHom F j) (liftLinear x), (limitπLieHom F j) (liftLinear y)⁆ := by
      rw [hfac_x, hfac_y]
    _ = (limitπLieHom F j) liftxy := by
      symm
      simpa [liftxy] using LieHom.map_lie (limitπLieHom F j) (liftLinear x) (liftLinear y)

/-- Helper for Lemma 6.15.2: a small compatible-sections Lie algebra diagram has a limit. -/
instance hasLimit [Small.{u} (sectionsLieSubalgebra F)] : HasLimit F :=
  HasLimit.mk
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

/-- Helper for Lemma 6.15.2: small indexing categories admit explicit limits in
`LieAlgebraCat`. -/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (LieAlgebraCat.{u} R) where
  has_limit _ := inferInstance

/-- Helper for Lemma 6.15.2: forgetting `LieAlgebraCat` to `ModuleCat` preserves the explicit
compatible-sections limit cone. -/
noncomputable instance forget₂Module_preservesLimit [Small.{u} (sectionsLieSubalgebra F)] :
    PreservesLimit F (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) :=
  preservesLimit_of_preserves_limit_cone (limitConeIsLimit F) <| by
    -- The mapped Lie limit cone is definitionally the module limit cone on the underlying
    -- module-valued diagram.
    simpa [limitCone, limitπLieHom, limitπLinearMap] using
      (ModuleCat.HasLimits.limitConeIsLimit
        (F := F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)))

/-- Helper for Lemma 6.15.2: forgetting to types preserves the explicit compatible-sections
limits. -/
noncomputable instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget (LieAlgebraCat.{u} R)) where
  preservesLimit := fun {K} ↦
    preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
      (Types.Small.limitConeIsLimit (K ⋙ forget (LieAlgebraCat.{u} R)))

end HasLimits

/-- Helper for Lemma 6.15.2: forgetting `LieAlgebraCat` to `ModuleCat` preserves the explicit
compatible-sections limits. -/
theorem forget₂Module_preservesLimits_aux (R : Type u) [CommRing R] :
    PreservesLimits (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) := by
  -- Assemble the shape-wise preservation result from the explicit cone comparison above.
  refine
    { preservesLimitsOfShape := fun {J} _ ↦
        { preservesLimit := fun {F} ↦ by infer_instance } }

/-- Helper for Lemma 6.15.2: the remaining limit-side step is to equip the compatible families in
the underlying module limit with the pointwise Lie bracket and prove the resulting cone is a limit.
-/
theorem hasLimits_aux (R : Type u) [CommRing R] : HasLimits (LieAlgebraCat.{u} R) := by
  -- The explicit compatible-sections limit exists for every small indexing category.
  refine
    { has_limits_of_shape := fun J _ ↦
        { has_limit := fun F ↦ by
            letI : Small.{u} J := by infer_instance
            infer_instance } }

/-- Helper for Lemma 6.15.2: once the compatible-sections limit cone is in place, forgetting to the
underlying module preserves limits by direct cone comparison. -/
theorem forget_preservesLimits_aux (R : Type u) [CommRing R] :
    PreservesLimits (forget (LieAlgebraCat.{u} R)) := by
  -- Each explicit Lie limit cone maps to the standard type-valued limit cone.
  refine
    { preservesLimitsOfShape := fun {J} _ ↦
        { preservesLimit := fun {F} ↦ by
            letI : Small.{u} J := by infer_instance
            infer_instance } }

instance hasLimits (R : Type u) [CommRing R] : HasLimits (LieAlgebraCat.{u} R) :=
  hasLimits_aux (R := R)

instance forget_preservesLimits (R : Type u) [CommRing R] :
    PreservesLimits (forget (LieAlgebraCat.{u} R)) :=
  forget_preservesLimits_aux (R := R)

end Limits

section ReflectsIso

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 6.15.2: a bijective Lie algebra morphism is an isomorphism, via the inverse
Lie equivalence on the underlying types. -/
theorem lie_isIso_of_bijective {L M : LieAlgebraCat.{u} R} (f : L ⟶ M)
    (hf : Function.Bijective f) : IsIso f := by
  -- A bijective Lie morphism upgrades to a Lie equivalence, and that equivalence supplies the
  -- inverse categorical morphism.
  let e : L ≃ₗ⁅R⁆ M := LieEquiv.ofBijective f hf
  let i : L ≅ M :=
    { hom := e.toLieHom
      inv := e.symm.toLieHom
      hom_inv_id := by
        ext x
        exact e.symm_apply_apply x
      inv_hom_id := by
        ext x
        exact e.apply_symm_apply x }
  have hhom : i.hom = f := by
    ext x
    rfl
  simpa [hhom] using i.isIso_hom

instance forget_reflectsIsomorphisms (R : Type u) [CommRing R] :
    (forget (LieAlgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects f :=
    lie_isIso_of_bijective (R := R) f <|
      (CategoryTheory.isIso_iff_bijective ((forget (LieAlgebraCat.{u} R)).map f)).mp inferInstance

end ReflectsIso

section FilteredColimits

variable {R : Type u} [CommRing R]

namespace FilteredColimits

open CategoryTheory.IsFiltered renaming max → max'

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ LieAlgebraCat.{u} R)

/-- Helper for Lemma 6.15.2: the filtered diagram of underlying modules attached to a Lie-algebra
diagram. -/
abbrev underlyingModuleDiagram : J ⥤ ModuleCat.{u} R :=
  F ⋙ forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)

/-- Helper for Lemma 6.15.2: the representative-level Lie bracket on the underlying module
filtered colimit. -/
noncomputable def colimitLieAux (x y : Σ j, F.obj j) :
    ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F) :=
  ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
    ⟨max' x.1 y.1, (⁅(F.map (IsFiltered.leftToMax x.1 y.1) x.2 : F.obj (max' x.1 y.1)),
      (F.map (IsFiltered.rightToMax x.1 y.1) y.2 : F.obj (max' x.1 y.1))⁆ :
        F.obj (max' x.1 y.1))⟩

/-- Helper for Lemma 6.15.2: the representative-level Lie bracket is compatible with changing the
left representative in the filtered-colimit relation. -/
theorem colimitLieAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel
      ((underlyingModuleDiagram (R := R) F) ⋙ forget (ModuleCat.{u} R)) x x') :
    colimitLieAux (R := R) F x y = colimitLieAux (R := R) F x' y := by
  -- Compare the two source representatives after moving every bracket term to one common object.
  obtain ⟨j₁, x⟩ := x
  obtain ⟨j₂, y⟩ := y
  obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by
    simpa using hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply ModuleCat.FilteredColimits.M.mk_eq
  use s, α, γ
  dsimp [colimitLieAux, underlyingModuleDiagram]
  change (F.map α) ⁅(F.map (IsFiltered.leftToMax j₁ j₂)) x, (F.map (IsFiltered.rightToMax j₁ j₂)) y⁆ =
    (F.map γ) ⁅(F.map (IsFiltered.leftToMax j₃ j₂)) x', (F.map (IsFiltered.rightToMax j₃ j₂)) y⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp_rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

/-- Helper for Lemma 6.15.2: the representative-level Lie bracket is compatible with changing the
right representative in the filtered-colimit relation. -/
theorem colimitLieAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel
      ((underlyingModuleDiagram (R := R) F) ⋙ forget (ModuleCat.{u} R)) y y') :
    colimitLieAux (R := R) F x y = colimitLieAux (R := R) F x y' := by
  -- The right-variable compatibility is the symmetric tulip comparison.
  obtain ⟨j₁, y⟩ := y
  obtain ⟨j₂, x⟩ := x
  obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  replace hfg : F.map f y = F.map g y' := by
    simpa using hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply ModuleCat.FilteredColimits.M.mk_eq
  use s, α, γ
  dsimp [colimitLieAux, underlyingModuleDiagram]
  change (F.map α) ⁅(F.map (IsFiltered.leftToMax j₂ j₁)) x, (F.map (IsFiltered.rightToMax j₂ j₁)) y⁆ =
    (F.map γ) ⁅(F.map (IsFiltered.leftToMax j₂ j₃)) x, (F.map (IsFiltered.rightToMax j₂ j₃)) y'⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp_rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

/-- Helper for Lemma 6.15.2: the filtered colimit of the underlying module diagram carries the
descended Lie bracket. -/
noncomputable instance colimitBracket :
    Bracket (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F))
      (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F)) := by
  -- Descend the representative-level bracket through the quotient presentation of the colimit.
  refine ⟨fun x y ↦ ?_⟩
  refine Quot.lift₂ (colimitLieAux (R := R) F) ?_ ?_ x y
  · intro x y y' h
    apply colimitLieAux_eq_of_rel_right
    exact Types.FilteredColimit.rel_of_colimitTypeRel _ _ _ h
  · intro x x' y h
    apply colimitLieAux_eq_of_rel_left
    exact Types.FilteredColimit.rel_of_colimitTypeRel _ _ _ h

/-- Helper for Lemma 6.15.2: the descended bracket on generators can be computed after moving to
any chosen common upper bound. -/
theorem colimit_lie_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    ⁅ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) x,
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) y⁆ =
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
        ⟨k, (⁅(F.map f x.2 : F.obj k), (F.map g y.2 : F.obj k)⁆ : F.obj k)⟩ := by
  -- Rewrite the default `max'`-based bracket through an arbitrary common upper bound.
  obtain ⟨j₁, x⟩ := x
  obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  apply ModuleCat.FilteredColimits.M.mk_eq
  use s, α, β
  dsimp [colimitLieAux, underlyingModuleDiagram]
  change (F.map α) ⁅(F.map (IsFiltered.leftToMax j₁ j₂)) x, (F.map (IsFiltered.rightToMax j₁ j₂)) y⁆ =
    (F.map β) ⁅(F.map f) x, (F.map g) y⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp_rw [← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

/-- Helper for Lemma 6.15.2: the descended bracket on two generators from the same object is the
expected image of the original bracket. -/
lemma colimit_lie_mk_eq' {j : J} (x y : F.obj j) :
    ⁅ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, x⟩,
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, y⟩⁆ =
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, (⁅x, y⁆ : F.obj j)⟩ := by
  -- Specialize the common-upper-bound formula to the identity maps.
  simpa using colimit_lie_mk_eq (R := R) (F := F) ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

/-- Helper for Lemma 6.15.2: the filtered colimit of the underlying module diagram inherits the
Lie-ring structure of the source diagram. -/
noncomputable instance colimitLieRing :
    LieRing (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F)) := by
  refine
    { add_lie := ?_
      lie_add := ?_
      lie_self := ?_
      leibniz_lie := ?_ }
  · intro x y z
    -- Reduce to generators and move the three representatives to one common upper bound.
    obtain ⟨i, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    obtain ⟨k, z, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) z
    let m : J := IsFiltered.max₃ i j k
    let fi : i ⟶ m := IsFiltered.firstToMax₃ i j k
    let fj : j ⟶ m := IsFiltered.secondToMax₃ i j k
    let fk : k ⟶ m := IsFiltered.thirdToMax₃ i j k
    rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fi x,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fj y,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fk z,
      ModuleCat.FilteredColimits.colimit_add_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq',
      colimit_lie_mk_eq', ModuleCat.FilteredColimits.colimit_add_mk_eq']
    exact congrArg
      (fun w : F.obj m ↦
        ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨m, w⟩)
      (add_lie ((F.map fi x : F.obj m)) ((F.map fj y : F.obj m)) ((F.map fk z : F.obj m)))
  · intro x y z
    -- The right-additivity proof uses the same common-upper-bound normalization.
    obtain ⟨i, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    obtain ⟨k, z, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) z
    let m : J := IsFiltered.max₃ i j k
    let fi : i ⟶ m := IsFiltered.firstToMax₃ i j k
    let fj : j ⟶ m := IsFiltered.secondToMax₃ i j k
    let fk : k ⟶ m := IsFiltered.thirdToMax₃ i j k
    rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fi x,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fj y,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fk z,
      ModuleCat.FilteredColimits.colimit_add_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq',
      colimit_lie_mk_eq', ModuleCat.FilteredColimits.colimit_add_mk_eq']
    exact congrArg
      (fun w : F.obj m ↦
        ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨m, w⟩)
      (lie_add ((F.map fi x : F.obj m)) ((F.map fj y : F.obj m)) ((F.map fk z : F.obj m)))
  · intro x
    -- On a single generator, alternation reduces directly to the source Lie algebra.
    obtain ⟨j, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    rw [colimit_lie_mk_eq', lie_self]
    simpa using
      (ModuleCat.FilteredColimits.colimit_zero_eq (underlyingModuleDiagram (R := R) F) j).symm
  · intro x y z
    -- After moving to one object, the Leibniz identity is the source identity.
    obtain ⟨i, x, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    obtain ⟨k, z, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) z
    let m : J := IsFiltered.max₃ i j k
    let fi : i ⟶ m := IsFiltered.firstToMax₃ i j k
    let fj : j ⟶ m := IsFiltered.secondToMax₃ i j k
    let fk : k ⟶ m := IsFiltered.thirdToMax₃ i j k
    rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fi x,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fj y,
      ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) fk z,
      colimit_lie_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq', colimit_lie_mk_eq',
      colimit_lie_mk_eq', colimit_lie_mk_eq', ModuleCat.FilteredColimits.colimit_add_mk_eq']
    exact congrArg
      (fun w : F.obj m ↦
        ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨m, w⟩)
      (leibniz_lie ((F.map fi x : F.obj m)) ((F.map fj y : F.obj m)) ((F.map fk z : F.obj m)))

/-- Helper for Lemma 6.15.2: the descended bracket is compatible with the scalar action on the
filtered colimit module. -/
noncomputable instance colimitLieAlgebra :
    LieAlgebra R (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F)) := by
  refine
    { lie_smul := ?_ }
  intro r x y
  -- Move the two representatives to one object, then rewrite the scalar action and the bracket.
  obtain ⟨i, x, rfl⟩ :=
    ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
  obtain ⟨j, y, rfl⟩ :=
    ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
  let k : J := max' i j
  let f : i ⟶ k := IsFiltered.leftToMax i j
  let g : j ⟶ k := IsFiltered.rightToMax i j
  rw [← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) f x,
    ← ModuleCat.FilteredColimits.M.mk_map (underlyingModuleDiagram (R := R) F) g y,
    ModuleCat.FilteredColimits.colimit_smul_mk_eq, colimit_lie_mk_eq', colimit_lie_mk_eq',
    ModuleCat.FilteredColimits.colimit_smul_mk_eq]
  exact congrArg
    (fun w : F.obj k ↦
      ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨k, w⟩)
    (LieAlgebra.lie_smul r ((F.map f x : F.obj k)) ((F.map g y : F.obj k)))

/-- Helper for Lemma 6.15.2: the bundled Lie algebra realizing the filtered colimit of the
diagram. -/
noncomputable def colimit : LieAlgebraCat.{u} R :=
  LieAlgebraCat.of R (ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F))

/-- Helper for Lemma 6.15.2: each object of the diagram maps into the explicit filtered colimit by
the canonical generator map. -/
noncomputable def coconeMorphism (j : J) : F.obj j ⟶ colimit (R := R) F := by
  -- Reuse the module-level generator map and prove bracket preservation on same-object generators.
  exact
    { toLinearMap :=
        (ModuleCat.FilteredColimits.coconeMorphism (underlyingModuleDiagram (R := R) F) j).hom
      map_lie' := by
        intro x y
        symm
        simpa using colimit_lie_mk_eq' (R := R) (F := F) x y
    }

/-- Helper for Lemma 6.15.2: the underlying linear map of the Lie cocone morphism is exactly the
module filtered-colimit cocone map. -/
theorem coconeMorphism_underlying_eq (j : J) :
    (coconeMorphism (R := R) F j).toLinearMap =
      (ModuleCat.FilteredColimits.coconeMorphism (underlyingModuleDiagram (R := R) F) j).hom :=
  rfl

/-- Helper for Lemma 6.15.2: the explicit cocone over the filtered diagram of Lie algebras. -/
noncomputable def colimitCocone : Cocone F where
  pt := colimit (R := R) F
  ι :=
    { app := coconeMorphism (R := R) F
      naturality := by
        intro j j' f
        -- Naturality is inherited from the module cocone after forgetting the Lie bracket.
        apply LieAlgebraCat.hom_ext
        intro x
        simpa [coconeMorphism, colimit] using
          ConcreteCategory.congr_hom
            ((ModuleCat.FilteredColimits.colimitCocone
              (underlyingModuleDiagram (R := R) F)).ι.naturality f) x }

/-- Helper for Lemma 6.15.2: the universal Lie morphism from the explicit filtered colimit to any
other cocone point. -/
noncomputable def colimitDesc (t : Cocone F) : colimit (R := R) F ⟶ t.pt := by
  -- Reuse the module universal morphism and verify Lie compatibility on generators.
  let f :
      ModuleCat.FilteredColimits.colimit (underlyingModuleDiagram (R := R) F) ⟶
        ModuleCat.of R t.pt :=
    ModuleCat.FilteredColimits.colimitDesc (underlyingModuleDiagram (R := R) F)
      ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t)
  have hf {j : J} (x : F.obj j) :
      f (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, x⟩) = t.ι.app j x :=
    ConcreteCategory.congr_hom
      (ModuleCat.FilteredColimits.ι_colimitDesc (underlyingModuleDiagram (R := R) F)
        ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t) j) x
  exact
    { toLinearMap := f.hom
      map_lie' := by
        intro x y
        obtain ⟨i, x, rfl⟩ :=
          ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) x
        obtain ⟨j, y, rfl⟩ :=
          ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
        let xi : t.pt := t.ι.app i x
        let yj : t.pt := t.ι.app j y
        let xik : t.pt := t.ι.app (max' i j) (F.map (IsFiltered.leftToMax i j) x)
        let yjk : t.pt := t.ι.app (max' i j) (F.map (IsFiltered.rightToMax i j) y)
        -- Compute the bracket at the canonical common upper bound and then use the cocone laws.
        have hcolimit :
            f.hom
                ((⁅ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨i, x⟩,
                    ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, y⟩⁆) :
                  ModuleCat.FilteredColimits.M (underlyingModuleDiagram (R := R) F))
              =
              f.hom
                (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
                  ⟨max' i j,
                    (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                      (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                        F.obj (max' i j))⟩) := by
          exact congrArg f.hom
            (colimit_lie_mk_eq (R := R) (F := F) ⟨i, x⟩ ⟨j, y⟩ (max' i j)
              (IsFiltered.leftToMax i j) (IsFiltered.rightToMax i j))
        have hdesc :
            f.hom
                (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F)
                  ⟨max' i j,
                    (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                      (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                        F.obj (max' i j))⟩)
              =
              ((t.ι.app (max' i j)
                (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                  (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                    F.obj (max' i j))) : t.pt) := by
          simpa using hf (j := max' i j)
            ((⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
              (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆ :
                F.obj (max' i j)))
        have hmap :
            ((t.ι.app (max' i j))
              (⁅(F.map (IsFiltered.leftToMax i j) x : F.obj (max' i j)),
                (F.map (IsFiltered.rightToMax i j) y : F.obj (max' i j))⁆) : t.pt) =
              (⁅xik, yjk⁆ : t.pt) := by
          simpa using LieHom.map_lie (t.ι.app (max' i j))
            (F.map (IsFiltered.leftToMax i j) x)
            (F.map (IsFiltered.rightToMax i j) y)
        have hleft : xik = xi := by
          change t.ι.app (max' i j) (F.map (IsFiltered.leftToMax i j) x) = t.ι.app i x
          exact ConcreteCategory.congr_hom (t.w (IsFiltered.leftToMax i j)) x
        have hright : yjk = yj := by
          change t.ι.app (max' i j) (F.map (IsFiltered.rightToMax i j) y) = t.ι.app j y
          exact ConcreteCategory.congr_hom (t.w (IsFiltered.rightToMax i j)) y
        have hfx : (f.hom) (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨i, x⟩) = xi := by
          simpa [xi] using hf (j := i) x
        have hfy : (f.hom) (ModuleCat.FilteredColimits.M.mk (underlyingModuleDiagram (R := R) F) ⟨j, y⟩) = yj := by
          simpa [yj] using hf (j := j) y
        exact hcolimit.trans <| hdesc.trans <| by
          rw [hmap, hleft, hright, ← hfx, ← hfy]
          rfl
    }

/-- Helper for Lemma 6.15.2: the underlying linear map of the universal Lie morphism is exactly
the module filtered-colimit desc map. -/
theorem colimitDesc_underlying_eq (t : Cocone F) :
    (colimitDesc (R := R) F t).toLinearMap =
      (ModuleCat.FilteredColimits.colimitDesc (underlyingModuleDiagram (R := R) F)
        ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t)).hom :=
  rfl

/-- Helper for Lemma 6.15.2: the universal Lie morphism restricts to the given cocone map on each
diagram object. -/
@[reassoc (attr := simp)] theorem ι_colimitDesc (t : Cocone F) (j : J) :
    (colimitCocone (R := R) F).ι.app j ≫ colimitDesc (R := R) F t = t.ι.app j := by
  -- Forget to modules, where this is the standard filtered-colimit computation.
  apply LieAlgebraCat.hom_ext
  intro x
  simpa [colimitCocone, coconeMorphism, colimitDesc, colimit] using
    ConcreteCategory.congr_hom
      (ModuleCat.FilteredColimits.ι_colimitDesc (underlyingModuleDiagram (R := R) F)
        ((forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)).mapCocone t) j) x

/-- Helper for Lemma 6.15.2: the explicit Lie-algebra filtered-colimit cocone satisfies the
universal property. -/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone (R := R) F) where
  desc := colimitDesc (R := R) F
  fac t j := by
    simpa using ι_colimitDesc (R := R) (F := F) t j
  uniq t m h := by
    -- Extensionality reduces uniqueness to generator classes of the module colimit.
    apply LieAlgebraCat.hom_ext
    intro y
    obtain ⟨j, y, rfl⟩ :=
      ModuleCat.FilteredColimits.M.mk_surjective (underlyingModuleDiagram (R := R) F) y
    simpa [colimitCocone, coconeMorphism, colimitDesc, colimit] using
      (ConcreteCategory.congr_hom (h j) y).trans
        (ConcreteCategory.congr_hom (ι_colimitDesc (R := R) (F := F) t j) y).symm

end FilteredColimits

/-- Helper for Lemma 6.15.2: the remaining source-faithful step is to put the Lie bracket on the
filtered colimit of the underlying module diagram and prove its universal property. -/
theorem hasFilteredColimits_aux (R : Type u) [CommRing R] :
    HasFilteredColimits (LieAlgebraCat.{u} R) := by
  -- Every filtered diagram gets the explicit cocone constructed above.
  refine
    { HasColimitsOfShape := fun J _ _ ↦
        ⟨fun F ↦ ⟨FilteredColimits.colimitCocone (R := R) F,
          FilteredColimits.colimitCoconeIsColimit (R := R) F⟩⟩ }

/-- Helper for Lemma 6.15.2: once the Lie bracket on filtered colimits is in place, forgetting to
modules preserves those filtered colimits by comparison with the underlying module cocone. -/
theorem forget₂Module_preservesFilteredColimits_aux (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) := by
  -- The explicit Lie filtered-colimit cocone forgets to the standard module filtered-colimit
  -- cocone.
  refine
    { preserves_filtered_colimits := fun J _ _ ↦
        ⟨fun {F} ↦
          preservesColimit_of_preserves_colimit_cocone
            (FilteredColimits.colimitCoconeIsColimit (R := R) F) <| by
              simpa [FilteredColimits.colimitCocone, FilteredColimits.coconeMorphism,
                FilteredColimits.colimit, FilteredColimits.colimitDesc] using
                (ModuleCat.FilteredColimits.colimitCoconeIsColimit
                  (FilteredColimits.underlyingModuleDiagram (R := R) F))⟩ }

instance hasFilteredColimits (R : Type u) [CommRing R] :
    HasFilteredColimits (LieAlgebraCat.{u} R) :=
  hasFilteredColimits_aux (R := R)

instance forget₂Module_preservesFilteredColimits (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (LieAlgebraCat.{u} R) (ModuleCat.{u} R)) :=
  forget₂Module_preservesFilteredColimits_aux (R := R)

instance forget_preservesFilteredColimits (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget (LieAlgebraCat.{u} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (LieAlgebraCat R) (ModuleCat R))
    (forget (ModuleCat.{u} R))

end FilteredColimits

end LieAlgebraCat

/-- Lemma 6.15.2 (7): for a fixed commutative ring `R`, the category of Lie algebras over `R`, with its
forgetful functor to sets, defines a type of algebraic structures. -/
instance lie_algebras_algebraic_structure_type (R : Type u) [CommRing R] :
    IsAlgebraicStructure (LieAlgebraCat.{u} R) (forget (LieAlgebraCat.{u} R)) := by
  -- Route correction: the Lie-algebra limit and filtered-colimit constructions are already proved.
  -- The remaining work is only to supply those instances at the exact inherited parent types.
  letI : HasLimitsOfSize.{u, u} (LieAlgebraCat.{u} R) :=
    show HasLimitsOfSize.{u, u} (LieAlgebraCat.{u} R) from LieAlgebraCat.hasLimits (R := R)
  letI : PreservesLimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) :=
    show PreservesLimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) from
      LieAlgebraCat.forget_preservesLimits (R := R)
  letI : HasFilteredColimitsOfSize.{u, u} (LieAlgebraCat.{u} R) :=
    show HasFilteredColimitsOfSize.{u, u} (LieAlgebraCat.{u} R) from
      LieAlgebraCat.hasFilteredColimits (R := R)
  letI : PreservesFilteredColimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) :=
    show PreservesFilteredColimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} R)) from
      LieAlgebraCat.forget_preservesFilteredColimits (R := R)
  letI : (forget (LieAlgebraCat.{u} R)).ReflectsIsomorphisms :=
    LieAlgebraCat.forget_reflectsIsomorphisms (R := R)
  -- With the exact parent classes in scope, the bundled algebraic-structure predicate follows.
  exact
    IsAlgebraicStructure.mk (C := LieAlgebraCat.{u} R) (F := forget (LieAlgebraCat.{u} R))
