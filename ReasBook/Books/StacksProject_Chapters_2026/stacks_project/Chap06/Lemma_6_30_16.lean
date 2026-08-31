module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Lemma_6_30_14

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

universe w v u

section

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable (BX : Set (Opens X)) (BY : Set (Opens Y))
variable (𝒢 : TopCat.Sheaf C Y) (ℱ : TopCat.Sheaf C X)

private instance basisOpenInclusion_isContinuous (hBX : Opens.IsBasis BX) :
    Functor.IsContinuous (basisOpenInclusion BX)
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) := by
  letI : (basisOpenInclusion BX).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hBX
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) (basisOpenInclusion BX)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion BX)
        (Opens.grothendieckTopology X))

-- The ambient inclusion of opens underlying a morphism in a basis-open full subcategory.
public theorem basisOpenHomLE {Z : TopCat.{w}} {B : Set (Opens Z)}
    {U V : BasisOpen B} (i : U ⟶ V) :
    U.obj ≤ V.obj :=
  i.hom.le

/- Domain-style sampling for Lemma 6.30.16:
- primary domain: basis-indexed pushforward morphisms of sheaves, with source-facing section data
  on basis opens of both `X` and `Y`;
- sampled owner declarations:
  `BasisOpen`,
  `basisOpenInclusion`,
  `Functor.sheafPushforwardContinuous`,
  `existsUnique_pushforward_hom_of_basis_restriction`;
- best owner abstraction: the canonical owner of the resulting map is the pushforward morphism
  `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`, while the basis-indexed section family is source-facing
  input data and the induced morphism between basis restrictions is derived API;
- primitive data: the section components `app` together with naturality in the source basis open
  and the target basis open;
- derived API: under the basis-restriction equivalences from Lemma `6.30.14`, such a family
  determines a unique morphism `𝒢 ⟶ f_* ℱ`.

Source/core/bridge triage:
- `source-facing`: `BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ`;
- `core/canonical`: `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`;
- `bridge/view`: the morphism between the basis restrictions of `𝒢` and `f_* ℱ` obtained from the
  section family via the basis-site equivalence.
-/
/-- A family of section morphisms on basis opens of `Y` and `X` over a continuous map `f`,
compatible with restriction in both variables. -/
structure BasisContinuousMapSectionFamily where
  app (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    𝒢.presheaf.obj (op V.obj) ⟶ ℱ.presheaf.obj (op U.obj)
  source_naturality {U U' : BasisOpen BX} (i : U' ⟶ U) {V : BasisOpen BY}
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    app U V h ≫ ℱ.presheaf.map (homOfLE (basisOpenHomLE i)).op =
      app U' V ((basisOpenHomLE i).trans h)
  target_naturality {U : BasisOpen BX} {V V' : BasisOpen BY} (j : V ⟶ V')
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫ app U V h =
      app U V'
        (h.trans ((Opens.map f).map (homOfLE (basisOpenHomLE j))).le)

/-- Helper for Lemma 6.30.16: on a basis open `V` of `Y`, the pushforward sheaf evaluates to the
section object of `ℱ` on the preimage open `f⁻¹(V)`. -/
lemma pushforward_obj_on_basis_open (V : BasisOpen BY) :
    ((Sheaf.pushforward C f).obj ℱ).presheaf.obj (op V.obj) =
      ℱ.presheaf.obj (op ((Opens.map f).obj V.obj)) :=
  rfl

/-- Helper for Lemma 6.30.16: for a fixed basis open `V` of `Y`, the maps
`φ.app U V h : 𝒢(V) ⟶ ℱ(U)` over basis neighborhoods `U ⊆ f⁻¹(V)` form a cone on the
structured-arrow diagram computing the right Kan extension over `f⁻¹(V)`. -/
noncomputable def section_family_structured_arrow_cone
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    (V : BasisOpen BY) :
    Cone (StructuredArrow.proj (op ((Opens.map f).obj V.obj)) (basisOpenInclusion BX).op ⋙
      (((basisOpenInclusion BX).sheafPushforwardContinuous C
        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj ℱ).obj) where
  pt := 𝒢.presheaf.obj (op V.obj)
  π :=
    { app := fun g ↦
        φ.app g.right.unop V
          (show g.right.unop.obj ≤ (Opens.map f).obj V.obj from g.hom.unop.le)
      naturality := by
        intro g g' i
        -- The structured-arrow morphism reverses the basis inclusion, exactly matching the
        -- `U`-naturality built into the source family.
        simpa using
          (φ.source_naturality (V := V) i.right.unop
            (show g.right.unop.obj ≤ (Opens.map f).obj V.obj from g.hom.unop.le)).symm }

/-- Helper for Lemma 6.30.16: the universal morphism from `𝒢(V)` into the limit of the basis
neighborhood diagram over `f⁻¹(V)`. This is the categorical replacement for the source proof's
stalkwise construction on a fixed basis open `V`. -/
noncomputable def section_family_limit_lift
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (V : BasisOpen BY) :
    𝒢.presheaf.obj (op V.obj) ⟶
      limit (StructuredArrow.proj (op ((Opens.map f).obj V.obj)) (basisOpenInclusion BX).op ⋙
        (((basisOpenInclusion BX).sheafPushforwardContinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj ℱ).obj) :=
  limit.lift _ (section_family_structured_arrow_cone (f := f) (BX := BX) (BY := BY)
    (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V)

/-- Helper for Lemma 6.30.16: the universal lift to the limit recovers the given basis component
after projecting to any basis neighborhood of `f⁻¹(V)`. -/
lemma section_family_limit_lift_π
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (V : BasisOpen BY)
    (g : StructuredArrow (op ((Opens.map f).obj V.obj)) (basisOpenInclusion BX).op) :
    section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
        limit.π _ g =
      φ.app g.right.unop V
        (show g.right.unop.obj ≤ (Opens.map f).obj V.obj from g.hom.unop.le) := by
  -- Evaluate the limit lift on the cone leg indexed by `g`.
  simpa [section_family_limit_lift, section_family_structured_arrow_cone] using
    limit.lift_π
      (section_family_structured_arrow_cone (f := f) (BX := BX) (BY := BY)
        (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V)
      g

/-- Helper for Lemma 6.30.16: the universal limit lift specializes to the original prescribed
map when one evaluates at the structured-arrow object corresponding to a basis inclusion
`U ⊆ f⁻¹(V)`. -/
lemma section_family_limit_lift_π_basis
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
        limit.π _ (StructuredArrow.mk (homOfLE h).op) =
      φ.app U V h := by
  -- The structured-arrow object `StructuredArrow.mk (homOfLE h).op` is exactly the basis
  -- neighborhood `U ⊆ f⁻¹(V)`.
  simpa using
    section_family_limit_lift_π (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V
      (StructuredArrow.mk (homOfLE h).op)

/-- Helper for Lemma 6.30.16: the comparison unit from a sheaf on `X` to the extension of its
basis restriction, followed by the canonical limit identification, restricts on a basis inclusion
`U ⊆ W` to the usual restriction map `ℱ(W) ⟶ ℱ(U)`. -/
lemma basis_restriction_unit_app_comp_π
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (W : Opens X) (U : BasisOpen BX) (h : U.obj ≤ W) :
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ).hom.app
        (op W) ≫
        ((basisOpenInclusion BX).op.ranObjObjIsoLimit
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
            (op W)).hom ≫
        limit.π
          (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
            (((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
          (StructuredArrow.mk (homOfLE h).op) =
      ℱ.presheaf.map (homOfLE h).op := by
  -- Rewrite the sheaf-side unit into the raw right Kan extension unit.
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom]
  have hπ :=
    Functor.ranObjObjIsoLimit_hom_π (L := (basisOpenInclusion BX).op)
      (F := (((basisOpenInclusion BX).sheafPushforwardContinuous C
        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj ℱ).obj)
      (X := op W) (f := StructuredArrow.mk (homOfLE h).op)
  have hrewrite₁ :
      (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫
          ((basisOpenInclusion BX).op.ranObjObjIsoLimit
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
              (op W)).hom ≫
          limit.π
            (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
              (((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
            (StructuredArrow.mk (homOfLE h).op)
        = (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫
            ((basisOpenInclusion BX).op.ran.obj
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).map
              (homOfLE h).op ≫
            (((basisOpenInclusion BX).op.ranCounit.app
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).app
              (op U)) := by
    simpa [Category.assoc] using congrArg
      (fun k => (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫ k) hπ
  have hnat :=
    NatTrans.naturality (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj)
      (homOfLE h).op
  have hrewrite₂ :
      (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op W) ≫
          ((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
            (homOfLE h).op ≫
          (((basisOpenInclusion BX).op.ranCounit.app
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).app
            (op U)) =
        (ℱ.presheaf.map (homOfLE h).op ≫
            (((basisOpenInclusion BX).op.ranAdjunction C).unit.app ℱ.obj).app (op U.obj)) ≫
          (((basisOpenInclusion BX).op.ranCounit.app
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).app
            (op U)) := by
    have h₂raw := congrArg
      (fun k => k ≫
        (((basisOpenInclusion BX).op.ranCounit.app
          ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                  (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
              ℱ).obj)).app (op U))) hnat.symm
    simpa [Functor.sheafPushforwardContinuous, Category.assoc] using h₂raw
  refine hrewrite₁.trans ?_
  refine hrewrite₂.trans ?_
  -- The remaining composite is the triangle identity for the right Kan extension adjunction.
  rw [Category.assoc]
  simpa using congrArg
    (fun k => ℱ.presheaf.map (homOfLE h).op ≫ k)
    (Functor.ranCounit_app_app_ranAdjunction_unit_app_app
      (L := (basisOpenInclusion BX).op) (H := C) ℱ.obj (op U))

/-- Helper for Lemma 6.30.16: restriction to the basis `BX` is an equivalence on `C`-valued
sheaves once `BX` is a basis and the needed right Kan extension limits exist. -/
public noncomputable instance basisOpenRestriction_isEquivalence
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C] :
    Functor.IsEquivalence
      ((basisOpenInclusion BX).sheafPushforwardContinuous C
        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)) := by
  letI : (basisOpenInclusion BX).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hBX
  let G := (basisOpenInclusion BX).sheafPushforwardContinuous C
    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)
  simpa using inferInstanceAs (G.IsEquivalence)

/-- Helper for Lemma 6.30.16: the basis-restriction unit formula may be read against any
structured-arrow object over `W`, not only the canonical one built from an explicit inclusion. -/
lemma basis_restriction_unit_app_comp_π_structured_arrow
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (W : Opens X)
    (g : StructuredArrow (op W) (basisOpenInclusion BX).op) :
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ).hom.app
        (op W) ≫
        ((basisOpenInclusion BX).op.ranObjObjIsoLimit
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
            (op W)).hom ≫
        limit.π
          (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
            (((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)
          g =
      ℱ.presheaf.map g.hom := by
  -- Every structured-arrow object is the canonical basis inclusion carried by its arrow.
  have hg : g = StructuredArrow.mk g.hom :=
    StructuredArrow.eq_mk g
  have hh : (homOfLE g.hom.unop.le).op = g.hom :=
    Subsingleton.elim _ _
  simpa [hg, hh] using
    basis_restriction_unit_app_comp_π (C := C) (X := X) (BX := BX) (ℱ := ℱ)
      hBX W g.right.unop g.hom.unop.le

/-- Helper for Lemma 6.30.16: on a basis open `U`, the forward unit component followed by the
right Kan extension counit is the identity. -/
lemma basis_restriction_unit_component_hom_inv_id
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) :
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ).hom.app
        (op U.obj) ≫
      (((basisOpenInclusion BX).op.ranCounit.app
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)).app
          (op U)) =
        𝟙 _ := by
  let η :=
    ((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ
  let ρ :=
    (basisOpenInclusion BX).op.ranObjObjIsoLimit
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj)
      (op U.obj)
  let κ :=
    ((basisOpenInclusion BX).op.ranCounit.app
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj))
  have hπ :
      ρ.hom ≫
          limit.π
            (StructuredArrow.proj (op U.obj) (basisOpenInclusion BX).op ⋙
              (((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
            (StructuredArrow.mk (homOfLE (show U.obj ≤ U.obj from le_rfl)).op) =
        κ.app (op U) := by
    -- The identity basis inclusion projects from the limit to the counit component at `U`.
    simpa [ρ, κ] using
      (Functor.ranObjObjIsoLimit_hom_π (L := (basisOpenInclusion BX).op)
        (F := ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj))
        (X := op U.obj)
        (f := StructuredArrow.mk (homOfLE (show U.obj ≤ U.obj from le_rfl)).op))
  have hunit :
      η.hom.app (op U.obj) ≫ ρ.hom ≫
          limit.π
            (StructuredArrow.proj (op U.obj) (basisOpenInclusion BX).op ⋙
              (((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)
            (StructuredArrow.mk (homOfLE (show U.obj ≤ U.obj from le_rfl)).op) =
        ℱ.presheaf.map (homOfLE (show U.obj ≤ U.obj from le_rfl)).op := by
    -- This is the basis-restriction unit formula at the identity inclusion `U ⊆ U`.
    simpa [η, ρ] using
      basis_restriction_unit_app_comp_π (C := C) (X := X) (BX := BX) (ℱ := ℱ)
        hBX U.obj U (show U.obj ≤ U.obj from le_rfl)
  -- Specialize the basis-restriction unit formula to the identity inclusion `U ⊆ U`.
  rw [← hπ]
  exact hunit.trans (by simp)

/-- Helper for Lemma 6.30.16: on a basis open `U`, the inverse of the sheaf-side comparison unit
is the corresponding right Kan extension counit component. -/
lemma basis_restriction_unit_component_inv
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) :
    ((asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
            (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app
          ℱ)).inv).hom.app (op U.obj) =
      (((basisOpenInclusion BX).op.ranCounit.app
            ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj)).app
          (op U)) := by
  let η :=
    asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ)
  let κ :=
    ((basisOpenInclusion BX).op.ranCounit.app
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj))
  let ηp : ℱ.presheaf ≅
      (((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) ⋙
            (basisOpenInclusion BX).sheafPushforwardCocontinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj :=
    ⟨η.hom.hom, η.inv.hom,
      congrArg (fun ψ ↦ ψ.hom) η.hom_inv_id,
      congrArg (fun ψ ↦ ψ.hom) η.inv_hom_id⟩
  -- The basis-open triangle identity identifies the counit as the inverse component.
  have htri :
      η.hom.hom.app (op U.obj) ≫ κ.app (op U) = 𝟙 _ := by
    simpa [η, κ] using
      basis_restriction_unit_component_hom_inv_id
        (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX U
  have hinv :
      η.inv.hom.app (op U.obj) ≫ η.hom.hom.app (op U.obj) = 𝟙 _ := by
    simpa [η, ηp] using ηp.inv_hom_id_app (op U.obj)
  have hcomp :
      η.inv.hom.app (op U.obj) =
        η.inv.hom.app (op U.obj) ≫ (η.hom.hom.app (op U.obj) ≫ κ.app (op U)) := by
    rw [htri]
    simp
  have hassoc :
      η.inv.hom.app (op U.obj) ≫ (η.hom.hom.app (op U.obj) ≫ κ.app (op U)) =
        (η.inv.hom.app (op U.obj) ≫ η.hom.hom.app (op U.obj)) ≫ κ.app (op U) := by
    rw [Category.assoc]
  have hcancel :
      (η.inv.hom.app (op U.obj) ≫ η.hom.hom.app (op U.obj)) ≫ κ.app (op U) =
        κ.app (op U) := by
    rw [hinv, Category.id_comp]
  exact hcomp.trans (hassoc.trans hcancel)

/-- Helper for Lemma 6.30.16: a morphism into `ℱ(W)` is determined by all of its basis
restrictions to basis opens `U ⊆ W`. -/
lemma basis_restriction_hom_ext
    (hBX : Opens.IsBasis BX)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    {A : C} {W : Opens X}
    {α β : A ⟶ ℱ.presheaf.obj (op W)}
    (hαβ : ∀ (U : BasisOpen BX) (h : U.obj ≤ W),
      α ≫ ℱ.presheaf.map (homOfLE h).op =
        β ≫ ℱ.presheaf.map (homOfLE h).op) :
    α = β := by
  let η :=
    asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ)
  let ρ :=
    (basisOpenInclusion BX).op.ranObjObjIsoLimit
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj)
      (op W)
  let μ :
      ℱ.presheaf.obj (op W) ⟶
        ((basisOpenInclusion BX).op.ran.obj
          ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                  (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
              ℱ).obj)).obj
          (op W) :=
    (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
          (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app
      ℱ).hom.app (op W)
  let ηp : ℱ.presheaf ≅
      (((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X) ⋙
            (basisOpenInclusion BX).sheafPushforwardCocontinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj :=
    ⟨η.hom.hom, η.inv.hom,
      congrArg (fun ψ ↦ ψ.hom) η.hom_inv_id,
      congrArg (fun ψ ↦ ψ.hom) η.inv_hom_id⟩
  -- Route correction: transport both maps forward into the basis-neighborhood limit and prove
  -- equality there, so no transport-back helper is needed.
  have hforward :
      α ≫ μ ≫ ρ.hom =
        β ≫ μ ≫ ρ.hom := by
    apply limit.hom_ext
    intro g
    -- Each structured-arrow object records a basis inclusion `g.right.unop ⊆ W`, so the
    -- projected forward transport is exactly that basis restriction.
    have hαg :
        (α ≫ μ ≫ ρ.hom) ≫
            limit.π
              (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
                (((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)
              g =
          α ≫ ℱ.presheaf.map g.hom := by
      simpa [μ, ρ, Category.assoc] using congrArg
        (fun k ↦ α ≫ k)
        (basis_restriction_unit_app_comp_π_structured_arrow
          (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX W g)
    have hβg :
        (β ≫ μ ≫ ρ.hom) ≫
            limit.π
              (StructuredArrow.proj (op W) (basisOpenInclusion BX).op ⋙
                (((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)
              g =
          β ≫ ℱ.presheaf.map g.hom := by
      simpa [μ, ρ, Category.assoc] using congrArg
        (fun k ↦ β ≫ k)
        (basis_restriction_unit_app_comp_π_structured_arrow
          (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX W g)
    exact hαg.trans ((hαβ g.right.unop g.hom.unop.le).trans hβg.symm)
  -- Postcompose with the inverse comparison maps to return from the limit object to `ℱ(W)`.
  have hback :
      α ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) =
        β ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ ρ.inv ≫ η.inv.hom.app (op W)) hforward
  have hρ : ρ.hom ≫ ρ.inv = 𝟙 _ := by
    simp [ρ]
  have hη :
      μ ≫ η.inv.hom.app (op W) = 𝟙 _ := by
    simpa [η, ηp, μ] using ηp.hom_inv_id_app (op W)
  have hαρ :
      α ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) =
        α ≫ μ ≫ η.inv.hom.app (op W) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ α ≫ k ≫ η.inv.hom.app (op W)) hρ
  have hαη :
      α ≫ μ ≫ η.inv.hom.app (op W) = α := by
    simpa [Category.assoc] using congrArg (fun k ↦ α ≫ k) hη
  have hα :
      α = α ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) := by
    exact (hαρ.trans hαη).symm
  have hβρ :
      β ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) =
        β ≫ μ ≫ η.inv.hom.app (op W) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ β ≫ k ≫ η.inv.hom.app (op W)) hρ
  have hβη :
      β ≫ μ ≫ η.inv.hom.app (op W) = β := by
    simpa [Category.assoc] using congrArg (fun k ↦ β ≫ k) hη
  have hβ :
      β ≫ μ ≫ ρ.hom ≫ ρ.inv ≫ η.inv.hom.app (op W) = β := by
    exact hβρ.trans hβη
  exact hα.trans (hback.trans hβ)

/-- Helper for Lemma 6.30.16: for a fixed basis open `V` of `Y`, transport the compatible family
`φ.app _ V _` back from the basis-neighborhood limit to a section over `f⁻¹(V)`. -/
noncomputable def basis_section_map_of_family
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (V : BasisOpen BY) :
    𝒢.presheaf.obj (op V.obj) ⟶
      ℱ.presheaf.obj (op ((Opens.map f).obj V.obj)) :=
  section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
    ((basisOpenInclusion BX).op.ranObjObjIsoLimit
        ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
            ℱ).obj)
        (op ((Opens.map f).obj V.obj))).inv ≫
    ((asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
            (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app
          ℱ)).inv).hom.app (op ((Opens.map f).obj V.obj))

/-- Helper for Lemma 6.30.16: the fixed-`V` section map recovers the prescribed basis-pair map
after restricting from `f⁻¹(V)` to a basis open `U ⊆ f⁻¹(V)`. -/
lemma basis_section_map_of_family_restrict
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
        ℱ.presheaf.map (homOfLE h).op =
      φ.app U V h := by
  let η :=
    asIso (((basisOpenInclusion BX).sheafAdjunctionCocontinuous C
      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).unit.app ℱ)
  let ρ :=
    (basisOpenInclusion BX).op.ranObjObjIsoLimit
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj)
      (op ((Opens.map f).obj V.obj))
  let κ :=
    ((basisOpenInclusion BX).op.ranCounit.app
      ((((basisOpenInclusion BX).sheafPushforwardContinuous C
              (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
          ℱ).obj))
  have hη :
      ρ.inv ≫ η.inv.hom.app (op ((Opens.map f).obj V.obj)) ≫ ℱ.presheaf.map (homOfLE h).op =
        ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          η.inv.hom.app (op U.obj) := by
    -- Move the restriction past the inverse unit while keeping the preceding `ρ.inv` fixed.
    simpa [η, Category.assoc] using
      congrArg (fun k ↦ ρ.inv ≫ k) ((η.inv.hom.naturality (homOfLE h).op).symm)
  have hκ :
      ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          η.inv.hom.app (op U.obj) =
        ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          κ.app (op U) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ρ.inv ≫
            (((basisOpenInclusion BX).op.ran.obj
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).map
                (homOfLE h).op) ≫
            k)
        (basis_restriction_unit_component_inv (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX U)
  have hρ :
      ρ.inv ≫
          (((basisOpenInclusion BX).op.ran.obj
              ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                      (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                  ℱ).obj)).map
              (homOfLE h).op) ≫
          κ.app (op U) =
        limit.π _ (StructuredArrow.mk (homOfLE h).op) := by
    -- The inverse right-Kan comparison sends the relevant restriction map to the matching limit
    -- projection.
    simpa [ρ, κ] using
      (Functor.ranObjObjIsoLimit_inv_π (L := (basisOpenInclusion BX).op)
        (F := ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                    (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                ℱ).obj))
        (X := op ((Opens.map f).obj V.obj))
        (f := StructuredArrow.mk (homOfLE h).op))
  -- Rewrite the transported restriction map until only the canonical limit projection remains.
  have htransport :
      basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          ℱ.presheaf.map (homOfLE h).op =
        section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          ρ.inv ≫
            (((basisOpenInclusion BX).op.ran.obj
                ((((basisOpenInclusion BX).sheafPushforwardContinuous C
                        (basisGrothendieckTopology BX hBX) (Opens.grothendieckTopology X)).obj
                    ℱ).obj)).map
                (homOfLE h).op) ≫
            κ.app (op U) := by
    simpa [basis_section_map_of_family, Category.assoc] using
      congrArg
        (fun k ↦
          section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
            k)
        (hη.trans hκ)
  have hπ :
    basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          ℱ.presheaf.map (homOfLE h).op =
        section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
          limit.π _ (StructuredArrow.mk (homOfLE h).op) := by
      rw [htransport]
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            section_family_limit_lift (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ V ≫
              k) hρ
  exact hπ.trans <| by
    simpa using
      section_family_limit_lift_π_basis (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
        hBX φ U V h

/-- Helper for Lemma 6.30.16: the fixed-`V` section maps are natural in the basis open `V` of
`Y`, so they assemble into the basis-restriction morphism required for Lemma `6.30.14`. -/
lemma basis_section_map_of_family_natural
    (hBX : Opens.IsBasis BX) (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    {V V' : BasisOpen BY} (j : V ⟶ V') :
    𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫
        basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V =
      basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V' ≫
        ℱ.presheaf.map ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op := by
  -- Compare the two maps after restricting to every basis open inside `f⁻¹(V)`.
  apply basis_restriction_hom_ext (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX
  intro U hU
  let hU' : U.obj ≤ (Opens.map f).obj V'.obj :=
    hU.trans ((Opens.map f).map (homOfLE (basisOpenHomLE j))).le
  have hcomp :
      ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op ≫ (homOfLE hU).op =
        (homOfLE hU').op :=
    Subsingleton.elim _ _
  have hmap :
      ℱ.presheaf.map ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op ≫
          ℱ.presheaf.map (homOfLE hU).op =
        ℱ.presheaf.map (homOfLE hU').op := by
    -- The preimage restriction followed by the basis restriction is the single composite
    -- restriction to `U ⊆ f⁻¹(V')`.
    simpa [Functor.map_comp] using congrArg ℱ.presheaf.map hcomp
  -- Both sides reduce to the prescribed target-naturality square for `φ`.
  calc
    (𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫
          basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V) ≫
          ℱ.presheaf.map (homOfLE hU).op =
        𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫ φ.app U V hU := by
      rw [Category.assoc, basis_section_map_of_family_restrict
        (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V hU]
    _ = φ.app U V' hU' := by
      simpa [hU'] using φ.target_naturality (U := U) (j := j) (h := hU)
    _ = basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V' ≫
        ℱ.presheaf.map (homOfLE hU').op := by
      symm
      exact basis_section_map_of_family_restrict
        (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V' hU'
    _ = (basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
          hBX φ V' ≫
        ℱ.presheaf.map ((Opens.map f).map (homOfLE (basisOpenHomLE j))).op) ≫
          ℱ.presheaf.map (homOfLE hU).op := by
      rw [Category.assoc, hmap]

-- Proof sketch: for each basis open `V` of `Y`, the `U`-naturality makes the family
-- `φ.app _ V _` into a compatible basis restriction datum on the open `f⁻¹(V)` of `X`, so the
-- basis-site equivalence on `X` yields a unique section map `𝒢(V) ⟶ ℱ(f⁻¹(V))` in `C`. The
-- `V`-naturality then assembles these maps into a morphism between the basis restrictions of `𝒢`
-- and `f_* ℱ` on `BY`, and Lemma `6.30.14` upgrades that canonical basis-restriction morphism to
-- a unique global morphism `𝒢 ⟶ f_* ℱ`.
/-- Lemma 6.30.16: a family of morphisms `𝒢(V) ⟶ ℱ(U)` given for basis opens `V` of `Y` and `U`
of `X` with `U ⊆ f⁻¹(V)` (equivalently `f(U) ⊆ V`), and compatible with restriction in both
variables, comes from a unique morphism `𝒢 ⟶ f_* ℱ` recovering the given maps after restricting
from `f⁻¹(V)` to `U`. -/
theorem existsUnique_pushforward_hom_of_basis_section_family
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    [∀ V : (Opens Y)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (basisOpenInclusion BY).op) C]
    (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ) :
    ∃! Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h := by
  let φB :
      ((basisOpenInclusion BY).sheafPushforwardContinuous C
          (basisGrothendieckTopology BY hBY) (Opens.grothendieckTopology Y)).obj 𝒢 ⟶
        ((basisOpenInclusion BY).sheafPushforwardContinuous C
          (basisGrothendieckTopology BY hBY) (Opens.grothendieckTopology Y)).obj
          ((Sheaf.pushforward C f).obj ℱ) :=
    CategoryTheory.ObjectProperty.homMk
      { app := fun V ↦
          basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V.unop
        naturality := by
          intro V V' i
          -- The fixed-`V` construction is natural in the `Y`-basis variable.
          simpa using
            basis_section_map_of_family_natural (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢)
              (ℱ := ℱ) hBX φ i.unop }
  rcases existsUnique_pushforward_hom_of_basis_restriction
      (C := C) (f := f) (ℱ := ℱ) (𝒢 := 𝒢) (B := BY) hBY φB with
    ⟨Φ, hΦ, hΦ_unique⟩
  refine ⟨Φ, ?_, ?_⟩
  · intro U V h
    have hΦV :
        Φ.hom.app (op V.obj) =
          basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V := by
      -- The global extension agrees with the basis-restriction morphism on each basis open.
      simpa [φB] using congrArg (fun ψ ↦ ψ.hom.app (op V)) hΦ
    -- The component formula is exactly the fixed-`V` restriction lemma after identifying
    -- `Φ` with the basis extension on `V`.
    simpa [hΦV] using
      basis_section_map_of_family_restrict
        (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V h
  · intro Ψ hΨ
    apply hΦ_unique
    apply CategoryTheory.Sheaf.hom_ext
    ext V
    change Ψ.hom.app (op V.unop.obj) =
      basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
        hBX φ V.unop
    -- Route correction: uniqueness is proved by fixed-open basis extensionality on `X`, not by
    -- a second dense-subsite transport argument on `Y`.
    apply basis_restriction_hom_ext (C := C) (X := X) (BX := BX) (ℱ := ℱ) hBX
    intro U hU
    calc
      Ψ.hom.app (op V.unop.obj) ≫ ℱ.presheaf.map (homOfLE hU).op = φ.app U V.unop hU := by
        exact hΨ U V.unop hU
      _ = basis_section_map_of_family (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ)
            hBX φ V.unop ≫
          ℱ.presheaf.map (homOfLE hU).op := by
        symm
        exact basis_section_map_of_family_restrict
          (f := f) (BX := BX) (BY := BY) (𝒢 := 𝒢) (ℱ := ℱ) hBX φ U V.unop hU

end
