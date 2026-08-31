module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Definition_6_15_1
public import stacks_project.Chap06.Lemma_6_11_1
public import stacks_project.Chap06.Lemma_6_13_1
public import stacks_project.Chap06.Lemma_6_15_3
public import stacks_project.Chap06.Lemma_6_15_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w u

/- Domain-style sampling for Lemma 6.16.4:
- primary domain: sheaves of algebraic structures on a topological space, compared with their
  underlying sheaves of sets through stalk functors;
- inspected owner declarations:
  `IsAlgebraicStructure`,
  `sheafCompose`,
  `filteredStalk`,
  `stalkCompIso`,
  `existsUnique_pushforward_hom_of_underlying_sectionwise_structure_preserving`;
- best owner abstraction:
  the source-facing owner here is the underlying morphism of sheaves of sets
  `(sheafCompose (Opens.grothendieckTopology X) F).obj ℱ ⟶
    (sheafCompose (Opens.grothendieckTopology X) F).obj 𝒢`,
  with the `C`-valued sheaf morphism `Φ : ℱ ⟶ 𝒢` recovered uniquely from it;
- primitive data:
  the underlying morphism of set-valued sheaves `φ` and the stalkwise existence of lifts in `C`;
- derived API:
  the comparison isomorphisms `stalkCompIso` and the equality
  `(sheafCompose (Opens.grothendieckTopology X) F).map Φ = φ`.

Source/core/bridge triage:
- `source-facing`: the textbook stalkwise criterion for lifting an underlying morphism of sheaves
  of sets to a morphism of sheaves of algebraic structures;
- `core/canonical`: the underlying sheaf-of-sets owner `sheafCompose (Opens.grothendieckTopology X) F`,
  with the sectionwise lifting criterion later abstracted by
  `existsUnique_pushforward_hom_of_underlying_sectionwise_structure_preserving`;
- `bridge/view`: the stalkwise compatibility equation expressed via `stalkCompIso`.

The theorem is therefore not a duplicate owner declaration. The right refinement is to keep this
source-facing theorem while aligning its surface with the chapter’s canonical owner API.
-/

section

variable {C : Type u} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]
variable {X : TopCat.{w}}
variable {ℱ 𝒢 : X.Sheaf C}

local notation "J" => Opens.grothendieckTopology X
local notation "underlyingSheaf" =>
  @sheafCompose _ _ _ _ _ _ J F (hasSheafCompose_of_preservesLimitsOfSize J)

/-- Helper for Lemma 6.16.4: forgetting a morphism of `C`-valued sheaves applies `F` to each
section map. -/
lemma underlying_sheaf_map_app
    (Φ : ℱ ⟶ 𝒢) (U : Opens X) :
    (Sheaf.homEquiv ((underlyingSheaf).map Φ)).app (op U) =
      F.map ((Sheaf.homEquiv Φ).app (op U)) := by
  -- This is definitionally how `sheafCompose` acts on morphisms.
  rfl

/-- Helper for Lemma 6.16.4: if sectionwise lifts of the underlying map are given, then they
satisfy the presheaf naturality condition. -/
lemma chosen_section_maps_natural
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (hφ : ∀ U : Opens X, ∃ ψU : ℱ.presheaf.obj (op U) ⟶ 𝒢.presheaf.obj (op U),
      F.map ψU = (Sheaf.homEquiv φ).app (op U))
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ℱ.presheaf.map i ≫ Classical.choose (hφ V.unop) =
      Classical.choose (hφ U.unop) ≫ 𝒢.presheaf.map i := by
  -- Faithfulness reduces naturality to the naturality square of the underlying sheaf map.
  apply F.map_injective
  rw [Functor.map_comp, Functor.map_comp, Classical.choose_spec (hφ V.unop),
    Classical.choose_spec (hφ U.unop)]
  simpa using (NatTrans.naturality (Sheaf.homEquiv φ) i)

/-- Helper for Lemma 6.16.4: sectionwise lifts assemble into a morphism of presheaves of
`C`-objects. -/
def sectionwise_lift_to_presheaf_hom
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (hφ : ∀ U : Opens X, ∃ ψU : ℱ.presheaf.obj (op U) ⟶ 𝒢.presheaf.obj (op U),
      F.map ψU = (Sheaf.homEquiv φ).app (op U)) :
    ℱ.presheaf ⟶ 𝒢.presheaf where
  app U := Classical.choose (hφ U.unop)
  naturality := fun {_ _} i ↦ chosen_section_maps_natural (F := F) (φ := φ) hφ i

/-- Helper for Lemma 6.16.4: the sheaf morphism built from sectionwise lifts forgets to the
original underlying sheaf morphism. -/
lemma constructed_lift_recovers_underlying_map
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (hφ : ∀ U : Opens X, ∃ ψU : ℱ.presheaf.obj (op U) ⟶ 𝒢.presheaf.obj (op U),
      F.map ψU = (Sheaf.homEquiv φ).app (op U)) :
    (underlyingSheaf).map
        (Sheaf.homEquiv.symm (sectionwise_lift_to_presheaf_hom (F := F) (φ := φ) hφ)) = φ := by
  -- Compare the two underlying morphisms componentwise on sections over each open set.
  apply (Sheaf.homEquiv).injective
  ext U
  rw [underlying_sheaf_map_app]
  rename_i a
  change F.map ((sectionwise_lift_to_presheaf_hom (F := F) (φ := φ) hφ).app U) a =
    (Sheaf.homEquiv φ).app U a
  simpa [sectionwise_lift_to_presheaf_hom] using congrFun (Classical.choose_spec (hφ U.unop)) a

/-- Helper for Lemma 6.16.4: over an open set `U`, the relevant product family is the family of
filtered stalks at the points of `U`. -/
abbrev filtered_stalk_family (ℋ : X.Sheaf C) (U : Opens X) : U → C :=
  fun x ↦ filteredStalk x.1 ℋ.presheaf

/-- Helper for Lemma 6.16.4: `C` has products indexed by types of the base universe. -/
private abbrev hasProductsOfBaseSize [HasLimits C] : HasProducts.{w} C := by
  -- Route correction: cache the base-size product owner once instead of reopening `HasLimits`
  -- synthesis at every filtered-stalk product.
  intro I
  let _ : HasLimitsOfShape (Discrete I) C :=
    HasLimits.has_limits_of_shape (C := C) (Discrete I)
  infer_instance

/-- Helper for Lemma 6.16.4: the filtered stalk family over a fixed open set carries the product
needed for the source diagram. -/
local instance filtered_stalk_family_hasProduct (ℋ : X.Sheaf C) (U : Opens X) :
    HasProduct (fun x : U ↦ filteredStalk x.1 ℋ.presheaf) := by
  -- Reuse the cached base-size products to build the product over the point-set `U`.
  let hbase : HasProducts.{w} C := hasProductsOfBaseSize (C := C)
  change HasLimit (Discrete.functor (fun x : U ↦ filteredStalk x.1 ℋ.presheaf))
  let hshape : HasProductsOfShape U C := @hasProductsOfShape_of_hasProducts _ _ hbase U
  exact hshape.has_limit (Discrete.functor (fun x : U ↦ filteredStalk x.1 ℋ.presheaf))

/-- Helper for Lemma 6.16.4: the neighborhood diagram defining a filtered stalk carries the
required colimit structure. -/
local instance openNhds_isCofiltered (x : X) : IsCofiltered (OpenNhds x) := by
  -- Open neighborhoods are closed under intersections, so they form a cofiltered poset.
  let _ : SemilatticeInf (OpenNhds x) := inferInstance
  let _ : Nonempty (OpenNhds x) := inferInstance
  exact CategoryTheory.isCofiltered_of_semilatticeInf_nonempty (OpenNhds x)

/-- Helper for Lemma 6.16.4: the opposite neighborhood category of a point is filtered. -/
local instance openNhds_op_isFiltered (x : X) : IsFiltered (OpenNhds x)ᵒᵖ :=
  CategoryTheory.isFiltered_op_of_isCofiltered (C := OpenNhds x)

/-- Helper for Lemma 6.16.4: the neighborhood diagram defining a filtered stalk carries the
required colimit structure. -/
public theorem filtered_stalk_colimit (ℋ : X.Sheaf C) (x : X)
    [hfiltered : HasFilteredColimitsOfSize.{w, w} C] :
    HasColimit (((OpenNhds.inclusion x).op) ⋙ ℋ.presheaf) := by
  -- Route correction: install the small filtered-colimit owner locally before asking for this
  -- specific neighborhood colimit.
  let hshape : HasColimitsOfShape (OpenNhds x)ᵒᵖ C :=
    @CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits _ _ hfiltered _ _ _
  exact hshape.has_colimit (((OpenNhds.inclusion x).op) ⋙ ℋ.presheaf)

/-- Helper for Lemma 6.16.4: forgetting along `F` preserves the product of filtered stalks over a
fixed open set. -/
private theorem filtered_stalk_family_preservesProduct (ℋ : X.Sheaf C) (U : Opens X) :
    PreservesLimit (Discrete.functor (fun x : U ↦ filteredStalk x.1 ℋ.presheaf)) F := by
  -- Cache the preserved-product comparison once for the fixed index set `U`.
  let _ : PreservesLimitsOfSize.{w, w} F := preservesLimitsOfSize_shrink F
  let h : PreservesLimitsOfShape (Discrete U) F :=
    PreservesLimitsOfSize.preservesLimitsOfShape (F := F)
  exact h.preservesLimit

/-- Helper for Lemma 6.16.4: the `x`-coordinate of the product map is the canonical leg from `U`
to the filtered stalk at `x`. -/
abbrev filtered_stalk_leg (ℋ : X.Sheaf C) (U : Opens X) (x : U) :
    ℋ.presheaf.obj (op U) ⟶ filteredStalk x.1 ℋ.presheaf :=
  letI : HasFilteredColimitsOfSize.{w, w} C :=
    IsAlgebraicStructure.toHasFilteredColimitsOfSize (C := C) (F := F)
  letI : HasColimit (((OpenNhds.inclusion x.1).op) ⋙ ℋ.presheaf) :=
    filtered_stalk_colimit (ℋ := ℋ) (x := x.1)
  (show ℋ.presheaf.obj (op U) ⟶ filteredStalk x.1 ℋ.presheaf from
    colimit.ι (((OpenNhds.inclusion x.1).op) ⋙ ℋ.presheaf) (op ⟨U, x.2⟩))

/-- Helper for Lemma 6.16.4: sections over `U` map canonically to the product of their filtered
stalks over points of `U`. -/
def section_to_filtered_stalk_product (ℋ : X.Sheaf C) (U : Opens X) :
    ℋ.presheaf.obj (op U) ⟶ ∏ᶜ fun x : U ↦ filteredStalk x.1 ℋ.presheaf :=
  let Aₓ : U → C := filtered_stalk_family (F := F) ℋ U
  letI : HasProduct Aₓ := filtered_stalk_family_hasProduct (F := F) ℋ U
  Pi.lift fun x : U ↦ filtered_stalk_leg (F := F) ℋ U x

/-- Helper for Lemma 6.16.4: the colimit leg from `U` to the filtered stalk at `x` becomes the
ordinary germ map after forgetting and applying the stalk comparison isomorphism. -/
lemma filtered_stalk_leg_underlying_apply
    (ℋ : X.Sheaf C) (U : Opens X)
    (s : F.obj (ℋ.presheaf.obj (op U))) (x : U) :
    (stalkCompIso x.1 F ℋ.presheaf).hom
        (F.map (filtered_stalk_leg (F := F) ℋ U x) s) =
      TopCat.Presheaf.germ (ℋ.presheaf ⋙ F) U x.1 x.2 s := by
  letI : HasFilteredColimitsOfSize.{w, w} C :=
    IsAlgebraicStructure.toHasFilteredColimitsOfSize (C := C) (F := F)
  letI : HasColimit (((OpenNhds.inclusion x.1).op) ⋙ ℋ.presheaf) :=
    filtered_stalk_colimit (ℋ := ℋ) (x := x.1)
  -- Unfold the chosen filtered-stalk leg once; it is exactly the preserved-colimit formula.
  simpa [TopCat.Presheaf.germ, stalkCompIso, filteredStalkCompIso, filteredStalkFunctor,
    filteredStalk, filtered_stalk_leg] using
    congrFun
      (ι_preservesColimitIso_hom (G := F)
        (F := ((OpenNhds.inclusion x.1).op) ⋙ ℋ.presheaf) (j := op ⟨U, x.2⟩))
      s

/-- Helper for Lemma 6.16.4: the `x`-coordinate of the product-valued section map is the colimit
leg from `U` into the filtered stalk at `x`. -/
lemma section_to_filtered_stalk_product_coordinate_owner
    (ℋ : X.Sheaf C) (U : Opens X) (x : U) :
    section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U ≫
        Pi.π (fun y : U ↦ filteredStalk y.1 ℋ.presheaf) x =
      filtered_stalk_leg (F := F) ℋ U x := by
  -- The top horizontal map is a `Pi.lift`, so its `x`-coordinate is the chosen colimit leg.
  simpa [section_to_filtered_stalk_product] using
    (Pi.lift_π (p := fun y : U ↦ filtered_stalk_leg (F := F) ℋ U y) x)

/-- Helper for Lemma 6.16.4: after forgetting and comparing products, the coordinate of the
canonical section-to-filtered-stalk map is the usual germ map transported by `stalkCompIso`. -/
lemma section_to_filtered_stalk_product_underlying_apply
    (ℋ : X.Sheaf C) (U : Opens X)
    [PreservesLimit (Discrete.functor (filtered_stalk_family (F := F) ℋ U)) F]
    (s : F.obj (ℋ.presheaf.obj (op U))) (x : U) :
    (stalkCompIso x.1 F ℋ.presheaf).hom
        (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x
          ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom
            (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U) s))) =
      TopCat.Presheaf.germ (ℋ.presheaf ⋙ F) U x.1 x.2 s := by
  -- First rewrite the product coordinate as the image of the `x`-projection.
  rw [productUnderlying_apply]
  rw [← FunctorToTypes.map_comp_apply]
  -- Then identify that projection with the filtered-stalk colimit leg.
  rw [section_to_filtered_stalk_product_coordinate_owner (F := F) (ℋ := ℋ) U x]
  -- The remaining statement is exactly the preserved-colimit germ formula.
  exact filtered_stalk_leg_underlying_apply (F := F) (ℋ := ℋ) U s x

/-- Helper for Lemma 6.16.4: the underlying map from sections over `U` to the product of filtered
stalks is injective. -/
lemma section_to_filtered_stalk_product_underlying_injective
    (ℋ : X.Sheaf C) (U : Opens X) :
    Function.Injective (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U)) := by
  letI : PreservesLimit (Discrete.functor (filtered_stalk_family (F := F) ℋ U)) F :=
    filtered_stalk_family_preservesProduct (F := F) (ℋ := ℋ) U
  intro s t hst
  -- Compare the stalk germs of the two sections via the coordinate formula above.
  apply sectionToStalkFamily_injective ((underlyingSheaf).obj ℋ) U
  ext x
  have hs :
      (stalkCompIso x.1 F ℋ.presheaf).hom
          (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x
            ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom
              (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U) s))) =
        TopCat.Presheaf.germ (ℋ.presheaf ⋙ F) U x.1 x.2 s :=
    section_to_filtered_stalk_product_underlying_apply (F := F) (ℋ := ℋ) U s x
  have ht :
      (stalkCompIso x.1 F ℋ.presheaf).hom
          (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x
            ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom
              (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U) t))) =
        TopCat.Presheaf.germ (ℋ.presheaf ⋙ F) U x.1 x.2 t :=
    section_to_filtered_stalk_product_underlying_apply (F := F) (ℋ := ℋ) U t x
  simpa [TopCat.Presheaf.germ] using
    calc
      TopCat.Presheaf.germ (ℋ.presheaf ⋙ F) U x.1 x.2 s
          = (stalkCompIso x.1 F ℋ.presheaf).hom
              (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x
                ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom
                  (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U) s))) := by
              symm
              exact hs
      _ = (stalkCompIso x.1 F ℋ.presheaf).hom
            (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x
              ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom
                (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℋ) U) t))) := by
              exact congrArg
                ((stalkCompIso x.1 F ℋ.presheaf).hom ∘
                  Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x ∘
                  (PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom)
                hst
      _ = TopCat.Presheaf.germ (ℋ.presheaf ⋙ F) U x.1 x.2 t := ht

/-- Helper for Lemma 6.16.4: after forgetting and comparing products, the coordinate of a product
map is obtained by applying the corresponding coordinate morphism. -/
lemma filtered_stalk_product_map_underlying_apply
    {ℋ 𝒦 : X.Sheaf C} (U : Opens X)
    [PreservesLimit (Discrete.functor (filtered_stalk_family (F := F) ℋ U)) F]
    [PreservesLimit (Discrete.functor (filtered_stalk_family (F := F) 𝒦 U)) F]
    (p : ∀ x : U, filteredStalk x.1 ℋ.presheaf ⟶ filteredStalk x.1 𝒦.presheaf)
    (s : F.obj (∏ᶜ filtered_stalk_family (F := F) ℋ U)) (x : U) :
    Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 𝒦.presheaf)) x
        ((PreservesProduct.iso F (filtered_stalk_family (F := F) 𝒦 U)).hom
          (F.map (Limits.Pi.map p) s)) =
      F.map (p x)
        (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℋ.presheaf)) x
          ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℋ U)).hom s)) := by
  -- Rewrite both product comparisons to the corresponding coordinate projections.
  rw [productUnderlying_apply]
  rw [← FunctorToTypes.map_comp_apply]
  rw [Pi.map_π]
  -- The coordinate of `Pi.map p` is exactly `p x`.
  rw [FunctorToTypes.map_comp_apply]
  rw [productUnderlying_apply]

/-- Helper for Lemma 6.16.4: the textbook square over an open set commutes after forgetting to
underlying sets. -/
lemma section_to_filtered_stalk_square_commutes
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (U : Opens X)
    (ψ : ∀ x : U, filteredStalk x.1 ℱ.presheaf ⟶ filteredStalk x.1 𝒢.presheaf)
    (hψ : ∀ x : U,
      (stalkCompIso x.1 F ℱ.presheaf).hom ≫
          (stalkFunctor (Type w) x.1).map (Sheaf.homEquiv φ) ≫
          (stalkCompIso x.1 F 𝒢.presheaf).inv =
        F.map (ψ x))
    :
    F.map
        (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U ≫
          Limits.Pi.map ψ) =
      (Sheaf.homEquiv φ).app (op U) ≫
        F.map (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U) := by
  letI : PreservesLimit (Discrete.functor (filtered_stalk_family (F := F) ℱ U)) F :=
    filtered_stalk_family_preservesProduct (F := F) (ℋ := ℱ) U
  letI : PreservesLimit (Discrete.functor (filtered_stalk_family (F := F) 𝒢 U)) F :=
    filtered_stalk_family_preservesProduct (F := F) (ℋ := 𝒢) U
  funext s
  -- Compare both section images after transporting to the product of underlying stalks.
  have hprod_injective :
      Function.Injective
        ((PreservesProduct.iso F (filtered_stalk_family (F := F) 𝒢 U)).hom) :=
    (isIso_iff_bijective _).1 inferInstance |>.1
  apply hprod_injective
  ext x
  change
    Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 𝒢.presheaf)) x.as
        ((PreservesProduct.iso F (filtered_stalk_family (F := F) 𝒢 U)).hom
          (F.map
            (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U ≫ Limits.Pi.map ψ) s)) =
      Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 𝒢.presheaf)) x.as
        ((PreservesProduct.iso F (filtered_stalk_family (F := F) 𝒢 U)).hom
          (((Sheaf.homEquiv φ).app (op U) ≫
              F.map (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U)) s))
  rw [FunctorToTypes.map_comp_apply]
  rw [filtered_stalk_product_map_underlying_apply (F := F) (U := U) ψ
    (s := F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U) s) (x := x.as)]
  have hstalk_injective :
      Function.Injective ((stalkCompIso x.as.1 F 𝒢.presheaf).hom) :=
    (stalkCompIso x.as.1 F 𝒢.presheaf).toEquiv.injective
  apply hstalk_injective
  change
    (stalkCompIso x.as.1 F 𝒢.presheaf).hom
        (F.map (ψ x.as)
          (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℱ.presheaf)) x.as
            ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℱ U)).hom
              (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U) s)))) =
      (stalkCompIso x.as.1 F 𝒢.presheaf).hom
        (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 𝒢.presheaf)) x.as
          ((PreservesProduct.iso F (filtered_stalk_family (F := F) 𝒢 U)).hom
            (F.map (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U)
              ((Sheaf.homEquiv φ).app (op U) s))))
  rw [section_to_filtered_stalk_product_underlying_apply (F := F) (ℋ := 𝒢) U
    ((Sheaf.homEquiv φ).app (op U) s) x.as]
  -- Rewrite the left-hand side using the chosen stalkwise lift at `x`.
  have hψ_apply := congrFun (hψ x.as)
      (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℱ.presheaf)) x.as
        ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℱ U)).hom
          (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U) s)))
  rw [← hψ_apply]
  change
    (stalkCompIso x.as.1 F 𝒢.presheaf).hom
        ((stalkCompIso x.as.1 F 𝒢.presheaf).inv
          ((stalkFunctor (Type w) x.as.1).map (Sheaf.homEquiv φ)
            ((stalkCompIso x.as.1 F ℱ.presheaf).hom
              (Pi.π (fun y : U ↦ F.obj (filteredStalk y.1 ℱ.presheaf)) x.as
                ((PreservesProduct.iso F (filtered_stalk_family (F := F) ℱ U)).hom
                  (F.map (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U) s)))))) =
      TopCat.Presheaf.germ (𝒢.presheaf ⋙ F) U x.as.1 x.as.2
        ((Sheaf.homEquiv φ).app (op U) s)
  rw [CategoryTheory.inv_hom_id_apply]
  rw [section_to_filtered_stalk_product_underlying_apply (F := F) (ℋ := ℱ) U s x.as]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x.as.1 x.as.2 (Sheaf.homEquiv φ) s

/-- Helper for Lemma 6.16.4: for each open `U`, the underlying section map of `φ` lifts to a
`C`-morphism on sections over `U`. -/
lemma exists_section_map_of_underlying_stalkwise_structure_preserving
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (hφ : ∀ x : X, ∃ ψx : filteredStalk x ℱ.presheaf ⟶ filteredStalk x 𝒢.presheaf,
      (stalkCompIso x F ℱ.presheaf).hom ≫
          (stalkFunctor (Type w) x).map (Sheaf.homEquiv φ) ≫
          (stalkCompIso x F 𝒢.presheaf).inv =
        F.map ψx)
    (U : Opens X) :
    ∃ ψU : ℱ.presheaf.obj (op U) ⟶ 𝒢.presheaf.obj (op U),
      F.map ψU = (Sheaf.homEquiv φ).app (op U) := by
  classical
  -- Choose the stalkwise structure-preserving lifts over the points of `U`.
  let ψ : ∀ x : U, filteredStalk x.1 ℱ.presheaf ⟶ filteredStalk x.1 𝒢.presheaf :=
    fun x ↦ Classical.choose (hφ x.1)
  have hψ : ∀ x : U,
      (stalkCompIso x.1 F ℱ.presheaf).hom ≫
          (stalkFunctor (Type w) x.1).map (Sheaf.homEquiv φ) ≫
          (stalkCompIso x.1 F 𝒢.presheaf).inv =
        F.map (ψ x) := by
    intro x
    exact Classical.choose_spec (hφ x.1)
  -- The fixed-open square from the source proof gives the range inclusion needed for 6.15.4.
  have hsquare :=
    section_to_filtered_stalk_square_commutes (F := F) (φ := φ) U ψ hψ
  have hsubset :
      Set.range
          (F.map
            (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U ≫ Limits.Pi.map ψ)) ⊆
        Set.range (F.map (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U)) := by
    intro y hy
    rcases hy with ⟨s, rfl⟩
    refine ⟨(Sheaf.homEquiv φ).app (op U) s, ?_⟩
    simpa [FunctorToTypes.map_comp_apply] using (congrFun hsquare s).symm
  have hinj :=
    section_to_filtered_stalk_product_underlying_injective (F := F) (ℋ := 𝒢) U
  rcases morphism_factors_through_of_range_subset_of_injective
      F
      (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U ≫ Limits.Pi.map ψ)
      (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U)
      hinj hsubset with ⟨ψU, hψU⟩
  refine ⟨ψU, ?_⟩
  -- Cancel the injective bottom map to recover the desired section map over `U`.
  funext s
  apply hinj
  calc
    F.map (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U) (F.map ψU s)
        = F.map
            (section_to_filtered_stalk_product (F := F) (ℋ := ℱ) U ≫
              Limits.Pi.map ψ) s := by
            simpa [Functor.map_comp, FunctorToTypes.map_comp_apply] using
              (congrFun (congrArg (fun k ↦ F.map k) hψU) s).symm
    _ = F.map (section_to_filtered_stalk_product (F := F) (ℋ := 𝒢) U)
          ((Sheaf.homEquiv φ).app (op U) s) := by
            simpa [FunctorToTypes.map_comp_apply] using congrFun hsquare s

/-- Lemma 6.16.4: if, for every point `x`, the induced map on stalks of the underlying sheaves of
sets of `C`-valued sheaves is the underlying map of a morphism in `C`, then the given underlying
morphism of sheaves of sets comes from a unique morphism of sheaves of algebraic structures. -/
theorem existsUnique_sheaf_hom_of_underlying_stalkwise_structure_preserving
    (φ : (underlyingSheaf).obj ℱ ⟶ (underlyingSheaf).obj 𝒢)
    (hφ : ∀ x : X, ∃ ψx : filteredStalk x ℱ.presheaf ⟶ filteredStalk x 𝒢.presheaf,
      (stalkCompIso x F ℱ.presheaf).hom ≫
          (stalkFunctor (Type w) x).map (Sheaf.homEquiv φ) ≫
          (stalkCompIso x F 𝒢.presheaf).inv =
        F.map ψx) :
    ∃! Φ : ℱ ⟶ 𝒢,
      (underlyingSheaf).map Φ = φ := by
  -- First lift the underlying section map over each open set using the filtered-stalk diagram.
  let hsections : ∀ U : Opens X, ∃ ψU : ℱ.presheaf.obj (op U) ⟶ 𝒢.presheaf.obj (op U),
      F.map ψU = (Sheaf.homEquiv φ).app (op U) :=
    exists_section_map_of_underlying_stalkwise_structure_preserving
      (F := F) (φ := φ) hφ
  -- Then assemble those sectionwise lifts into a sheaf morphism.
  let ψ : ℱ.presheaf ⟶ 𝒢.presheaf :=
    sectionwise_lift_to_presheaf_hom (F := F) (φ := φ) hsections
  let Φ : ℱ ⟶ 𝒢 := Sheaf.homEquiv.symm ψ
  refine ⟨Φ, ?_, ?_⟩
  · -- The constructed sheaf morphism forgets to `φ` by construction of the sectionwise lifts.
    simpa [Φ, ψ] using
      constructed_lift_recovers_underlying_map (F := F) (φ := φ) hsections
  · intro Φ' hΦ'
    -- Faithfulness of the underlying-sheaf functor turns equality after forgetting into equality.
    exact (underlyingSheaf).map_injective <| by
      calc
        (underlyingSheaf).map Φ' = φ := hΦ'
        _ = (underlyingSheaf).map Φ := by
          symm
          simpa [Φ, ψ] using
            constructed_lift_recovers_underlying_map (F := F) (φ := φ) hsections

end
