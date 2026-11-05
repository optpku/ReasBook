module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_42_3
public import stacks_project.Chap07.Lemma_7_28_5.TypeSheafification
public import stacks_project.Chap07.Lemma_7_42_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [K.WEqualsLocallyBijective (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/-- Helper for Lemma 7.42.5: a connected colimit of singleton-valued `Type`-diagrams is itself a
singleton. -/
private lemma unique_cocone_point_of_connected_types_diagram
    (I : Type u₃) [SmallCategory I] [IsConnected I]
    {G : I ⥤ Type w} (c : Cocone G) (hc : IsColimit c)
    (hG : ∀ i, Nonempty (Unique (G.obj i))) :
    Nonempty (Unique c.pt) := by
  classical
  let e : G ≅ CategoryTheory.Limits.Types.constPUnitFunctor I := NatIso.ofComponents
    (fun i ↦
      { hom := fun _ ↦ PUnit.unit
        inv := fun _ ↦ (Classical.choice (hG i)).default
        hom_inv_id := by
          funext x
          exact ((Classical.choice (hG i)).uniq x).symm
        inv_hom_id := by
          funext x
          cases x
          rfl })
    (fun {X Y} f ↦ by
      ext x
      rfl)
  let cPUnit : Cocone G := (Cocone.precompose
    e.hom).obj (CategoryTheory.Limits.Types.pUnitCocone I)
  have hcPUnit : IsColimit cPUnit := by
    -- Replace the singleton-valued diagram by the constant `PUnit` diagram and transport the
    -- canonical connected colimit cocone along that natural isomorphism.
    exact (IsColimit.precomposeHomEquiv e (CategoryTheory.Limits.Types.pUnitCocone I)).symm
      (CategoryTheory.Limits.Types.isColimitPUnitCocone I)
  let e : c.pt ≅ PUnit := hc.coconePointUniqueUpToIso hcPUnit
  exact ⟨e.toEquiv.unique⟩

/-- Helper for Lemma 7.42.5: a sheaf-theoretically empty object has a unique section in any
`Type`-valued sheaf. -/
private lemma unique_sections_of_isSheafTheoreticallyEmpty
    (V : D) (hV : K.IsSheafTheoreticallyEmpty V) (ℱ : Sheaf K (Type w)) :
    Nonempty (Unique (ℱ.obj.obj (op V))) := by
  -- Rewrite sheaf-theoretic emptiness as the covering condition for the bottom sieve.
  rw [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hV
  -- The sheaf condition for the empty cover forces the section type to be terminal.
  exact ⟨CategoryTheory.Limits.Types.isTerminalEquivUnique _ (ℱ.isTerminalOfBotCover V hV)⟩

/-- Helper for Lemma 7.42.5: the point of a presheaf colimit cocone is singleton-valued on every
sheaf-theoretically empty object. -/
private lemma presheaf_colimit_point_unique_of_isSheafTheoreticallyEmpty
    (I : Type u₃) [SmallCategory I] [FinCategory I] [IsConnected I]
    {F : I ⥤ Sheaf K (Type w)}
    (E : Cocone (F ⋙ sheafToPresheaf K (Type w))) (hE : IsColimit E) :
    ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (E.pt.obj (op V))) := by
  intro V hV
  let eV : (Dᵒᵖ ⥤ Type w) ⥤ Type w := (CategoryTheory.evaluation Dᵒᵖ (Type w)).obj (op V)
  let EV : Cocone (F ⋙ sheafToPresheaf K (Type w) ⋙ eV) := Functor.mapCocone eV E
  letI : PreservesColimitsOfShape I eV := inferInstance
  have hEV : IsColimit EV := isColimitOfPreserves eV hE
  -- Evaluate the colimit cocone at `V` and reduce to the connected singleton colimit fact.
  simpa [eV, EV] using
    (unique_cocone_point_of_connected_types_diagram
      (I := I) EV hEV
      (fun i ↦ unique_sections_of_isSheafTheoreticallyEmpty
        (K := K) V hV (F.obj i)))

/-- Helper for Lemma 7.42.5: mapping the sheafified presheaf colimit cocone along `u_*` rewrites
its `i`-th leg as whiskering the underlying presheaf map. -/
private lemma map_sheafify_cocone_leg_eq_whisker_toSheafify
    (I : Type u₃) [SmallCategory I]
    {F : I ⥤ Sheaf K (Type w)}
    (E : Cocone (F ⋙ sheafToPresheaf K (Type w))) (i : I) :
    ((Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
        (Sheaf.sheafifyCocone E)).ι.app i).hom =
      Functor.whiskerLeft u.op (E.ι.app i ≫ toSheafify K E.pt) := by
  -- Evaluate both sides objectwise and use the standard formula for the sheafified cocone leg.
  ext X x
  change (((Sheaf.sheafifyCocone E).ι.app i).hom.app (u.op.obj X) x =
      (E.ι.app i ≫ toSheafify K E.pt).app (u.op.obj X) x)
  rw [Sheaf.sheafifyCocone_ι_app_val]

/-- Helper for Lemma 7.42.5: whiskering a presheaf cocone along `u.op` sends the cocone point to
the whiskered presheaf point. -/
private lemma whiskered_presheaf_colimit_cocone_pt
    (I : Type u₃) [SmallCategory I]
    {F : I ⥤ Sheaf K (Type w)}
    (E : Cocone (F ⋙ sheafToPresheaf K (Type w))) :
    (Functor.mapCocone ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) E).pt = u.op ⋙ E.pt := by
  -- `Functor.mapCocone` computes its point by whiskering the original cocone point.
  simp [Functor.mapCocone_pt]

/-- Helper for Lemma 7.42.5: mapping the sheafified presheaf colimit cocone along `u_*` sends the
point to the pushforward of the sheafified presheaf colimit point. -/
private lemma mapped_sheafify_colimit_cocone_pt
    (I : Type u₃) [SmallCategory I]
    {F : I ⥤ Sheaf K (Type w)}
    (E : Cocone (F ⋙ sheafToPresheaf K (Type w))) :
    (Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
      (Sheaf.sheafifyCocone E)).pt =
        (presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj E.pt := by
  -- Mapping a cocone changes only the point object, and `Sheaf.sheafifyCocone` uses
  -- `presheafToSheaf` on the underlying presheaf point.
  simp [Functor.mapCocone_pt, Sheaf.sheafifyCocone]

/-- Helper for Lemma 7.42.5: after composing with the 7.42.4 comparison morphism, the sheafified
whiskered `i`-th leg collapses to the whiskered naturality identity for `toSheafify`. -/
private lemma sheafify_whiskered_leg_via_comparison
    (I : Type u₃) [SmallCategory I]
    {F : I ⥤ Sheaf K (Type w)}
    (E : Cocone (F ⋙ sheafToPresheaf K (Type w))) (i : I) :
    (toSheafify J ((u.sheafPushforwardContinuous (Type w) J K).obj (F.obj i)).obj ≫
        sheafifyMap J (𝟙 ((u.sheafPushforwardContinuous (Type w) J K).obj (F.obj i)).obj) ≫
        sheafifyMap J (Functor.whiskerLeft u.op (E.ι.app i))) ≫
        sheafifyLift J (Functor.whiskerLeft u.op (toSheafify K E.pt))
          ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj
            E.pt).property =
      Functor.whiskerLeft u.op (toSheafify K (F.obj i).obj) ≫
        Functor.whiskerLeft u.op (sheafifyMap K (E.ι.app i)) := by
  -- The comparison from `u_*` to the whiskered presheaf functor is definitionally the identity.
  simp only [sheafifyMap_id, Category.id_comp, Category.assoc]
  -- Collapse the middle comparison to a single `sheafifyLift`.
  rw [sheafifyMap_sheafifyLift]
  -- Evaluate the resulting sheafification lift on the source unit.
  rw [toSheafify_sheafifyLift]
  -- The remaining identity is exactly the whiskered naturality of `toSheafify`.
  ext X x
  let h :=
    congrArg (fun τ ↦ τ.app (u.op.obj X))
      (toSheafify_naturality K (E.ι.app i))
  exact congrFun h x

/-- Helper for Lemma 7.42.5: the 7.42.4 comparison map identifies the mapped sheaf colimit cocone
with the sheafification of the whiskered presheaf colimit cocone. -/
private noncomputable def sheafify_whiskered_colimit_cocone_iso
    (I : Type u₃) [SmallCategory I] [IsConnected I]
    {F : I ⥤ Sheaf K (Type w)}
    (E : Cocone (F ⋙ sheafToPresheaf K (Type w)))
    (hP : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (E.pt.obj (op V)))) :
    Sheaf.sheafifyCocone
        ((Cocone.precompose
          (Functor.isoWhiskerLeft F
            (u.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) J K)).hom).obj
          (Functor.mapCocone ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) E)) ≅
      Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K) (Sheaf.sheafifyCocone E) := by
  let EwPresheaf : Cocone
      (F ⋙ sheafToPresheaf K (Type w) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) :=
    Functor.mapCocone ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) E
  let Ew :
      Cocone ((F ⋙ u.sheafPushforwardContinuous (Type w) J K) ⋙ sheafToPresheaf J (Type w)) :=
    (Cocone.precompose
      (Functor.isoWhiskerLeft F
        (u.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) J K)).hom).obj
      EwPresheaf
  let α :=
    sheafifyLift J (Functor.whiskerLeft u.op (toSheafify K E.pt))
      ((presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj E.pt).property
  have hα : IsIso α := by
    -- Apply Lemma 7.42.4 to the presheaf colimit point `E.pt`.
    simpa [α] using
      (Functor.pushforwardContinuousSheafificationComparison_isIso_of_isAlmostCocontinuous
        (u := u) (J := J) (K := K) E.pt hP)
  let _ : IsIso α := hα
  have hEwPresheaf_pt : EwPresheaf.pt = u.op ⋙ E.pt := by
    -- The whiskered presheaf cocone keeps the source colimit point and precomposes by `u.op`.
    simpa [EwPresheaf] using
      whiskered_presheaf_colimit_cocone_pt (u := u) (J := J) (K := K) (I := I) E
  have hleftPoint :
      (Sheaf.sheafifyCocone Ew).pt = (presheafToSheaf J (Type w)).obj (u.op ⋙ E.pt) := by
    simp [Sheaf.sheafifyCocone, Ew, hEwPresheaf_pt]
  have hrightPoint :
      (Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
          (Sheaf.sheafifyCocone E)).pt =
        (presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj E.pt := by
    -- The mapped sheaf colimit cocone uses the pushforward of the sheafified presheaf colimit.
    simpa using
      mapped_sheafify_colimit_cocone_pt (u := u) (J := J) (K := K) (I := I) E
  let leftPoint :
      (Sheaf.sheafifyCocone Ew).pt ≅ (presheafToSheaf J (Type w)).obj (u.op ⋙ E.pt) :=
    eqToIso hleftPoint
  let rightPoint :
      (Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
          (Sheaf.sheafifyCocone E)).pt ≅
        (presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj E.pt :=
    eqToIso hrightPoint
  let eα : sheafify J (u.op ⋙ E.pt) ≅ u.op ⋙ sheafify K E.pt := asIso α
  let middlePoint :
      (presheafToSheaf J (Type w)).obj (u.op ⋙ E.pt) ≅
        (presheafToSheaf K (Type w) ⋙ u.sheafPushforwardContinuous (Type w) J K).obj E.pt :=
    { hom := ObjectProperty.homMk eα.hom
      inv := ObjectProperty.homMk eα.inv
      hom_inv_id := by
        apply Sheaf.hom_ext
        exact eα.hom_inv_id
      inv_hom_id := by
        apply Sheaf.hom_ext
        exact eα.inv_hom_id }
  let ePt :
      (Sheaf.sheafifyCocone Ew).pt ≅
        (Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
          (Sheaf.sheafifyCocone E)).pt :=
    leftPoint ≪≫ middlePoint ≪≫ rightPoint.symm
  -- Use the comparison map as the point isomorphism and verify compatibility with each cocone leg.
  refine Cocone.ext ePt ?_
  intro i
  apply Sheaf.hom_ext
  change ((Sheaf.sheafifyCocone Ew).ι.app i).hom ≫ ePt.hom.hom =
      ((Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
        (Sheaf.sheafifyCocone E)).ι.app i).hom
  -- Both legs are the whiskered presheaf map `E.ι.app i ≫ toSheafify K E.pt`.
  change ((Sheaf.sheafifyCocone Ew).ι.app i).hom ≫ α =
      ((Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
        (Sheaf.sheafifyCocone E)).ι.app i).hom
  rw [Sheaf.sheafifyCocone_ι_app_val, map_sheafify_cocone_leg_eq_whisker_toSheafify
    (u := u) (J := J) (K := K) (I := I) E i]
  -- Route correction: normalize the leg through the comparison morphism before using naturality.
  simp [α, Ew, EwPresheaf, Functor.sheafPushforwardContinuousCompSheafToPresheafIso,
    Category.assoc]
  exact
    sheafify_whiskered_leg_via_comparison
      (u := u) (J := J) (K := K) (I := I) E i

/- Domain-style sampling for Lemma 7.42.5:
- primary domain: direct-image functors on sheaves of types for continuous, almost cocontinuous
  functors of sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `PreservesColimitsOfShape`,
  `Functor.IsAlmostCocontinuous`,
  `Limits.preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project statement that `u_*` commutes with finite connected
  colimits, hence with pushouts and coequalizers;
  `core/canonical`: the owner property
  `PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K)`;
  `bridge/view`: the specializations to `WalkingCospan` and `WalkingParallelPair`.

Primitive data are only the site functor `u`, the two topologies, the weak sheafification
hypotheses, and the continuity/almost-cocontinuity assumptions. The pushout and coequalizer
statements are derived API from the finite-connected-colimit owner and should remain companion
specializations rather than parallel root declarations. -/

-- Proof sketch: for a finite connected diagram of sheaves on `(D, K)`, compute its colimit as the
-- sheafification of the presheaf colimit. Finite connected colimits of singleton sets are
-- singleton, so Lemma `7.42.4` applies to the underlying presheaf colimit and identifies pulling
-- back after sheafification with sheafifying after pullback. Precomposition on presheaves preserves
-- all colimits, hence the direct-image functor on sheaves preserves the original finite connected
-- colimit.
private instance sheafPushforwardContinuous_preservesFiniteConnectedColimits
    (I : Type u₃) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K) := by
  classical
  refine ⟨?_⟩
  intro F
  let E : Cocone (F ⋙ sheafToPresheaf K (Type w)) :=
    colimit.cocone (F ⋙ sheafToPresheaf K (Type w))
  let hE : IsColimit E := colimit.isColimit (F ⋙ sheafToPresheaf K (Type w))
  let EwPresheaf : Cocone
      (F ⋙ sheafToPresheaf K (Type w) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) :=
    Functor.mapCocone ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) E
  let Ew :
      Cocone ((F ⋙ u.sheafPushforwardContinuous (Type w) J K) ⋙ sheafToPresheaf J (Type w)) :=
    (Cocone.precompose
      (Functor.isoWhiskerLeft F
        (u.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) J K)).hom).obj
      EwPresheaf
  let hEwPresheaf : IsColimit EwPresheaf :=
    isColimitOfPreserves ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op) hE
  let hEw : IsColimit Ew :=
    (IsColimit.precomposeHomEquiv
      (Functor.isoWhiskerLeft F
        (u.sheafPushforwardContinuousCompSheafToPresheafIso (Type w) J K)) EwPresheaf).symm
      hEwPresheaf
  have hP :
      ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (E.pt.obj (op V))) :=
    presheaf_colimit_point_unique_of_isSheafTheoreticallyEmpty
      (K := K) (I := I) E hE
  let e :
      Sheaf.sheafifyCocone Ew ≅
        Functor.mapCocone (u.sheafPushforwardContinuous (Type w) J K)
          (Sheaf.sheafifyCocone E) :=
    sheafify_whiskered_colimit_cocone_iso
      (u := u) (J := J) (K := K) (I := I) E hP
  -- Sheaf colimits are sheafifications of presheaf colimits, and 7.42.4 identifies those
  -- colimits after whiskering with the mapped sheaf colimit cocone.
  exact preservesColimit_of_preserves_colimit_cocone
    (Sheaf.isColimitSheafifyCocone E hE)
    (IsColimit.ofIsoColimit (Sheaf.isColimitSheafifyCocone Ew hEw) e)

end

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

/-- Lemma 7.42.5: if `u : (C, J) ⥤ (D, K)` is continuous and almost cocontinuous, then the
direct-image functor `u^s = u^p : Sh(K, Type w) ⥤ Sh(J, Type w)` preserves finite connected
colimits. -/
theorem sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [u.IsAlmostCocontinuous J K]
    [UnivLE.{max u₂ v₂, w}]
    (I : Type u₃) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K) := by
  -- Proof comment: the internal colimit-comparison proof uses the standard `W = locally
  -- bijective` package on `Type w`; the universe side condition makes the target-site concrete
  -- plus-plus owners available.
  let _ : K.WEqualsLocallyBijective (Type w) :=
    CategoryTheory.type_WEqualsLocallyBijective_of_hasWeakSheafify (L := K)
  infer_instance

-- Proof sketch: `WalkingSpan` is a finite connected indexing category, so this is the
-- specialization of the finite-connected-colimit preservation statement to pushout diagrams.
/-- Under the continuous and almost cocontinuous hypotheses, the direct-image functor on sheaves
of sets preserves pushouts. -/
theorem sheafPushforwardContinuous_preservesPushouts_of_isAlmostCocontinuous
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [u.IsAlmostCocontinuous J K]
    [UnivLE.{max u₂ v₂, w}]
    :
    PreservesColimitsOfShape WalkingSpan
      (u.sheafPushforwardContinuous (Type w) J K) :=
  sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous
    u J K WalkingSpan

-- Proof sketch: `WalkingParallelPair` is a finite connected indexing category, so this is the
-- specialization of the finite-connected-colimit preservation statement to coequalizer diagrams.
/-- Under the continuous and almost cocontinuous hypotheses, the direct-image functor on sheaves
of sets preserves coequalizers. -/
theorem sheafPushforwardContinuous_preservesCoequalizers_of_isAlmostCocontinuous
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [u.IsAlmostCocontinuous J K]
    [UnivLE.{max u₂ v₂, w}]
    :
    PreservesColimitsOfShape WalkingParallelPair
      (u.sheafPushforwardContinuous (Type w) J K) :=
  sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous
    u J K WalkingParallelPair

end

end CategoryTheory.Functor
