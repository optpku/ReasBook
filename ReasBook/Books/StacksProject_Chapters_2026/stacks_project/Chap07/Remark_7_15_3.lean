module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Types
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.Limits
open CategoryTheory.Types

universe u

noncomputable section

namespace CategoryTheory.ObjectProperty

/-
Domain-style sampling for Remark 7.15.3:
- primary domain: sheaves on full subcategories of `Type` equipped with the pulled-back jointly
  surjective topology;
- sampled owner API:
  `typesGrothendieckTopology`,
  `Functor.inducedTopology`,
  `typeEquiv`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source/core/bridge triage:
  `source-facing`: the jointly surjective site on `S.FullSubcategory`;
  `core/canonical`: the induced-topology owner `S.ι.inducedTopology typesGrothendieckTopology`,
  together with `typeEquiv` and the dense-subsite comparison for
  `S.ι.sheafPushforwardContinuous`;
  `bridge/view`: the source-facing topology
  `(jointlySurjectivePrecoverage.comap S.ι).toGrothendieck` and the resulting set-to-sheaf
  functor.

Primitive data are the inclusion `S.ι` and the source-facing jointly surjective precoverage on the
full subcategory. The canonical comparison machinery is organized around
`S.ι.inducedTopology typesGrothendieckTopology`, so the local topology/functor names should be
thin bridges to that owner rather than parallel replacements for it.
-/

section

variable (S : ObjectProperty (Type u))

/-- The pulled-back jointly surjective topology on `S.FullSubcategory`. -/
abbrev fullSubcategoryJointlySurjectiveTopology : GrothendieckTopology S.FullSubcategory :=
  (jointlySurjectivePrecoverage.comap S.ι).toGrothendieck

/-- If `S` contains a singleton object, the inclusion `S.FullSubcategory ⥤ Type` is cover-dense
for the jointly surjective topology on `Type`. -/
theorem fullSubcategoryInclusion_isCoverDense_of_singleton_object
    (e : S.FullSubcategory) (he : Unique e.obj) :
    S.ι.IsCoverDense typesGrothendieckTopology := by
  refine ⟨fun X x ↦ ?_⟩
  refine ⟨⟨e, (↾fun _ ↦ he.default), (↾fun _ ↦ x), ?_⟩⟩
  funext y
  simp

/-- If `S` contains a nonempty object, the inclusion `S.FullSubcategory ⥤ Type` is cover-dense
for the jointly surjective topology on `Type`. -/
theorem fullSubcategoryInclusion_isCoverDense_of_nonempty_object
    (e : S.FullSubcategory) (he : Nonempty e.obj) :
    S.ι.IsCoverDense typesGrothendieckTopology := by
  rcases he with ⟨y⟩
  refine ⟨fun X x ↦ ?_⟩
  -- The constant map from a chosen point of `e` hits the prescribed point `x`.
  refine ⟨⟨e, (↾fun _ ↦ y), (↾fun _ ↦ x), ?_⟩⟩
  funext z
  rfl

/-- Helper for Remark 7.15.3: for a presieve on a type, the generated sieve is covering for
`typesGrothendieckTopology` exactly when the original family is jointly surjective. -/
theorem typesGrothendieckTopology_generate_mem_iff_jointly_surjective
    {X : Type u} (R : Presieve X) :
    Sieve.generate R ∈ typesGrothendieckTopology X ↔ R ∈ jointlySurjectivePrecoverage X := by
  constructor
  · intro hR
    -- A covering generated sieve contains a singleton-valued arrow through each point.
    rw [Types.mem_jointlySurjectivePrecoverage_iff]
    intro x
    rcases hR x with ⟨Y, h, g, hg, hgx⟩
    refine ⟨Y, g, hg, ⟨h PUnit.unit, ?_⟩⟩
    simpa using congrFun hgx PUnit.unit
  · intro hR
    -- A jointly surjective presieve already contains a map whose image hits each point.
    rw [Types.mem_jointlySurjectivePrecoverage_iff] at hR
    intro x
    obtain ⟨Y, g, hg, ⟨y, rfl⟩⟩ := hR x
    exact ⟨Y, (fun _ : PUnit => y), g, hg, rfl⟩

/-- Helper for Remark 7.15.3: a sieve on a type is covering for
`typesGrothendieckTopology` exactly when its arrows are jointly surjective. -/
theorem typesGrothendieckTopology_mem_iff_jointly_surjective
    {X : Type u} (T : Sieve X) :
    T ∈ typesGrothendieckTopology X ↔ T.arrows ∈ jointlySurjectivePrecoverage X := by
  constructor
  · intro hT
    -- The singleton map onto a point belongs to the sieve exactly when the sieve covers that point.
    rw [Types.mem_jointlySurjectivePrecoverage_iff]
    intro x
    refine ⟨PUnit, (fun _ : PUnit => x), hT x, ⟨PUnit.unit, rfl⟩⟩
  · intro hT
    -- Joint surjectivity gives an arrow in the sieve whose image contains the prescribed point.
    rw [Types.mem_jointlySurjectivePrecoverage_iff] at hT
    intro x
    rcases hT x with ⟨Y, f, hf, ⟨y, rfl⟩⟩
    simpa using T.downward_closed hf (fun _ : PUnit => y)

/-- Under cover density, the source-facing jointly surjective topology on `S.FullSubcategory`
agrees with the canonical induced topology coming from the inclusion into `Type`. -/
theorem fullSubcategoryJointlySurjectiveTopology_eq_inducedTopology
    [HasPullbacks S.FullSubcategory]
    [S.ι.IsCoverDense typesGrothendieckTopology] :
    fullSubcategoryJointlySurjectiveTopology S = S.ι.inducedTopology typesGrothendieckTopology := by
  classical
  -- Route correction: instead of chasing arbitrary pullback refinements, compare both topologies
  -- directly through the pointwise jointly-surjective characterization on `Type`.
  apply le_antisymm
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro U R hR
    have hmap : Presieve.map S.ι R ∈ jointlySurjectivePrecoverage (S.ι.obj U) := by
      -- The comap generator becomes a genuinely jointly-surjective family after applying `S.ι`.
      rwa [Precoverage.mem_comap_iff] at hR
    -- The generated image sieve is covering on `Type`, so the original presieve is covering for
    -- the induced topology.
    rw [GrothendieckTopology.mem_toPrecoverage_iff, Functor.mem_inducedTopology_sieves_iff,
      ← Sieve.generate_map_eq_functorPushforward,
      typesGrothendieckTopology_generate_mem_iff_jointly_surjective]
    exact hmap
  · intro U T hT
    -- Covering in the induced topology means the pushed-forward sieve is jointly surjective on
    -- the ambient type.
    rw [Functor.mem_inducedTopology_sieves_iff,
      typesGrothendieckTopology_mem_iff_jointly_surjective] at hT
    rw [Types.mem_jointlySurjectivePrecoverage_iff] at hT
    have hcover :
        ∀ x : U.obj, ∃ (Z : S.FullSubcategory) (f : Z ⟶ U), T f ∧ x ∈ Set.range (S.ι.map f) := by
      intro x
      obtain ⟨Y, g, hg, hx⟩ := hT x
      rcases hx with ⟨y, rfl⟩
      rcases hg with ⟨Z, f, h, hf, rfl⟩
      exact ⟨Z, f, hf, ⟨h y, rfl⟩⟩
    choose Z f hf hx using hcover
    let R : Presieve U := Presieve.ofArrows Z f
    have hR : R ∈ jointlySurjectivePrecoverage.comap S.ι U := by
      -- The chosen source arrows already hit every point of `U`.
      rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
      intro x
      exact ⟨x, hx x⟩
    refine GrothendieckTopology.superset_covering
      (J := fullSubcategoryJointlySurjectiveTopology S) (X := U) (S := Sieve.generate R)
      (R := T) ?_ ?_
    · -- The generated sieve stays inside `T` because each chosen generator lies in `T`.
      rw [Sieve.generate_le_iff]
      intro Z' g hg
      simpa [hg.eq_eqToHom_comp_hom_idx] using
        T.downward_closed (hf hg.idx) (eqToHom hg.obj_idx.symm)
    · exact Precoverage.generate_mem_toGrothendieck hR

section

variable [HasPullbacks S.FullSubcategory]

/-- Helper for Remark 7.15.3: the canonical presheaf `U ↦ (U.obj → E)` is a sheaf on the pulled
back jointly surjective site. -/
theorem fullSubcategorySetDirectImage_isSheaf
    (E : Type u) :
    Presheaf.IsSheaf (fullSubcategoryJointlySurjectiveTopology S)
      (S.ι.op ⋙ ((typeEquiv.functor).obj E).obj) := by
  classical
  by_cases hnonempty : ∃ e : S.FullSubcategory, Nonempty e.obj
  · rcases hnonempty with ⟨e, he⟩
    letI : S.ι.IsCoverDense typesGrothendieckTopology :=
      fullSubcategoryInclusion_isCoverDense_of_nonempty_object S e he
    have hInduced :
        Presheaf.IsSheaf (S.ι.inducedTopology typesGrothendieckTopology)
          (S.ι.op ⋙ ((typeEquiv.functor).obj E).obj) := by
      -- In the nonempty case, the pulled-back topology agrees with the owner induced topology.
      simpa using S.ι.op_comp_isSheaf (S.ι.inducedTopology typesGrothendieckTopology)
        typesGrothendieckTopology ((typeEquiv.functor).obj E)
    -- Transport the owner sheaf condition along the topology identification.
    rw [fullSubcategoryJointlySurjectiveTopology_eq_inducedTopology S]
    exact hInduced
  · have hEmpty : ∀ U : S.FullSubcategory, IsEmpty U.obj := by
      intro U
      by_contra hU
      exact hnonempty ⟨U, not_isEmpty_iff.mp hU⟩
    let P : S.FullSubcategoryᵒᵖ ⥤ Type u := S.ι.op ⋙ ((typeEquiv.functor).obj E).obj
    have hIso : P ≅ (Functor.const S.FullSubcategoryᵒᵖ).obj PUnit := by
      refine NatIso.ofComponents ?_ ?_
      · intro U
        -- If every object is empty, then every section space `U.obj → E` is terminal.
        let hU : IsEmpty (unop U).obj := hEmpty (unop U)
        refine
          { hom := fun _ ↦ PUnit.unit
            inv := fun _ ↦ fun x ↦ False.elim (hU.false x)
            hom_inv_id := ?_
            inv_hom_id := ?_ }
        · funext x y
          exact False.elim (hU.false y)
        · funext x
          cases x
          rfl
      · intro U V f
        funext x
        rfl
    -- The empty case reduces to the terminal presheaf, which is a sheaf on every site.
    exact (Presheaf.isSheaf_of_iso_iff
        (J := fullSubcategoryJointlySurjectiveTopology S) hIso).2
      (Presheaf.isSheaf_of_isTerminal (fullSubcategoryJointlySurjectiveTopology S)
        Types.isTerminalPUnit)

/-- The canonical direct-image functor `E ↦ (U ↦ (U → E))` from sets to sheaves on the surjective
site attached to a full subcategory of `Type`. -/
abbrev fullSubcategorySetDirectImage :
    Type u ⥤ Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u) :=
  ObjectProperty.lift (Presheaf.IsSheaf (fullSubcategoryJointlySurjectiveTopology S))
    (typeEquiv.functor ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj S.ι.op)
    (fun E ↦ fullSubcategorySetDirectImage_isSheaf S E)

/-- On an object `U` of the full subcategory, the direct image of `E` is the set of maps
`U ⟶ E`, i.e. functions `U.obj → E`. -/
theorem fullSubcategorySetDirectImage_obj_obj
    (E : Type u) (U : S.FullSubcategory) :
    ((fullSubcategorySetDirectImage S).obj E).obj.obj (op U) = (U.obj ⟶ E) := by
  exact typeEquiv_functor_obj_obj_obj E (op U.obj)

attribute [simp] fullSubcategorySetDirectImage_obj_obj

end

section

theorem fullSubcategorySetInverseImageOfEndomorphism_map_mem
    {e : S.FullSubcategory} (φ : e ⟶ e)
    {F G : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u)} (η : F ⟶ G)
    {x : F.obj.obj (op e)}
    (hx : x ∈ Set.range (F.obj.map φ.op)) :
    η.hom.app (op e) x ∈ Set.range (G.obj.map φ.op) := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨η.hom.app (op e) y, ?_⟩
  simpa using (congrFun (η.hom.naturality φ.op) y).symm

/-- For an endomorphism `φ : e ⟶ e`, this inverse-image functor sends a sheaf `F` to the image
`Im(F(φ))`, represented in Lean as the subtype `Set.range (F.obj.map φ.op)`. -/
def fullSubcategorySetInverseImageOfEndomorphism
    {e : S.FullSubcategory} (φ : e ⟶ e) :
    Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u) ⥤ Type u where
  obj F := ↥(Set.range (F.obj.map φ.op))
  map η :=
    Subtype.map (η.hom.app (op e))
      (fun a ha ↦ fullSubcategorySetInverseImageOfEndomorphism_map_mem S φ η ha)
  map_id F := by
    ext x
    rfl
  map_comp η θ := by
    ext x
    rfl

/-- Objectwise, the endomorphism-image inverse-image functor is the image `Im(F(φ))`. -/
@[simp] theorem fullSubcategorySetInverseImageOfEndomorphism_obj
    {e : S.FullSubcategory} (φ : e ⟶ e)
    (F : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u)) :
    (fullSubcategorySetInverseImageOfEndomorphism S φ).obj F = ↥(Set.range (F.obj.map φ.op)) := rfl

section

variable [HasPullbacks S.FullSubcategory]

/-- Helper for Remark 7.15.3: the direct image functor acts on a morphism by precomposition. -/
theorem fullSubcategorySetDirectImage_map_apply
    (E : Type u) {U V : S.FullSubcategory} (g : U ⟶ V) (f : V.obj → E) :
    (((fullSubcategorySetDirectImage S).obj E).obj.map g.op) f = f ∘ g := by
  -- The owner `typeEquiv` model is definitionally restriction by precomposition.
  rfl

omit [HasPullbacks S.FullSubcategory] in
/-- Helper for Remark 7.15.3: postcomposing two maps into `e` with an endomorphism whose image is
subsingleton makes them equal. -/
theorem postcomp_endomorphism_eq_of_subsingleton_range
    {e : S.FullSubcategory} (φ : e ⟶ e) (hφ : (Set.range φ).Subsingleton)
    {X : Type u} (f g : X → e.obj) :
    φ ∘ f = φ ∘ g := by
  -- Every point in the image of `φ` is equal, so the composites agree pointwise.
  funext x
  exact hφ ⟨f x, rfl⟩ ⟨g x, rfl⟩

/-- Helper for Remark 7.15.3: precomposition by an endomorphism of singleton image on a nonempty
object has image equivalent to the target set. -/
noncomputable def precomp_endomorphism_range_equiv
    {e : S.FullSubcategory} (he : Nonempty e.obj) (φ : e ⟶ e)
    (hφ : (Set.range φ).Subsingleton) (E : Type u) :
    Set.range (fun f : e.obj → E ↦ f ∘ φ) ≃ E := by
  classical
  let x₀ : e.obj := Classical.choice he
  refine
    { toFun := fun h ↦ h.1 x₀
      invFun := fun y ↦ ⟨fun _ ↦ y, ⟨fun _ ↦ y, rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    rcases h.2 with ⟨f, hf⟩
    -- Every function in the image of precomposition is constant because `φ` has singleton range.
    apply Subtype.ext
    funext x
    have hconst : φ x = φ x₀ := hφ ⟨x, rfl⟩ ⟨x₀, rfl⟩
    have hx : h.1 x = f (φ x) := (congrFun hf x).symm
    have hx₀ : h.1 x₀ = f (φ x₀) := (congrFun hf x₀).symm
    simp [hx, hx₀, hconst]
  · intro y
    rfl

omit [HasPullbacks S.FullSubcategory] in
/-- Helper for Remark 7.15.3: the constant maps from a nonempty object `e` jointly surject onto
any object `U` in the pulled-back jointly surjective precoverage. -/
theorem fullSubcategory_constant_cover_mem
    {e U : S.FullSubcategory} (he : Nonempty e.obj) :
    Presieve.ofArrows (fun _ : U.obj ↦ e)
      (fun u ↦ homMk (P := S) (↾fun _ : e.obj ↦ u)) ∈
      (jointlySurjectivePrecoverage.comap S.ι) U := by
  rcases he with ⟨y⟩
  -- Every point of `U` lies in the image of its corresponding constant map from `e`.
  rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  intro u
  exact ⟨u, y, rfl⟩

/-- Helper for Remark 7.15.3: a chosen nonempty object allows one to lift any compatible pair of
points in `Type` to an actual point of the categorical pullback in `S.FullSubcategory`. -/
theorem fullSubcategory_pullbackComparison_surjective_of_nonempty_object
    {e : S.FullSubcategory} (he : Nonempty e.obj)
    {X Y Z : S.FullSubcategory} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Function.Surjective (pullbackComparison S.ι f g) := by
  rcases he with ⟨e0⟩
  intro xy
  let fx : e ⟶ X := homMk (P := S) (fun _ : e.obj ↦ pullback.fst (S.ι.map f) (S.ι.map g) xy)
  let gy : e ⟶ Y := homMk (P := S) (fun _ : e.obj ↦ pullback.snd (S.ι.map f) (S.ι.map g) xy)
  -- The chosen point of `e` turns the target pullback point into constant maps into `X` and `Y`.
  have hfg : fx ≫ f = gy ≫ g := by
    ext t
    simpa using congrFun (pullback.condition (f := S.ι.map f) (g := S.ι.map g)) xy
  refine ⟨pullback.lift fx gy hfg e0, ?_⟩
  let lhs : PUnit ⟶ pullback (S.ι.map f) (S.ι.map g) :=
    fun _ ↦ pullbackComparison S.ι f g ((pullback.lift fx gy hfg) e0)
  let rhs : PUnit ⟶ pullback (S.ι.map f) (S.ι.map g) := fun _ ↦ xy
  -- Equality in the pullback object is reduced to equality of the two projections.
  have hfst_point :
      pullback.fst (S.ι.map f) (S.ι.map g)
          (pullbackComparison S.ι f g ((pullback.lift fx gy hfg) e0)) =
        pullback.fst (S.ι.map f) (S.ι.map g) xy := by
    have hcomp := congrFun (pullbackComparison_comp_fst (G := S.ι) (f := f) (g := g))
      ((pullback.lift fx gy hfg) e0)
    have hlift := congrFun
      (congrArg (fun k : e ⟶ X => (k : e.obj → X.obj)) (pullback.lift_fst fx gy hfg)) e0
    simpa [fx] using hcomp.trans hlift
  have hsnd_point :
      pullback.snd (S.ι.map f) (S.ι.map g)
          (pullbackComparison S.ι f g ((pullback.lift fx gy hfg) e0)) =
        pullback.snd (S.ι.map f) (S.ι.map g) xy := by
    have hcomp := congrFun (pullbackComparison_comp_snd (G := S.ι) (f := f) (g := g))
      ((pullback.lift fx gy hfg) e0)
    have hlift := congrFun
      (congrArg (fun k : e ⟶ Y => (k : e.obj → Y.obj)) (pullback.lift_snd fx gy hfg)) e0
    simpa [gy] using hcomp.trans hlift
  have hfst :
      lhs ≫ pullback.fst (S.ι.map f) (S.ι.map g) =
        rhs ≫ pullback.fst (S.ι.map f) (S.ι.map g) := by
    funext u
    exact hfst_point
  have hsnd :
      lhs ≫ pullback.snd (S.ι.map f) (S.ι.map g) =
        rhs ≫ pullback.snd (S.ι.map f) (S.ι.map g) := by
    funext u
    exact hsnd_point
  have hEq : lhs = rhs := by
    apply pullback.hom_ext hfst hsnd
  exact congrFun hEq PUnit.unit

omit [HasPullbacks S.FullSubcategory] in
/-- Helper for Remark 7.15.3: an image-valued family on the constant cover by `e` is compatible. -/
theorem constant_cover_family_compatible_of_endomorphism_image
    {e U : S.FullSubcategory} (he : Nonempty e.obj) (φ : e ⟶ e)
    (hφ : (Set.range φ).Subsingleton)
    (F : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u))
    (s : U.obj → Set.range (F.obj.map φ.op)) :
    Presieve.Arrows.Compatible F.obj
      (fun u : U.obj ↦ homMk (P := S) (↾fun _ : e.obj ↦ u))
      (fun u ↦ (s u).1) := by
  let hF : Presieve.IsSheaf (fullSubcategoryJointlySurjectiveTopology S) F.obj := by
    simpa using (isSheaf_iff_isSheaf_of_type (fullSubcategoryJointlySurjectiveTopology S) F.obj).1
      F.property
  intro u v Z g₁ g₂ hEq
  by_cases hZ : Nonempty Z.obj
  · let z0 : Z.obj := Classical.choice hZ
    have huv : u = v := by
      exact congrFun
        (congrArg (fun k : Z ⟶ U => (k : Z.obj → U.obj)) hEq) z0
    subst huv
    let t : U.obj → F.obj.obj (op e) := fun u ↦ (s u).2.choose
    have ht : ∀ u : U.obj, F.obj.map φ.op (t u) = (s u).1 := fun u ↦ (s u).2.choose_spec
    let πZ : Z.obj → (e ⟶ Z) := fun z ↦ homMk (P := S) (↾fun _ : e.obj ↦ z)
    have hπZ :
        Sieve.ofArrows (fun _ : Z.obj ↦ e) πZ ∈ fullSubcategoryJointlySurjectiveTopology S Z := by
      -- The same constant-cover argument works on the overlap object `Z`.
      simpa [Sieve.ofArrows] using
        (Precoverage.generate_mem_toGrothendieck
          (fullSubcategory_constant_cover_mem (S := S) (e := e) (U := Z) he))
    have hsepZ :
        Presieve.IsSeparatedFor F.obj
          (Presieve.ofArrows (fun _ : Z.obj ↦ e) πZ) := by
      rw [Presieve.isSeparatedFor_iff_generate]
      exact hF.isSeparated _ hπZ
    -- Equality on `Z` is checked after restricting further to the constant cover by `e`.
    apply hsepZ.ext
    rintro _ _ ⟨z⟩
    have hpost :
        (πZ z ≫ g₁) ≫ φ = (πZ z ≫ g₂) ≫ φ := by
      ext x
      exact hφ ⟨((πZ z ≫ g₁) x), rfl⟩ ⟨((πZ z ≫ g₂) x), rfl⟩
    -- On a nonempty overlap, both constant charts correspond to the same point of `U`, so we can
    -- compare the restrictions using one chosen lift of that common image value.
    calc
      F.obj.map (πZ z).op (F.obj.map g₁.op ((s u).1))
          = F.obj.map (((πZ z) ≫ g₁) ≫ φ).op (t u) := by
              rw [← ht u]
              rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
              simp [← op_comp]
      _ = F.obj.map (((πZ z) ≫ g₂) ≫ φ).op (t u) := by simp [hpost]
      _ = F.obj.map (πZ z).op (F.obj.map g₂.op ((s u).1)) := by
            rw [← ht u]
            rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
            simp [← op_comp]
  · have hEmpty : IsEmpty Z.obj := not_nonempty_iff.mp hZ
    let X : Empty → S.FullSubcategory := fun i => nomatch i
    let π : (i : Empty) → X i ⟶ Z := fun i => nomatch i
    have hπ :
        Sieve.ofArrows X π ∈ fullSubcategoryJointlySurjectiveTopology S Z := by
      have hmem :
          Presieve.ofArrows X π ∈ (jointlySurjectivePrecoverage.comap S.ι) Z := by
        rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
        intro z
        exact False.elim (hEmpty.false z)
      simpa [Sieve.ofArrows] using (Precoverage.generate_mem_toGrothendieck hmem)
    have hsep :
        Presieve.IsSeparatedFor F.obj (Presieve.ofArrows X π) := by
      rw [Presieve.isSeparatedFor_iff_generate]
      exact hF.isSeparated _ hπ
    -- If the overlap object is empty, the empty cover forces all sections on it to be equal.
    apply hsep.ext
    rintro _ _ ⟨i⟩
    cases i

/-- Helper for Remark 7.15.3: restricting a section along the constant cover by `e` identifies
sections on `U` with functions from `U` to the image of `F(φ)`. -/
noncomputable def sections_equiv_functions_to_endomorphism_image
    {e : S.FullSubcategory} (he : Nonempty e.obj) (φ : e ⟶ e)
    (hφ : (Set.range φ).Subsingleton)
    (F : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u))
    (U : S.FullSubcategory) :
    F.obj.obj (op U) ≃ (U.obj → Set.range (F.obj.map φ.op)) := by
  let hF : Presieve.IsSheaf (fullSubcategoryJointlySurjectiveTopology S) F.obj := by
    simpa using (isSheaf_iff_isSheaf_of_type (fullSubcategoryJointlySurjectiveTopology S) F.obj).1
      F.property
  let π : U.obj → (e ⟶ U) := fun u ↦ homMk (P := S) (↾fun _ : e.obj ↦ u)
  have hπ :
      Sieve.ofArrows (fun _ : U.obj ↦ e) π ∈ fullSubcategoryJointlySurjectiveTopology S U := by
    -- The chosen nonempty object `e` gives a covering by constant maps onto `U`.
    simpa [Sieve.ofArrows] using
      (Precoverage.generate_mem_toGrothendieck
        (fullSubcategory_constant_cover_mem (S := S) (e := e) (U := U) he))
  have hSheafFor :
      (Presieve.ofArrows (fun _ : U.obj ↦ e) π).IsSheafFor F.obj := by
    simpa [Sieve.ofArrows] using
      hF.isSheafFor (Presieve.ofArrows (fun _ : U.obj ↦ e) π)
        (by simpa [Sieve.ofArrows] using hπ)
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible
      (P := F.obj) (π := π)).1 hSheafFor
  let forward : F.obj.obj (op U) → (U.obj → Set.range (F.obj.map φ.op)) := fun σ u ↦ by
    have hconst : φ ≫ π u = π u := by
      ext x
      simp [π]
    refine ⟨F.obj.map (π u).op σ, ⟨F.obj.map (π u).op σ, ?_⟩⟩
    calc
      F.obj.map φ.op (F.obj.map (π u).op σ)
          = F.obj.map ((φ ≫ π u)).op σ := by
              rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      _ = F.obj.map (π u).op σ := by simp [hconst]
  let liftedFamily :
      (U.obj → Set.range (F.obj.map φ.op)) → Subtype (Presieve.Arrows.Compatible F.obj π) :=
    fun s ↦ ⟨fun u ↦ (s u).1,
      constant_cover_family_compatible_of_endomorphism_image
        (S := S) he φ hφ F s⟩
  refine
    { toFun := forward
      invFun := fun s ↦ Classical.choose (hbij.2 (liftedFamily s))
      left_inv := ?_
      right_inv := ?_ }
  · intro σ
    let y : Subtype (Presieve.Arrows.Compatible F.obj π) := liftedFamily (forward σ)
    have hy : y = Presieve.Arrows.toCompatible F.obj π σ := by
      ext u
      rfl
    exact hbij.1 <| (Classical.choose_spec (hbij.2 y)).trans hy
  · intro s
    funext u
    apply Subtype.ext
    -- Surjectivity of the compatible-family map records exactly these restrictions.
    simpa [liftedFamily] using
      congrFun
        (congrArg Subtype.val
          (Classical.choose_spec (hbij.2 (liftedFamily s)))) u

/-- Remark 7.15.3: if the full subcategory contains a nonempty object, then the canonical functor
`E ↦ (U ↦ (U → E))` gives an equivalence between sets and sheaves for the jointly surjective site
on that full subcategory. -/
theorem fullSubcategorySetDirectImage_isEquivalence_of_nonempty_object
    (e : S.FullSubcategory) (he : Nonempty e.obj) :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := by
  classical
  let x₀ : e.obj := Classical.choice he
  let φ : e ⟶ e := homMk (P := S) (↾fun _ : e.obj ↦ x₀)
  have hφ : (Set.range φ).Subsingleton := by
    intro a ha b hb
    rcases ha with ⟨y, rfl⟩
    rcases hb with ⟨z, rfl⟩
    rfl
  let G : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u) ⥤ Type u :=
    fullSubcategorySetInverseImageOfEndomorphism S φ
  let η : 𝟭 (Type u) ≅ fullSubcategorySetDirectImage S ⋙ G := by
    refine NatIso.ofComponents (fun E ↦ ?_) ?_
    · -- The unit identifies a set with the image of precomposition by the constant endomorphism.
      simpa [G, fullSubcategorySetInverseImageOfEndomorphism_obj,
        fullSubcategorySetDirectImage_map_apply] using
        Equiv.toIso (precomp_endomorphism_range_equiv (S := S) he φ hφ E).symm
    · intro E E' f
      ext y
      apply Subtype.ext
      funext x
      rfl
  let εPresheaf :
      (F : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u)) →
        ((fullSubcategorySetDirectImage S).obj (G.obj F)).obj ≅ F.obj := fun F ↦ by
          let eF := sections_equiv_functions_to_endomorphism_image
            (S := S) he φ hφ F
          let π : ∀ U : S.FullSubcategory, U.obj → (e ⟶ U) :=
            fun U u ↦ homMk (P := S) (↾fun _ : e.obj ↦ u)
          refine NatIso.ofComponents (fun U ↦ Equiv.toIso ((eF U.unop).symm)) ?_
          intro U V g
          -- Naturality is the compatibility of the section formula with restriction maps.
          funext s
          apply (eF V.unop).injective
          funext v
          apply Subtype.ext
          have hπ : π V.unop v ≫ g.unop = π U.unop (g.unop v) := by
            ext x
            rfl
          calc
            (((eF V.unop)
                (((((fullSubcategorySetDirectImage S).obj (G.obj F)).obj.map g) ≫
                    (Equiv.toIso ((eF V.unop).symm)).hom) s)) v).1
                = (s (g.unop v)).1 := by
                    exact congrArg Subtype.val
                      (congrFun
                        ((eF V.unop).apply_symm_apply
                          (((fullSubcategorySetDirectImage S).obj (G.obj F)).obj.map g s))
                        v)
            _ = F.obj.map (π U.unop (g.unop v)).op ((eF U.unop).symm s) := by
                  exact congrArg Subtype.val
                    (congrFun ((eF U.unop).apply_symm_apply s) (g.unop v)).symm
            _ = F.obj.map (π V.unop v).op (F.obj.map g ((eF U.unop).symm s)) := by
                  have hg : g ≫ (π V.unop v).op = (π U.unop (g.unop v)).op := by
                    simpa [← op_comp] using congrArg Quiver.Hom.op hπ
                  rw [← hg]
                  rw [← FunctorToTypes.map_comp_apply]
  let ε : G ⋙ fullSubcategorySetDirectImage S ≅
      𝟭 (Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u)) := by
    refine NatIso.ofComponents
      (fun F ↦ ObjectProperty.isoMk
        (Presheaf.IsSheaf (fullSubcategoryJointlySurjectiveTopology S)) (εPresheaf F)) ?_
    intro F F' α
    apply Sheaf.hom_ext
    ext U s
    let eF := sections_equiv_functions_to_endomorphism_image
      (S := S) he φ hφ F U.unop
    let eF' := sections_equiv_functions_to_endomorphism_image
      (S := S) he φ hφ F' U.unop
    let π : U.unop.obj → (e ⟶ U.unop) := fun u ↦ homMk (P := S) (↾fun _ : e.obj ↦ u)
    apply eF'.injective
    funext v
    apply Subtype.ext
    -- The two composites agree after evaluating on the constant arrow indexed by `v`.
    calc
      (eF' ((((εPresheaf F').hom.app U) (((G ⋙ fullSubcategorySetDirectImage S).map α).hom.app U s))) v).1
          = ((((G ⋙ fullSubcategorySetDirectImage S).map α).hom.app U s) v).1 := by
              exact congrArg Subtype.val
                (congrFun
                  ((eF').apply_symm_apply (((G ⋙ fullSubcategorySetDirectImage S).map α).hom.app U s))
                  v)
      _ = α.hom.app (op e) ((s v).1) := by
            rfl
      _ = α.hom.app (op e) (F.obj.map (π v).op (((εPresheaf F).hom.app U) s)) := by
            have hs :
                F.obj.map (π v).op (((εPresheaf F).hom.app U) s) = (s v).1 := by
              exact congrArg Subtype.val (congrFun ((eF).apply_symm_apply s) v)
            rw [← hs]
      _ = F'.obj.map (π v).op (α.hom.app U (((εPresheaf F).hom.app U) s)) := by
            simpa using (congrFun (α.hom.naturality (π v).op) (((εPresheaf F).hom.app U) s))
      _ = (eF' (α.hom.app U (((εPresheaf F).hom.app U) s)) v).1 := by
            rfl
  exact Functor.IsEquivalence.mk' G η ε

omit [HasPullbacks S.FullSubcategory] in
/-- Helper for Remark 7.15.3: a cover-dense full subcategory of `Type` contains a nonempty
object. -/
theorem coverDense_has_nonempty_object
    [S.ι.IsCoverDense typesGrothendieckTopology] :
    ∃ e : S.FullSubcategory, Nonempty e.obj := by
  have hcover : Sieve.coverByImage S.ι PUnit ∈ typesGrothendieckTopology PUnit := by
    exact S.ι.is_cover_of_isCoverDense typesGrothendieckTopology PUnit
  rw [typesGrothendieckTopology_mem_iff_jointly_surjective] at hcover
  obtain ⟨Y, f, hf, ⟨y, hy⟩⟩ := hcover PUnit.unit
  rcases hf with ⟨⟨e, g, h, hh⟩⟩
  exact ⟨e, ⟨g y⟩⟩

/-- Helper for Remark 7.15.3: cover density supplies a nonempty object, so the explicit
endomorphism-image quasi-inverse applies. -/
theorem fullSubcategorySetDirectImage_isEquivalence_of_cover_dense
    [S.ι.IsCoverDense typesGrothendieckTopology] :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := by
  rcases coverDense_has_nonempty_object (S := S) with ⟨e, he⟩
  -- Route correction: the dense-subsite theorem is now just a wrapper around the explicit
  -- nonempty-object equivalence proved above.
  exact fullSubcategorySetDirectImage_isEquivalence_of_nonempty_object S e he

-- Proof sketch: a singleton object is in particular nonempty, so the explicit nonempty-object
-- equivalence of Remark 7.15.3 applies immediately.
/-- If the full subcategory contains a singleton object, the canonical functor from sets to sheaves
is an equivalence, with quasi-inverse the evaluation functor
`(sheafSections (fullSubcategoryJointlySurjectiveTopology S) (Type u)).obj (op e)`.
-/
theorem fullSubcategorySetDirectImage_isEquivalence_of_singleton_object
    (e : S.FullSubcategory) (he : Unique e.obj) :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := by
  -- The singleton case is now a direct special case of the nonempty-object theorem.
  exact fullSubcategorySetDirectImage_isEquivalence_of_nonempty_object S e ⟨he.default⟩

-- Proof sketch: a constant endomorphism of the nonempty object `e` has singleton image. The
-- preceding singleton-object comparison can then be applied through the source-facing inverse
-- image functor `F ↦ Im(F(φ))`.
/-- If a nonempty object admits an endomorphism with singleton image, then Remark 7.15.3 applies.
The quasi-inverse is `fullSubcategorySetInverseImageOfEndomorphism S φ`, whose value on a sheaf is
`Im(F(φ))`. -/
theorem fullSubcategorySetDirectImage_isEquivalence_of_nonempty_endomorphism_with_singleton_range
    (e : S.FullSubcategory) (he : Nonempty e.obj) (φ : e ⟶ e)
    (hφ : (Set.range φ).Subsingleton) :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := by
  let _ := hφ
  -- Once the nonempty-object equivalence is established, the singleton-range endomorphism
  -- hypothesis becomes additional source data but does not change the equivalence statement.
  exact fullSubcategorySetDirectImage_isEquivalence_of_nonempty_object S e he

end

end

end

end CategoryTheory.ObjectProperty
