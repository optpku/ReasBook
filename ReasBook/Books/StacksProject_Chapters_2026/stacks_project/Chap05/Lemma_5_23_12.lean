module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_14_2
import stacks_project.Chap05.Lemma_5_14_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite Set TopologicalSpace

universe u

noncomputable section

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (F : Iᵒᵖ ⥤ TopCat.{u})
variable [∀ i : Iᵒᵖ, T0Space (F.obj i)]
variable [∀ i : Iᵒᵖ, QuasiSober (F.obj i)]

/-- Helper for Lemma 5.23.12: a compatible family of stage points determines a point of the
explicit inverse-limit cone `TopCat.limitCone F`. -/
def limit_cone_point_of_compatible_family
    (x : ∀ i : Iᵒᵖ, F.obj i)
    (hx : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), F.map f (x i) = x j) :
    (TopCat.limitCone F).pt :=
  ⟨x, fun {_ _} f ↦ hx f⟩

/-- Helper for Lemma 5.23.12: an irreducible closed subset of the explicit inverse limit has a
generic point obtained from the compatible family of stage generic points. -/
lemma generic_point_of_irreducible_closed_limit
    {Z : Set (TopCat.limitCone F).pt} (hZ_irred : IsIrreducible Z) (hZ_closed : IsClosed Z) :
    ∃ ξ : (TopCat.limitCone F).pt, IsGenericPoint ξ Z := by
  let C := TopCat.limitCone F
  have hC : IsLimit C := TopCat.limitConeIsLimit F
  have hπ {i j : Iᵒᵖ} (f : i ⟶ j) (x : C.pt) :
      C.π.app j x = F.map f (C.π.app i x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ g x) (C.w f).symm
  have hImage_irred (i : Iᵒᵖ) : IsIrreducible (C.π.app i '' Z) :=
    hZ_irred.image (C.π.app i) (C.π.app i).hom.continuous.continuousOn
  let ξi : ∀ i : Iᵒᵖ, F.obj i := fun i ↦ (hImage_irred i).genericPoint
  have hξi : ∀ i : Iᵒᵖ, IsGenericPoint (ξi i) (closure (C.π.app i '' Z)) := by
    intro i
    simpa [ξi] using (hImage_irred i).isGenericPoint_genericPoint_closure
  have hmap_image {i j : Iᵒᵖ} (f : i ⟶ j) :
      F.map f '' (C.π.app i '' Z) = C.π.app j '' Z := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, hπ f z⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨C.π.app i z, ⟨z, hz, rfl⟩, (hπ f z).symm⟩
  have hξ_compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), F.map f (ξi i) = ξi j := by
    intro i j f
    have hImageGeneric :
        IsGenericPoint (F.map f (ξi i)) (closure (C.π.app j '' Z)) := by
      have htmp := (hξi i).image (F.map f).hom.continuous
      have hclosure :
          closure (F.map f '' closure (C.π.app i '' Z)) = closure (C.π.app j '' Z) := by
        rw [closure_image_closure (F.map f).hom.continuous]
        simpa using congrArg closure (hmap_image (f := f))
      exact hclosure ▸ htmp
    exact IsGenericPoint.eq hImageGeneric (hξi j)
  let ξ : C.pt :=
    limit_cone_point_of_compatible_family (F := F) ξi (fun {i j} f ↦ hξ_compatible f)
  have hξ_mem_closure : ξ ∈ closure Z := by
    -- Expand an arbitrary neighborhood of `ξ` into a union of stage pullbacks, then use the stage
    -- generic point to find a point of `Z` in that same stage pullback.
    rw [mem_closure_iff]
    intro U hU hξU
    let Uo : Opens C.pt := ⟨U, hU⟩
    obtain ⟨W, hW⟩ := open_eq_iUnion_preimage_of_isLimit (F := F) (C := C) hC Uo
    have hξUo : ξ ∈ (Uo : Set C.pt) := by
      simpa [Uo] using hξU
    have hξUnionSet : ξ ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      rwa [hW] at hξUo
    rcases mem_iUnion.1 hξUnionSet with ⟨i, hξWi⟩
    have hξiWi : ξi i ∈ (W i : Set (F.obj i)) := by
      simpa [ξ, limit_cone_point_of_compatible_family] using hξWi
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (W i : Set (F.obj i))).Nonempty :=
      ((hξi i).mem_open_set_iff (W i).isOpen).1 hξiWi
    rcases hStageMeet with ⟨y, hyClosure, hyWi⟩
    rcases mem_closure_iff.1 hyClosure (W i : Set (F.obj i)) (W i).isOpen hyWi with
      ⟨w, hwWi, hwImage⟩
    rcases hwImage with ⟨z, hz, rfl⟩
    refine ⟨z, ?_, hz⟩
    have hzUnion : z ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      exact mem_iUnion.2 ⟨i, by simpa using hwWi⟩
    have hzUo : z ∈ (Uo : Set C.pt) := by
      rwa [hW]
    simpa [Uo] using hzUo
  have hξ_mem : ξ ∈ Z := by
    simpa [hZ_closed.closure_eq] using hξ_mem_closure
  have hξ_specializes : ∀ ⦃z : C.pt⦄, z ∈ Z → ξ ⤳ z := by
    intro z hz
    -- Expand a neighborhood of `z` into stage pullbacks. The chosen stage pullback contains a
    -- point of the stage image of `Z`, hence also the stage generic point, so `ξ` lies in it.
    rw [specializes_iff_forall_open]
    intro U hU hzU
    let Uo : Opens C.pt := ⟨U, hU⟩
    obtain ⟨W, hW⟩ := open_eq_iUnion_preimage_of_isLimit (F := F) (C := C) hC Uo
    have hzUo : z ∈ (Uo : Set C.pt) := by
      simpa [Uo] using hzU
    have hzUnionSet : z ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      rwa [hW] at hzUo
    rcases mem_iUnion.1 hzUnionSet with ⟨i, hzWi⟩
    have hStageMeet :
        (closure (C.π.app i '' Z) ∩ (W i : Set (F.obj i))).Nonempty := by
      exact ⟨C.π.app i z, subset_closure ⟨z, hz, rfl⟩, hzWi⟩
    have hξiWi : ξi i ∈ (W i : Set (F.obj i)) :=
      ((hξi i).mem_open_set_iff (W i).isOpen).2 hStageMeet
    have hξUnion : ξ ∈ ⋃ i, C.π.app i ⁻¹' (W i : Set (F.obj i)) := by
      exact mem_iUnion.2 ⟨i, by simpa [ξ, limit_cone_point_of_compatible_family] using hξiWi⟩
    have hξUo : ξ ∈ (Uo : Set C.pt) := by
      rwa [hW]
    simpa [Uo] using hξUo
  have hclosure_subset : closure ({ξ} : Set C.pt) ⊆ Z :=
    hZ_closed.closure_subset_iff.mpr (by simpa using (singleton_subset_iff.mpr hξ_mem))
  refine ⟨ξ, ?_⟩
  -- The specialization criterion identifies `Z` with the closure of the singleton `{ξ}`.
  rw [isGenericPoint_iff_specializes]
  intro z
  constructor
  · intro hz
    exact hclosure_subset (specializes_iff_mem_closure.mp hz)
  · intro hz
    exact hξ_specializes hz

/-- Helper for Lemma 5.23.12: index the basic opens on the explicit limit cone by a stage together
with an open subset of that stage. -/
def projection_preimage_basis (C : Cone F) :
    (Σ i : Iᵒᵖ, Opens (F.obj i)) → Set C.pt :=
  fun p ↦ C.π.app p.1 ⁻¹' (p.2 : Set (F.obj p.1))

/-- Helper for Lemma 5.23.12: projection pullbacks of stage opens form the canonical basis on the
explicit inverse-limit cone. -/
lemma isTopologicalBasis_projection_preimages :
    IsTopologicalBasis
      (Set.range (projection_preimage_basis (F := F) (TopCat.limitCone F))) := by
  let C := TopCat.limitCone F
  -- Rewrite the sigma-indexed family into the existential form expected by the mathlib owner.
  rw [show Set.range (projection_preimage_basis (F := F) C) =
      {W : Set C.pt | ∃ (j : Iᵒᵖ) (U : Set (F.obj j)), IsOpen U ∧ W = C.π.app j ⁻¹' U} by
      ext W
      constructor
      · rintro ⟨⟨j, U⟩, rfl⟩
        exact ⟨j, (U : Set (F.obj j)), U.isOpen, rfl⟩
      · rintro ⟨j, U, hU, rfl⟩
        exact ⟨⟨j, ⟨U, hU⟩⟩, rfl⟩]
  simpa using
    (TopCat.isTopologicalBasis_cofiltered_limit.{u, u, u} F C (TopCat.limitConeIsLimit F)
      (fun j ↦ {U : Set (F.obj j) | IsOpen U})
      (fun _ ↦ isTopologicalBasis_opens)
      (fun _ ↦ isOpen_univ)
      (fun _ _ _ hU₁ hU₂ ↦ hU₁.inter hU₂)
      (fun _ _ f _ hU ↦ hU.preimage (F.map f).hom.continuous))

/-- Helper for Lemma 5.23.12: the identity on compatible families is continuous from the inverse
limit built from the discrete stage topologies to the original inverse limit. -/
noncomputable def continuous_discrete_stage_limit_to_original_limit :
    (TopCat.limitCone (F ⋙ forget TopCat ⋙ TopCat.discrete)).pt ⟶ (TopCat.limitCone F).pt := by
  let C := TopCat.limitCone F
  let D := TopCat.limitCone (F ⋙ forget TopCat ⋙ TopCat.discrete)
  have hC : IsLimit C := TopCat.limitConeIsLimit F
  have hle : D.pt.str ≤ C.pt.str := by
    -- Route correction: compare the two limit topologies by checking continuity of each original
    -- stage projection out of the finer discrete-stage limit.
    rw [TopCat.induced_of_isLimit C hC]
    refine le_iInf ?_
    intro i
    exact (continuous_iff_le_induced).1 <| by
      letI : DiscreteTopology ↥((F ⋙ forget TopCat ⋙ TopCat.discrete).obj i) := by
        change DiscreteTopology ↥(TopCat.discrete.obj ↥(F.obj i))
        infer_instance
      -- Every subset is open on the discrete stage, so the original stage projection is
      -- continuous from the discrete-stage limit.
      rw [continuous_def]
      intro V hV
      let V' : Set ((F ⋙ forget TopCat ⋙ TopCat.discrete).obj i) := V
      have hV' : IsOpen V' := isOpen_discrete V'
      simpa [V'] using (D.π.app i).hom.continuous.isOpen_preimage _ hV'
  have hcont : @Continuous D.pt C.pt D.pt.str C.pt.str (fun x ↦ (x : C.pt)) := by
    rw [continuous_iff_le_induced]
    change D.pt.str ≤ induced id C.pt.str
    rw [induced_id]
    exact hle
  exact TopCat.ofHom ⟨fun x ↦ (x : C.pt), hcont⟩

/-- Helper for Lemma 5.23.12: every basic projection pullback is compact, by viewing the same
compatible-family set with the finer inverse-limit topology coming from discrete finite stages. -/
lemma projection_preimage_isCompact_via_discrete_stage_limit
    [∀ i : Iᵒᵖ, Finite (F.obj i)] (i : Iᵒᵖ) (U : Opens (F.obj i)) :
    IsCompact (((TopCat.limitCone F).π.app i) ⁻¹' (U : Set (F.obj i))) := by
  let C := TopCat.limitCone F
  let G := F ⋙ forget TopCat ⋙ TopCat.discrete
  let D := TopCat.limitCone G
  let f : D.pt ⟶ C.pt := continuous_discrete_stage_limit_to_original_limit (F := F)
  have hproj (x : D.pt) : C.π.app i (f x) = D.π.app i x := rfl
  haveI : CompactSpace ↥D.pt := by
    -- The discrete-stage system is a diagram of finite discrete compact Hausdorff spaces.
    haveI : ∀ j : Iᵒᵖ, CompactSpace ↥(G.obj j) := by
      intro j
      letI : Finite ↥(G.obj j) := by
        change Finite ↥(F.obj j)
        infer_instance
      infer_instance
    haveI : ∀ j : Iᵒᵖ, T2Space ↥(G.obj j) := by
      intro j
      letI : DiscreteTopology ↥(G.obj j) := by
        change DiscreteTopology ↥(TopCat.discrete.obj ↥(F.obj j))
        infer_instance
      infer_instance
    letI : CompactSpace ↥((limit.cone G).pt) := by
      simpa using (compactSpace_limit_of_compactSpace_t2Space G)
    let e :=
      TopCat.homeoOfIso
        (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit G) (limit.isLimit G))
    simpa [D] using e.symm.compactSpace
  let s : Set (G.obj i) := ((U : Set (F.obj i)) : Set (G.obj i))
  have hCompactDiscrete : IsCompact ((D.π.app i) ⁻¹' s) := by
    letI : DiscreteTopology ↥(G.obj i) := by
      change DiscreteTopology ↥(TopCat.discrete.obj ↥(F.obj i))
      infer_instance
    -- In the discrete-stage limit the same basic set is closed, hence compact.
    have hClosed : IsClosed ((D.π.app i) ⁻¹' s : Set D.pt) :=
      (isClosed_discrete s).preimage (D.π.app i).hom.continuous
    exact hClosed.isCompact
  have hImage :
      (f '' ((D.π.app i) ⁻¹' s : Set D.pt)) = ((C.π.app i) ⁻¹' (U : Set (F.obj i)) : Set C.pt) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_preimage.2 <| by
        simpa [s, hproj y] using (mem_preimage.1 hy)
    · intro hx
      refine ⟨x, ?_, ?_⟩
      · exact mem_preimage.2 <| by
          simpa [s, hproj x] using (mem_preimage.1 hx)
      · show (f x : C.pt) = x
        rfl
  -- The comparison map is the identity on the compatible-family set, so its image is exactly the
  -- original basic open.
  convert hCompactDiscrete.image f.hom.continuous using 1
  exact hImage.symm

/-- Helper for Lemma 5.23.12: the intersection of two basis opens is again a single basis open
after passing to a common upper-bound stage in the directed system. -/
lemma projection_preimage_inter_eq
    (i j : Iᵒᵖ) (Ui : Opens (F.obj i)) (Uj : Opens (F.obj j)) :
    ∃ (k : Iᵒᵖ) (_ : k ⟶ i) (_ : k ⟶ j) (Uk : Opens (F.obj k)),
      (((TopCat.limitCone F).π.app i) ⁻¹' (Ui : Set (F.obj i))) ∩
          (((TopCat.limitCone F).π.app j) ⁻¹' (Uj : Set (F.obj j))) =
        ((TopCat.limitCone F).π.app k) ⁻¹' (Uk : Set (F.obj k)) := by
  let C := TopCat.limitCone F
  have hπ {a b : Iᵒᵖ} (h : a ⟶ b) (x : C.pt) :
      C.π.app b x = F.map h (C.π.app a x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun m : C.pt ⟶ F.obj b ↦ m x) (C.w h).symm
  -- Directedness lets us compare both stage conditions at one common stage.
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.unop j.unop
  let k' : Iᵒᵖ := Opposite.op k
  let f : k' ⟶ i := Quiver.Hom.op (homOfLE hik)
  let g : k' ⟶ j := Quiver.Hom.op (homOfLE hjk)
  let Uk : Opens (F.obj k') := Opens.comap (F.map f).hom Ui ⊓ Opens.comap (F.map g).hom Uj
  refine ⟨k', f, g, Uk, ?_⟩
  ext x
  constructor
  · rintro ⟨hxi, hxj⟩
    refine mem_preimage.2 ?_
    constructor
    · have hxi' : C.π.app i x ∈ (Ui : Set (F.obj i)) := hxi
      rwa [hπ f x] at hxi'
    · have hxj' : C.π.app j x ∈ (Uj : Set (F.obj j)) := hxj
      rwa [hπ g x] at hxj'
  · intro hx
    have hxpair :
        x ∈ (C.π.app k') ⁻¹' ((Opens.comap (F.map f).hom Ui : Opens (F.obj k')) : Set (F.obj k')) ∩
          (C.π.app k') ⁻¹' ((Opens.comap (F.map g).hom Uj : Opens (F.obj k')) : Set (F.obj k')) := by
      simpa [Uk] using hx
    constructor
    · refine mem_preimage.2 ?_
      have hleft : F.map f (C.π.app k' x) ∈ (Ui : Set (F.obj i)) := hxpair.1
      rwa [hπ f x]
    · refine mem_preimage.2 ?_
      have hright : F.map g (C.π.app k' x) ∈ (Uj : Set (F.obj j)) := hxpair.2
      rwa [hπ g x]

-- Proof sketch: the source proof splits into two pieces. The sobriety part is implemented below by
-- constructing the compatible family of stage generic points. The remaining compact-open basis
-- comparison still needs the discrete-limit compactness bridge.
/-- Lemma 5.23.12: the inverse limit of a directed inverse system of finite sober topological
spaces is a spectral topological space. -/
theorem spectralSpace_of_limit_finite_sober_inverse_system
    [∀ i : Iᵒᵖ, Finite (F.obj i)] :
    SpectralSpace ↥(limit F) := by
  classical
  let C := TopCat.limitCone F
  -- Route correction: work on the explicit cone point first; the sobriety heart is already
  -- available from `generic_point_of_irreducible_closed_limit`.
  letI : T0Space C.pt := by
    change T0Space { u : ∀ j : Iᵒᵖ, F.obj j |
      ∀ {i j : Iᵒᵖ} (f : i ⟶ j), F.map f (u i) = u j }
    infer_instance
  letI : QuasiSober C.pt :=
    { sober := fun {Z} hZ_irred hZ_closed ↦
        generic_point_of_irreducible_closed_limit (F := F) hZ_irred hZ_closed }
  let i₀ : Iᵒᵖ := Opposite.op (Classical.choice ‹Nonempty I›)
  letI : CompactSpace C.pt := CompactSpace.mk <| by
    -- Taking the top open on any stage identifies the whole inverse limit with one basis element.
    simpa using
      (projection_preimage_isCompact_via_discrete_stage_limit (F := F) i₀ (⊤ : Opens (F.obj i₀)))
  let b := projection_preimage_basis (F := F) C
  have hBasis : IsTopologicalBasis (Set.range b) :=
    isTopologicalBasis_projection_preimages (F := F)
  have hCompactBasis : ∀ p : Σ i : Iᵒᵖ, Opens (F.obj i), IsCompact (b p) := by
    rintro ⟨i, U⟩
    -- Each basis open inherits compactness from the discrete-stage comparison space.
    simpa [b, projection_preimage_basis] using
      (projection_preimage_isCompact_via_discrete_stage_limit (F := F) i U)
  have hCompactInter :
      ∀ p q : Σ i : Iᵒᵖ, Opens (F.obj i), IsCompact (b p ∩ b q) := by
    rintro ⟨i, Ui⟩ ⟨j, Uj⟩
    obtain ⟨k, _, _, Uk, hEq⟩ := projection_preimage_inter_eq (F := F) i j Ui Uj
    -- Directedness rewrites every basis intersection to one basis open upstairs.
    have hbEq : b ⟨i, Ui⟩ ∩ b ⟨j, Uj⟩ = b ⟨k, Uk⟩ := by
      simpa [b, projection_preimage_basis] using hEq
    rw [hbEq]
    simpa [b, projection_preimage_basis] using
      (projection_preimage_isCompact_via_discrete_stage_limit (F := F) k Uk)
  letI : PrespectralSpace C.pt :=
    PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis
  letI : QuasiSeparatedSpace C.pt :=
    QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
  letI : SpectralSpace C.pt :=
    { toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := inferInstance
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  let e :=
    TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit F) (limit.isLimit F))
  -- Transport the spectral ingredients from the explicit owner cone to the abstract categorical
  -- limit object.
  letI : T0Space ↥(limit F) := e.t0Space
  letI : CompactSpace ↥(limit F) := e.compactSpace
  letI : QuasiSober ↥(limit F) := e.symm.isOpenEmbedding.quasiSober
  letI : QuasiSeparatedSpace ↥(limit F) := e.symm.isOpenEmbedding.quasiSeparatedSpace
  letI : PrespectralSpace ↥(limit F) := e.symm.isOpenEmbedding.prespectralSpace
  exact SpectralSpace.mk

end
