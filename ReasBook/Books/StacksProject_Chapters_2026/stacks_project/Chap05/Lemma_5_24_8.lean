module

public import stacks_project.Chap05.Lemma_5_24_7
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import stacks_project.Chap05.Lemma_5_15_8
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_5
import stacks_project.Chap05.Lemma_5_24_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits
open CompactOpens
open TopologicalSpace.Opens

universe u

noncomputable section

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.24.8:
- primary domain: inverse limits in `TopCat` of locally closed spectral subspaces cut out by a
  constructible subset inside a directed family of compact opens;
- sampled owner declarations:
  `compactOpenIntersectionCone`,
  `TopCat.nonempty_isLimit_iff_eq_induced`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`;
- best owner abstraction: the source-facing cone
  `sdiffCone_of_compactOpenDirectedIntersection E S hW`, with the canonical `TopCat` limit
  criterion and cofiltered-limit spectrality theorem reused as the core/canonical layer;
- primitive data: a constructible subset `E`, a family `S : Set (CompactOpens X)`, and the
  equality `nhdsKer E = ⋂ U ∈ S, (U : Set X)`;
- derived API: spectrality of each stage `U \ E`, spectrality of the transition maps, and the
  limiting-cone statement for `nhdsKer E \ E`.

Source/core/bridge triage:
- `source-facing`: the diagram `U ↦ U \ E` and its canonical cone from `nhdsKer E \ E`;
- `core/canonical`: `TopCat.nonempty_isLimit_iff_eq_induced` and
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- `bridge/view`: the underlying `Type`-valued section argument proving the cone satisfies the
  universal property.

No earlier Chapter 5 file owns the locally closed diagram `U ↦ U \ E`, so this file keeps that
source-facing cone and refines only the proof boilerplate and public limit entry. -/

/-- The diagram `U ↦ U \ E` attached to a family of compact opens, ordered by reverse inclusion. -/
def sdiffDiagram_of_compactOpenDirectedIntersection
    (E : Set X) (S : Set (CompactOpens X)) :
    S ⥤ TopCat.{u} where
  obj U := TopCat.of ↥(((U.1 : Set X) \ E : Set X))
  map hij :=
    TopCat.ofHom
      ⟨fun x ↦ ⟨x.1, ⟨hij.le x.2.1, x.2.2⟩⟩,
        continuous_subtype_val.subtype_mk fun x ↦ ⟨hij.le x.2.1, x.2.2⟩⟩
  map_id U := by
    ext x
    rfl
  map_comp hij hjk := by
    ext x
    rfl

/-- The canonical cone from `nhdsKer E \ E` to the diagram `U ↦ U \ E` attached to an
intersection presentation of `nhdsKer E`. -/
def sdiffCone_of_compactOpenDirectedIntersection
    (E : Set X) (S : Set (CompactOpens X))
    (hW : nhdsKer E = ⋂ U ∈ S, (U : Set X)) :
    Cone (sdiffDiagram_of_compactOpenDirectedIntersection E S) where
  pt := TopCat.of ↥((nhdsKer E \ E : Set X))
  π :=
    { app := fun U ↦
        TopCat.ofHom
          ⟨fun x ↦ ⟨x.1, ⟨mem_of_mem_iInter_compactOpens hW x.2.1 U.2, x.2.2⟩⟩,
            continuous_subtype_val.subtype_mk
              (fun x ↦ ⟨mem_of_mem_iInter_compactOpens hW x.2.1 U.2, x.2.2⟩)⟩
      naturality := by
        intro U V hij
        ext x
        rfl }

theorem induced_sdiffConeApp
    (E : Set X) (S : Set (CompactOpens X)) (hW : nhdsKer E = ⋂ U ∈ S, (U : Set X)) (U : S) :
    TopologicalSpace.induced
        ((sdiffCone_of_compactOpenDirectedIntersection E S hW).π.app U)
        ((sdiffDiagram_of_compactOpenDirectedIntersection E S).obj U).str =
      (sdiffCone_of_compactOpenDirectedIntersection E S hW).pt.str := by
  change
      TopologicalSpace.induced
          ((sdiffCone_of_compactOpenDirectedIntersection E S hW).π.app U)
          (TopologicalSpace.induced Subtype.val inferInstance) =
        TopologicalSpace.induced Subtype.val inferInstance
  rw [induced_compose]
  rfl

theorem val_eq_of_section_of_sdiffDiagram
    (E : Set X) (S : Set (CompactOpens X)) (hDirected : DirectedOn (· ≥ ·) S)
    (s : ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙ forget TopCat).sections)
    (U V : S) :
    ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
        forget TopCat).obj T) U).1 =
      ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
        forget TopCat).obj T) V).1 := by
  obtain ⟨Z, hZS, hZU, hZV⟩ := hDirected U.1 U.2 V.1 V.2
  let Z' : S := ⟨Z, hZS⟩
  have hZU_eq :
      (((sdiffDiagram_of_compactOpenDirectedIntersection E S).map (show Z' ⟶ U from homOfLE hZU))
        ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
          forget TopCat).obj T) Z')) =
      (s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
        forget TopCat).obj T) U :=
    s.2 (show Z' ⟶ U from homOfLE hZU)
  have hZV_eq :
      (((sdiffDiagram_of_compactOpenDirectedIntersection E S).map (show Z' ⟶ V from homOfLE hZV))
        ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
          forget TopCat).obj T) Z')) =
      (s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
        forget TopCat).obj T) V :=
    s.2 (show Z' ⟶ V from homOfLE hZV)
  have hZU_val :
      Subtype.val
          (((sdiffDiagram_of_compactOpenDirectedIntersection E S).map
                (show Z' ⟶ U from homOfLE hZU))
              ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
                forget TopCat).obj T) Z')) =
        Subtype.val
          ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
            forget TopCat).obj T) U) := by
    exact congrArg Subtype.val hZU_eq
  have hZV_val :
      Subtype.val
          (((sdiffDiagram_of_compactOpenDirectedIntersection E S).map
                (show Z' ⟶ V from homOfLE hZV))
              ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
                forget TopCat).obj T) Z')) =
        Subtype.val
          ((s : ∀ T : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙
            forget TopCat).obj T) V) := by
    exact congrArg Subtype.val hZV_eq
  exact hZU_val.symm.trans hZV_val

def isLimit_sdiffCone_of_directed_forget
    (E : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : nhdsKer E = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    IsLimit ((forget TopCat).mapCone (sdiffCone_of_compactOpenDirectedIntersection E S hW)) := by
  classical
  let F : S ⥤ Type _ := (sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙ forget TopCat
  refine Classical.choice <| (Types.isLimit_iff_bijective_sectionOfCone _).2 ?_
  let U₀ : S := Classical.choice hS_nonempty.to_subtype
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hU₀ :
        ((Types.sectionOfCone
              ((forget TopCat).mapCone (sdiffCone_of_compactOpenDirectedIntersection E S hW)) x).1 U₀) =
          ((Types.sectionOfCone
                ((forget TopCat).mapCone (sdiffCone_of_compactOpenDirectedIntersection E S hW))
              y).1 U₀) := by
      exact congrArg (fun t ↦ t.1 U₀) hxy
    simp only at hU₀
    exact Subtype.ext <|
      congrArg
        (fun z :
          ((sdiffDiagram_of_compactOpenDirectedIntersection E S) ⋙ forget TopCat).obj U₀ ↦ z.1)
        hU₀
  · intro s
    let x : X := ((s : ∀ U : S, F.obj U) U₀).1
    have hx_mem :
        ∀ V : CompactOpens X, V ∈ S →
          x ∈ (V : Set X) ∧ x ∉ E := by
      intro V hV
      have hx_eq :
          x = ((s : ∀ U : S, F.obj U) ⟨V, hV⟩).1 := by
        simpa [F, x] using
          val_eq_of_section_of_sdiffDiagram E S hDirected s U₀ ⟨V, hV⟩
      exact hx_eq ▸ ((s : ∀ U : S, F.obj U) ⟨V, hV⟩).2
    have hxW : x ∈ nhdsKer E := by
      rw [hW]
      simpa [Set.mem_iInter] using fun V hV ↦ (hx_mem V hV).1
    refine ⟨⟨x, ⟨hxW, (hx_mem U₀.1 U₀.2).2⟩⟩, ?_⟩
    apply Subtype.ext
    funext V
    apply Subtype.ext
    change x = ((s : ∀ U : S, F.obj U) V).1
    simpa [F, x] using val_eq_of_section_of_sdiffDiagram E S hDirected s U₀ V

theorem sdiffCone_pt_eq_iInf_induced
    (E : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : nhdsKer E = ⋂ U ∈ S, (U : Set X)) :
    (sdiffCone_of_compactOpenDirectedIntersection E S hW).pt.str =
      ⨅ U : S, ((sdiffDiagram_of_compactOpenDirectedIntersection E S).obj U).str.induced
        ((sdiffCone_of_compactOpenDirectedIntersection E S hW).π.app U) := by
  classical
  let U₀ : S := Classical.choice hS_nonempty.to_subtype
  have hinduced :
      ∀ U : S,
        ((sdiffDiagram_of_compactOpenDirectedIntersection E S).obj U).str.induced
            ((sdiffCone_of_compactOpenDirectedIntersection E S hW).π.app U) =
          (sdiffCone_of_compactOpenDirectedIntersection E S hW).pt.str := by
    intro U
    simpa using induced_sdiffConeApp E S hW U
  apply le_antisymm
  · exact le_iInf fun U ↦ (hinduced U).ge
  · exact (iInf_le
        (fun U : S ↦
          ((sdiffDiagram_of_compactOpenDirectedIntersection E S).obj U).str.induced
            ((sdiffCone_of_compactOpenDirectedIntersection E S hW).π.app U))
        U₀).trans (hinduced U₀).le

/-- Lemma 5.24.8, second clause: if `nhdsKer E` is written as a directed nonempty intersection of
quasi-compact opens as in Lemma `5.24.7 (5)`, then `nhdsKer E \ E` is the inverse limit of the
diagram `U ↦ U \ E`, expressed by the canonical cone
`sdiffCone_of_compactOpenDirectedIntersection E S hW`. -/
def isLimit_sdiff_of_compactOpenDirectedIntersection
    (E : Set X) (S : Set (CompactOpens X))
    (hS_nonempty : S.Nonempty) (hW : nhdsKer E = ⋂ U ∈ S, (U : Set X))
    (hDirected : DirectedOn (· ≥ ·) S) :
    IsLimit (sdiffCone_of_compactOpenDirectedIntersection E S hW) := by
  classical
  let hforget :=
    isLimit_sdiffCone_of_directed_forget E S hS_nonempty hW hDirected
  exact Classical.choice <|
    (TopCat.nonempty_isLimit_iff_eq_induced
        (sdiffCone_of_compactOpenDirectedIntersection E S hW) hforget).2
      (sdiffCone_pt_eq_iInf_induced E S hS_nonempty hW)

theorem spectralSpace_sdiff_compactOpen
    [SpectralSpace X] (E : Set X) (hE : IsConstructible E) (U : CompactOpens X) :
    SpectralSpace ↥(((U : Set X) \ E : Set X)) := by
  haveI : SpectralSpace ↥(U : Set X) := by
    letI : CompactSpace ↥((Opens.toTopCat (TopCat.of X)).obj U.toOpens) := by
      change CompactSpace ↥(U.toOpens)
      exact isCompact_iff_compactSpace.mp U.isCompact
    let V : Opens (TopCat.of X) := U.toOpens
    have hOpenEmbedding : IsOpenEmbedding (inclusion' V) := Opens.isOpenEmbedding V
    simpa using
      (hOpenEmbedding.spectralSpace :
        SpectralSpace ↥((Opens.toTopCat (TopCat.of X)).obj U.toOpens))
  have hU_retro : IsRetrocompact (U : Set X) := by
    exact (QuasiSeparatedSpace.isRetrocompact_iff_isCompact U.isOpen).2 U.isCompact
  have hTrace : IsConstructible ((Subtype.val : ↥(U : Set X) → X) ⁻¹' E) :=
    Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact hE hU_retro
  have hClosed :
      IsClosed[constructibleTopology ↥(U : Set X)] (((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) := by
    have hOpen :
        @IsOpen ↥(U : Set X) (constructibleTopology ↥(U : Set X))
          ((Subtype.val : ↥(U : Set X) → X) ⁻¹' E) := by
      simpa using
        (show @IsOpen ↥(U : Set X) (constructibleTopology ↥(U : Set X))
            ((Subtype.val : ↥(U : Set X) → X) ⁻¹' E) from
          (isClopen_constructibleTopology_of_isConstructible hTrace).2)
    simpa using
      (@IsOpen.isClosed_compl
        ↥(U : Set X) (constructibleTopology ↥(U : Set X))
        ((Subtype.val : ↥(U : Set X) → X) ⁻¹' E) hOpen)
  have hNested :
      SpectralSpace ↥(((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) :=
    by
      let Y : Type u := ↥(U : Set X)
      change SpectralSpace ↥(((Subtype.val : Y → X) ⁻¹' E)ᶜ)
      exact spectralSpace_subtype_of_isClosed_constructibleTopology hClosed
  letI : SpectralSpace ↥(((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) := hNested
  let e :
      ↥(((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) ≃ₜ
        (Subtype.val : ↥(U : Set X) → X) '' (((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) :=
    IsEmbedding.subtypeVal.homeomorphImage (((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ)
  have himage :
      (Subtype.val : ↥(U : Set X) → X) '' (((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) =
        ((U : Set X) \ E : Set X) := by
    ext x
    simp [and_comm]
  let e' : ↥(((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ) ≃ₜ ↥(((U : Set X) \ E : Set X)) :=
    e.trans (Homeomorph.setCongr himage)
  have hCompactTarget : IsCompact (((U : Set X) \ E : Set X)) := by
    rw [← himage]
    exact
      (isCompact_iff_compactSpace.mpr
        (inferInstance :
          CompactSpace ↥(((Subtype.val : ↥(U : Set X) → X) ⁻¹' E)ᶜ))).image continuous_subtype_val
  letI : CompactSpace ↥(((U : Set X) \ E : Set X)) := by
    exact isCompact_iff_compactSpace.mp hCompactTarget
  have hOpenEmbedding : IsOpenEmbedding e'.symm := e'.symm.isOpenEmbedding
  exact hOpenEmbedding.spectralSpace

theorem isSpectralMap_sdiff_inclusion
    [SpectralSpace X] (E : Set X) (hE : IsConstructible E)
    {U V : CompactOpens X} (hUV : U ≤ V) :
    IsSpectralMap
      (show ↥(((U : Set X) \ E : Set X)) → ↥(((V : Set X) \ E : Set X)) from
        fun x ↦ ⟨x.1, ⟨hUV x.2.1, x.2.2⟩⟩) := by
  haveI : SpectralSpace ↥(((U : Set X) \ E : Set X)) := spectralSpace_sdiff_compactOpen E hE U
  haveI : SpectralSpace ↥(((V : Set X) \ E : Set X)) := spectralSpace_sdiff_compactOpen E hE V
  let T : Set ↥(((V : Set X) \ E : Set X)) :=
    (Subtype.val : ↥(((V : Set X) \ E : Set X)) → X) ⁻¹' (U : Set X)
  have hT_open : IsOpen T := U.isOpen.preimage continuous_subtype_val
  let hsub : ((U : Set X) \ E : Set X) ⊆ ((V : Set X) \ E : Set X) :=
    fun x hx ↦ ⟨hUV hx.1, hx.2⟩
  let f : ↥(((U : Set X) \ E : Set X)) → ↥(((V : Set X) \ E : Set X)) :=
    fun x ↦ ⟨x.1, ⟨hUV x.2.1, x.2.2⟩⟩
  have hT_image : f '' (univ : Set ↥(((U : Set X) \ E : Set X))) = T := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2.1
    · intro hx
      refine ⟨⟨x.1, ⟨hx, x.2.2⟩⟩, trivial, ?_⟩
      ext
      rfl
  have hT_compact : IsCompact T := by
    rw [← hT_image]
    exact isCompact_univ.image (show Continuous f from
      continuous_subtype_val.subtype_mk fun x ↦ ⟨hUV x.2.1, x.2.2⟩)
  have hT_retro : IsRetrocompact T := by
    exact (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hT_open).2 hT_compact
  have hSubtype :
      IsSpectralMap (Subtype.val : T → ↥(((V : Set X) \ E : Set X))) :=
    (IsRetrocompact_iff_isSpectralMap_subtypeVal).mp hT_retro
  let e :
      ↥(((U : Set X) \ E : Set X)) ≃ₜ T :=
    (Homeomorph.Set.univ ↥(((U : Set X) \ E : Set X))).symm.trans
      ((Topology.IsEmbedding.inclusion hsub).homeomorphImage univ) |>.trans
      (Homeomorph.setCongr hT_image)
  have hHomeo : IsSpectralMap e := by
    refine ⟨e.continuous, fun s hs_open hs_comp ↦ ?_⟩
    simpa [e.toEquiv.image_symm_eq_preimage s] using hs_comp.image e.symm.continuous
  simpa [e, T, hT_image, Function.comp] using hSubtype.comp hHomeo

-- Proof sketch: apply Lemma `5.24.7` to the quasi-compact subset `E`, obtaining a directed
-- presentation of `nhdsKer E` by quasi-compact opens. Each difference `U \ E` is a spectral
-- subspace because `E` stays constructible in `U`, and the canonical inverse-limit presentation
-- of the intersection identifies `nhdsKer E \ E` with a cofiltered limit of these spectral
-- spaces. Then use the inverse-limit spectrality theorem.
/-- Lemma 5.24.8: if `X` is spectral and `E ⊆ X` is constructible, then the subspace of points
specializing to `E` but not lying in `E`, i.e. `nhdsKer E \ E`, is spectral. -/
theorem spectralSpace_specializingPoints_sdiff_constructible
    [SpectralSpace X] (E : Set X) (hE : IsConstructible E) :
    SpectralSpace ↥(nhdsKer E \ E) := by
  have hE_closed : IsClosed[constructibleTopology X] E := by
    have hOpen : @IsOpen X (constructibleTopology X) Eᶜ :=
      by
        simpa using
          (show @IsOpen X (constructibleTopology X) Eᶜ from
            (isClopen_constructibleTopology_of_isConstructible hE.compl).2)
    simpa using @IsOpen.isClosed_compl X (constructibleTopology X) Eᶜ hOpen
  haveI : SpectralSpace ↥E :=
    by
      let Y : Type u := X
      change SpectralSpace ↥(E : Set Y)
      exact spectralSpace_subtype_of_isClosed_constructibleTopology hE_closed
  have hE_compact : IsCompact E := isCompact_iff_compactSpace.mpr inferInstance
  have hClause3 : ∃ F : Set X, IsCompact F ∧ nhdsKer E = nhdsKer F := ⟨E, hE_compact, rfl⟩
  obtain ⟨S, hS_nonempty, hW, hDirected⟩ :=
    ((compact_generalizing_subset_tfae (nhdsKer E)).out 2 4).mp hClause3
  letI : Nonempty S := hS_nonempty.to_subtype
  letI : IsCodirectedOrder S :=
    directedOn_univ_iff.mp fun U _ V _ ↦ by
      obtain ⟨Z, hZS, hZU, hZV⟩ := hDirected U.1 U.2 V.1 V.2
      exact ⟨⟨Z, hZS⟩, trivial, hZU, hZV⟩
  letI (U : S) : SpectralSpace ↥((sdiffDiagram_of_compactOpenDirectedIntersection E S).obj U) := by
    simpa [sdiffDiagram_of_compactOpenDirectedIntersection] using
      spectralSpace_sdiff_compactOpen E hE U.1
  have hF :
      ∀ ⦃U V : S⦄ (hUV : U ⟶ V),
        IsSpectralMap ((sdiffDiagram_of_compactOpenDirectedIntersection E S).map hUV) := by
    intro U V hUV
    simpa [sdiffDiagram_of_compactOpenDirectedIntersection] using
      isSpectralMap_sdiff_inclusion E hE hUV.le
  exact spectralSpace_of_isLimit_of_cofiltered_spectral_diagram
    (isLimit_sdiff_of_compactOpenDirectedIntersection E S hS_nonempty hW hDirected) hF

end
