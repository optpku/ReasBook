module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Topology.Separation.CompletelyRegular
import stacks_project.Chap05.Lemma_5_23_10
import stacks_project.Chap05.Lemma_5_23_12
import stacks_project.Chap05.Lemma_5_23_3
import stacks_project.Chap05.Lemma_5_23_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Limits Opposite
open Set TopologicalSpace Topology

/- Domain-style sampling for spectral Sierpinski-product embeddings:
- primary domain: spectral spaces, constructible topology, and a compact-open Sierpinski-product
  map;
- sampled owner declarations:
  `SpectralSpace`,
  `CompactOpens`,
  `IsSpectralMap.isClosed_range_constructibleTopology`,
  `spectralSpace_subtype_of_isClosed_constructibleTopology`;
- best owner abstraction: the primitive owner data for the reverse direction are an embedding
  `f : X → ι → Prop` together with constructible-topology closedness of its range, while the
  forward spectral witness is the compact-open characteristic map indexed by `CompactOpens X`;
- primitive-vs-derived split: the embedding and range-closedness are the source-facing primitive
  data, while the existential packaging of a witness is derived API.

Layer triage:
- `source-facing`: Lemma 5.23.13, the existential embedding characterization of spectral spaces;
- `core/canonical`: `SpectralSpace`, `constructibleTopology`, `CompactOpens`, and the Sierpinski
  function space `ι → Prop`;
- `bridge/view`: the constructible-closed range bridge for spectral maps, the spectral-subspace
  bridge for constructibly closed subspaces, and the inverse-limit comparison from finite
  coordinate systems to the full Sierpinski product.
-/

section

variable (X : Type u) [TopologicalSpace X]

/-- Helper for Lemma 5.23.13: an open subset of the Sierpinski space containing `False` is the
whole space. -/
private theorem open_subset_prop_eq_univ {s : Set Prop} (hs : IsOpen s) (hFalse : False ∈ s) :
    s = Set.univ := by
  have h : s ∈ 𝓝 False := hs.mem_nhds hFalse
  simpa using h

/-- Helper for Lemma 5.23.13: an open subset of the Sierpinski space containing `True` but not
`False` is exactly `{True}`. -/
private theorem open_subset_prop_eq_singleton_true {s : Set Prop} (hs : IsOpen s)
    (hTrue : True ∈ s) (hFalse : False ∉ s) : s = ({True} : Set Prop) := by
  ext p
  by_cases hp : p
  · simpa [hp] using hTrue
  · have h : s ∈ 𝓝 True := hs.mem_nhds hTrue
    simpa [nhds_true, hp, hFalse] using h

/-- Helper for Lemma 5.23.13: the two-point Sierpinski space is quasi-sober. -/
private theorem quasiSoberProp : QuasiSober Prop := by
  refine ⟨?_⟩
  intro S hS hSclosed
  by_cases hTrue : True ∈ S
  · -- A closed irreducible subset containing `True` must also contain `False`, hence is `univ`.
    have hFalse : False ∈ S := by
      have hsub : closure ({True} : Set Prop) ⊆ S :=
        hSclosed.closure_subset_iff.mpr (by simpa using hTrue)
      have hmem : False ∈ closure ({True} : Set Prop) := by
        simp
      exact hsub hmem
    use True
    have hUniv : S = Set.univ := by
      ext p
      by_cases hp : p <;> simp [hp, hTrue, hFalse]
    simpa [hUniv] using (show IsGenericPoint True (Set.univ : Set Prop) by
      rw [isGenericPoint_def]
      ext p
      by_cases hp : p <;> simp [hp])
  · -- Otherwise irreducibility forces the closed subset to be exactly `{False}`.
    have hFalse : False ∈ S := by
      rcases hS.1 with ⟨x, hx⟩
      by_cases hxTrue : x
      · have hxEq : x = True := propext (iff_true_intro hxTrue)
        exact (hTrue <| by simpa [hxEq] using hx).elim
      · have hxEq : x = False := propext (iff_false_intro hxTrue)
        simpa [hxEq] using hx
    use False
    have hSingleton : S = ({False} : Set Prop) := by
      ext p
      by_cases hp : p <;> simp [hp, hTrue, hFalse]
    simpa [hSingleton] using (show IsGenericPoint False ({False} : Set Prop) by
      rw [isGenericPoint_def]
      ext p
      by_cases hp : p <;> simp [hp])

/-- Helper for Lemma 5.23.13: the Sierpinski space itself is spectral. -/
private theorem spectralSpaceProp : SpectralSpace Prop := by
  letI : QuasiSober Prop := quasiSoberProp
  exact SpectralSpace.mk

/-- Helper for Lemma 5.23.13: every finite product of the Sierpinski space is spectral. -/
private theorem spectralSpaceFiniteSierpinskiProduct {α : Type v} [Finite α] :
    SpectralSpace (α → Prop) := by
  classical
  -- Build finite products by repeatedly splitting off one coordinate with `Option`.
  refine Finite.induction_empty_option (P := fun β => SpectralSpace (β → Prop)) ?_ ?_ ?_ α
  · intro β γ e hβ
    let hHomeo : (γ → Prop) ≃ₜ (β → Prop) := by
      simpa using (Homeomorph.piCongrLeft (Y := fun _ : β => Prop) e.symm)
    letI : SpectralSpace (β → Prop) := hβ
    letI : CompactSpace (γ → Prop) := hHomeo.symm.compactSpace
    exact hHomeo.isOpenEmbedding.spectralSpace
  · let hHomeo : (PEmpty.{v + 1} → Prop) ≃ₜ PUnit.{v + 1} :=
      Homeomorph.homeomorphOfUnique _ _
    letI : SpectralSpace PUnit.{v + 1} := SpectralSpace.mk
    letI : CompactSpace (PEmpty → Prop) := hHomeo.symm.compactSpace
    exact hHomeo.isOpenEmbedding.spectralSpace
  · intro β _ hβ
    let e₁ : (Option β → Prop) ≃ₜ ((i : {x : Option β // x = none}) → Prop) ×
        ((i : {x : Option β // x ≠ none}) → Prop) :=
      Homeomorph.piEquivPiSubtypeProd (fun x : Option β => x = none) (fun _ => Prop)
    let eSome : {x : Option β // x ≠ none} ≃ β :=
      { toFun := fun x =>
          Option.get x.1 (Option.isSome_iff_exists.mpr (Option.ne_none_iff_exists'.1 x.2))
        invFun := fun b => ⟨some b, by simp⟩
        left_inv := by
          intro x
          apply Subtype.ext
          have hmem := Option.get_mem (o := x.1)
            (Option.isSome_iff_exists.mpr (Option.ne_none_iff_exists'.1 x.2))
          simpa [Option.mem_def] using hmem
        right_inv := by
          intro b
          simp }
    let e₂ :
        ((i : {x : Option β // x = none}) → Prop) × ((i : {x : Option β // x ≠ none}) → Prop) ≃ₜ
          Prop × (β → Prop) := by
      refine Homeomorph.prodCongr (Homeomorph.funUnique _ _) ?_
      simpa using (Homeomorph.piCongrLeft (Y := fun _ : β => Prop) eSome)
    let hHomeo : (Option β → Prop) ≃ₜ Prop × (β → Prop) := e₁.trans e₂
    letI : SpectralSpace Prop := spectralSpaceProp
    letI : SpectralSpace (β → Prop) := hβ
    letI : SpectralSpace (Prop × (β → Prop)) := inferInstance
    letI : CompactSpace (Option β → Prop) := hHomeo.symm.compactSpace
    exact hHomeo.isOpenEmbedding.spectralSpace

/-- Helper for Lemma 5.23.13: the finite-coordinate restriction system over `Finset ι`. -/
noncomputable def finiteRestrictionDiagram (ι : Type v) : (Finset ι)ᵒᵖ ⥤ TopCat where
  obj s := TopCat.of (s.unop → Prop)
  map {s t} h := TopCat.ofHom
    { toFun := fun f x => f ⟨x, (show t.unop ≤ s.unop from h.unop.down.down) x.2⟩
      continuous_toFun := continuous_pi fun x => continuous_apply _ }
  map_id s := by
    ext f x
    rfl
  map_comp {a b c} f g := by
    ext u x
    rfl

/-- Helper for Lemma 5.23.13: compatible finite-coordinate families are exactly full Sierpinski
functions. -/
noncomputable def compatibleFamilyHomeomorph (ι : Type v) :
    ↥(TopCat.limitCone (finiteRestrictionDiagram ι)).pt ≃ₜ (ι → Prop) where
  toFun u i := u.1 (Opposite.op ({i} : Finset ι)) ⟨i, by simp⟩
  invFun g := ⟨fun s x => g x.1, by intro i j f; funext x; rfl⟩
  left_inv := by
    intro u
    -- Read the value on a finite stage from its singleton restriction using compatibility.
    apply Subtype.ext
    funext s
    funext x
    let h : s ⟶ Opposite.op ({x.1} : Finset ι) := by
      exact Quiver.Hom.op ⟨PLift.up <| by simpa using x.2⟩
    have hcompat := congrFun (u.2 h) ⟨x.1, by simp⟩
    simpa [finiteRestrictionDiagram, h] using hcompat.symm
  right_inv := by
    intro g
    funext i
    rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    have hstage :
        Continuous fun u : ↥(TopCat.limitCone (finiteRestrictionDiagram ι)).pt =>
          u.1 (Opposite.op ({i} : Finset ι)) :=
      (continuous_apply (Opposite.op ({i} : Finset ι))).comp continuous_subtype_val
    exact (continuous_apply (⟨i, by simp⟩ : ({x // x ∈ ({i} : Finset ι)}))).comp hstage
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun s => continuous_pi fun x => continuous_apply x.1)
      (fun g i j f => by funext x; rfl)

/-- Helper for Lemma 5.23.13: arbitrary products of the Sierpinski space are spectral. -/
private theorem spectralSpaceSierpinskiProduct {ι : Type v} : SpectralSpace (ι → Prop) := by
  classical
  let F := finiteRestrictionDiagram ι
  letI : ∀ i : (Finset ι)ᵒᵖ, SpectralSpace (F.obj i) := by
    intro i
    change SpectralSpace (i.unop → Prop)
    exact spectralSpaceFiniteSierpinskiProduct
  letI : ∀ i : (Finset ι)ᵒᵖ, T0Space (F.obj i) := by
    intro i
    change T0Space (i.unop → Prop)
    infer_instance
  letI : ∀ i : (Finset ι)ᵒᵖ, Finite (F.obj i) := by
    intro i
    change Finite (i.unop → Prop)
    infer_instance
  have hLimit : SpectralSpace ↥(limit F) :=
    spectralSpace_of_limit_finite_sober_inverse_system (F := F)
  let eLimit : ↥(TopCat.limitCone F).pt ≃ₜ ↥(limit F) :=
    TopCat.homeoOfIso (IsLimit.conePointUniqueUpToIso (TopCat.limitConeIsLimit F) (limit.isLimit F))
  let e : ↥(limit F) ≃ₜ (ι → Prop) := eLimit.symm.trans (compatibleFamilyHomeomorph ι)
  letI : SpectralSpace ↥(limit F) := hLimit
  letI : CompactSpace (ι → Prop) := e.compactSpace
  exact e.symm.isOpenEmbedding.spectralSpace

/-- Helper for Lemma 5.23.13: the finite `true`-cylinder in a Sierpinski product. -/
private def trueCylinder {ι : Type v} (s : Finset ι) : Set (ι → Prop) :=
  {f | ∀ i ∈ s, f i}

/-- Helper for Lemma 5.23.13: finite `true`-cylinders are open in a Sierpinski product. -/
private theorem trueCylinder_isOpen {ι : Type v} (s : Finset ι) : IsOpen (trueCylinder s) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [trueCylinder]
  | cons i s hs ih =>
      have hiOpen : IsOpen ((fun f : ι → Prop => f i) ⁻¹' ({True} : Set Prop)) :=
        isOpen_singleton_true.preimage (continuous_apply i)
      simpa [trueCylinder, hs, Set.setOf_and] using hiOpen.inter ih

/-- Helper for Lemma 5.23.13: finite `true`-cylinders are compact. -/
private theorem trueCylinder_isCompact {ι : Type v} (s : Finset ι) : IsCompact (trueCylinder s) := by
  classical
  let e₁ : (ι → Prop) ≃ₜ ((i : {x // x ∈ s}) → Prop) × ((i : {x // x ∉ s}) → Prop) :=
    Homeomorph.piEquivPiSubtypeProd (fun i : ι => i ∈ s) (fun _ => Prop)
  let A : Set ((i : {x // x ∈ s}) → Prop) := {g | ∀ x, g x}
  have hACompact : IsCompact A := (Set.toFinite _).isCompact
  have himage : e₁ '' trueCylinder s = A ×ˢ (Set.univ : Set ((i : {x // x ∉ s}) → Prop)) := by
    ext p
    constructor
    · rintro ⟨f, hf, rfl⟩
      constructor
      · intro x
        exact hf x.1 x.2
      · simp
    · rintro ⟨hpA, hpU⟩
      refine ⟨e₁.symm p, ?_, by simp⟩
      intro i hi
      have hcoord : (e₁.symm p) i = p.1 ⟨i, hi⟩ := by
        simpa [e₁, hi]
      rw [hcoord]
      exact hpA ⟨i, hi⟩
  rw [e₁.isEmbedding.isCompact_iff]
  simpa [himage] using hACompact.prod isCompact_univ

/-- Helper for Lemma 5.23.13: finite `true`-cylinders form a basis of a Sierpinski product. -/
private theorem trueCylinder_isTopologicalBasis {ι : Type v} :
    IsTopologicalBasis (Set.range (trueCylinder : Finset ι → Set (ι → Prop))) := by
  classical
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with ⟨t, rfl⟩
    exact trueCylinder_isOpen t
  · intro x u hx hu
    -- Convert a general product-basis neighborhood to the equivalent finite `true`-cylinder.
    obtain ⟨v, hv, hxv, hvu⟩ :=
      (isTopologicalBasis_pi (fun _ : ι => isTopologicalBasis_opens)).exists_subset_of_mem_open hx hu
    rcases hv with ⟨U, F, hUopen, rfl⟩
    let t : Finset ι := F.filter fun i => U i = ({True} : Set Prop)
    refine ⟨trueCylinder t, ⟨t, rfl⟩, ?_, ?_⟩
    · intro i hi
      have hit : i ∈ F := (Finset.mem_filter.1 hi).1
      have hEq : U i = ({True} : Set Prop) := (Finset.mem_filter.1 hi).2
      have hxi : x i ∈ U i := by
        have : ∀ i ∈ F, x i ∈ U i := by
          simpa [Set.pi_def] using hxv
        exact this i hit
      simpa [hEq] using hxi
    · intro y hy
      apply hvu
      have hy' : ∀ i ∈ F, y i ∈ U i := by
        intro i hi
        by_cases hEq : U i = ({True} : Set Prop)
        · have hit : i ∈ t := by
            simpa [t, hEq] using hi
          have hyi : y i := hy i hit
          simpa [hEq] using hyi
        · have hFalse : False ∈ U i := by
            by_contra hFalse
            have hxi : x i ∈ U i := by
              have : ∀ i ∈ F, x i ∈ U i := by
                simpa [Set.pi_def] using hxv
              exact this i hi
            have hTrue : True ∈ U i := by
              by_cases hxiTrue : x i
              · simpa [hxiTrue] using hxi
              · exact (hFalse <| by simpa [hxiTrue] using hxi).elim
            have : U i = ({True} : Set Prop) :=
              open_subset_prop_eq_singleton_true (hUopen i hi) hTrue hFalse
            exact hEq this
          have hUniv : U i = Set.univ := open_subset_prop_eq_univ (hUopen i hi) hFalse
          simpa [hUniv]
      simpa [Set.pi_def] using hy'

/-- Helper for Lemma 5.23.13: the compact-open characteristic map into a Sierpinski product. -/
private def compactOpenSierpinskiMap (X : Type u) [TopologicalSpace X] :
    C(X, CompactOpens X → Prop) where
  toFun x U := x ∈ (U : Set X)
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro U
    exact continuous_Prop.2 U.isOpen

/-- Helper for Lemma 5.23.13: compact opens already recover the topology through Sierpinski
coordinates. -/
private theorem compactOpenSierpinskiMap_isInducing (X : Type u) [TopologicalSpace X]
    [PrespectralSpace X] : IsInducing (compactOpenSierpinskiMap X) := by
  refine .mk ?_
  apply le_antisymm
  · exact continuous_iff_le_induced.1 (compactOpenSierpinskiMap X).continuous
  · let B : Set (Set X) := {U : Set X | IsOpen U ∧ IsCompact U}
    have hOpen :
        ∀ s ∈ B,
          IsOpen[TopologicalSpace.induced (compactOpenSierpinskiMap X) inferInstance] s := by
      intro s hs
      rcases hs with ⟨hsOpen, hsCompact⟩
      let U : CompactOpens X := ⟨⟨s, hsCompact⟩, hsOpen⟩
      have hTargetOpen :
          IsOpen[Pi.topologicalSpace]
            ((fun g : CompactOpens X → Prop => g U) ⁻¹' ({True} : Set Prop)) :=
        isOpen_singleton_true.preimage (continuous_apply U)
      have hPreOpen :
          IsOpen[TopologicalSpace.induced (compactOpenSierpinskiMap X) inferInstance]
            ((fun x : X => compactOpenSierpinskiMap X x) ⁻¹'
              ((fun g : CompactOpens X → Prop => g U) ⁻¹' ({True} : Set Prop))) := by
        rw [isOpen_induced_iff]
        exact ⟨_, hTargetOpen, rfl⟩
      simpa [compactOpenSierpinskiMap] using hPreOpen
    have hgen :
        TopologicalSpace.induced (compactOpenSierpinskiMap X) inferInstance ≤
          TopologicalSpace.generateFrom B :=
      le_generateFrom hOpen
    exact hgen.trans (PrespectralSpace.isTopologicalBasis (X := X)).eq_generateFrom.ge

/-- Helper for Lemma 5.23.13: the compact-open characteristic map is injective on a spectral
space. -/
private theorem compactOpenSierpinskiMap_injective (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : Function.Injective (compactOpenSierpinskiMap X) := by
  intro x y hxy
  apply Inseparable.eq
  rw [← IsInducing.inseparable_iff (compactOpenSierpinskiMap_isInducing X), hxy]

/-- Helper for Lemma 5.23.13: the compact-open characteristic map is an embedding. -/
private theorem compactOpenSierpinskiMap_isEmbedding (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : IsEmbedding (compactOpenSierpinskiMap X) :=
  .mk (compactOpenSierpinskiMap_isInducing X) (compactOpenSierpinskiMap_injective X)

/-- Helper for Lemma 5.23.13: finite intersections of compact opens are open. -/
private theorem compactOpen_inter_isOpen {X : Type u} [TopologicalSpace X]
    (s : Finset (CompactOpens X)) : IsOpen (⋂ U ∈ s, (U : Set X)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons U s hU ih =>
      simpa [hU] using U.isOpen.inter ih

/-- Helper for Lemma 5.23.13: finite intersections of compact opens remain compact in a
quasi-separated space. -/
private theorem compactOpen_inter_isCompact {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] (s : Finset (CompactOpens X)) :
    IsCompact (⋂ U ∈ s, (U : Set X)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using (isCompact_univ : IsCompact (Set.univ : Set X))
  | cons U s hU ih =>
      have hsOpen : IsOpen (⋂ V ∈ s, (V : Set X)) := compactOpen_inter_isOpen s
      simpa [hU] using U.isCompact.inter_of_isOpen ih U.isOpen hsOpen

/-- Helper for Lemma 5.23.13: the preimage of a finite `true`-cylinder is the corresponding finite
intersection of compact opens. -/
private theorem preimage_compactOpenSierpinskiMap_trueCylinder {X : Type u} [TopologicalSpace X]
    (s : Finset (CompactOpens X)) :
    (compactOpenSierpinskiMap X) ⁻¹' trueCylinder s = ⋂ U ∈ s, (U : Set X) := by
  ext x
  simp [compactOpenSierpinskiMap, trueCylinder]

/-- Helper for Lemma 5.23.13: the compact-open characteristic map is spectral. -/
private theorem compactOpenSierpinskiMap_isSpectralMap (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : IsSpectralMap (compactOpenSierpinskiMap X) := by
  classical
  let f := compactOpenSierpinskiMap X
  refine ⟨f.continuous, ?_⟩
  intro s hsOpen hsCompact
  let b : Set (Finset (CompactOpens X)) := {t | trueCylinder t ⊆ s}
  -- Cover the compact open target set by basis cylinders that already lie inside it.
  have hcover : s ⊆ ⋃ t ∈ b, trueCylinder t := by
    intro y hy
    obtain ⟨v, ⟨t, rfl⟩, hyv, hvs⟩ :=
      (trueCylinder_isTopologicalBasis (ι := CompactOpens X)).isOpen_iff.mp hsOpen y hy
    exact mem_iUnion.2 ⟨t, mem_iUnion.2 ⟨hvs, hyv⟩⟩
  obtain ⟨b', hb'b, hb'finite, hs_sub⟩ :=
    hsCompact.elim_finite_subcover_image (b := b) (c := trueCylinder)
      (fun t ht => trueCylinder_isOpen t) hcover
  have hsub' : ⋃ t ∈ b', trueCylinder t ⊆ s := by
    intro y hy
    rcases mem_iUnion.1 hy with ⟨t, hy⟩
    rcases mem_iUnion.1 hy with ⟨ht, hyt⟩
    exact hb'b ht hyt
  have hEq : s = ⋃ t ∈ b', trueCylinder t := subset_antisymm hs_sub hsub'
  have hpreEq : f ⁻¹' s = ⋃ t ∈ b', f ⁻¹' trueCylinder t := by
    ext x
    simp [hEq]
  rw [hpreEq]
  exact hb'finite.isCompact_biUnion fun t ht => by
    rw [preimage_compactOpenSierpinskiMap_trueCylinder]
    exact compactOpen_inter_isCompact t

-- Proof sketch: for the forward implication, use the compact-open characteristic map
-- `X → CompactOpens X → Prop`; it is an embedding because compact opens form a basis, and it is
-- spectral because compact opens in the codomain are finite unions of finite coordinate cylinders.
-- For the reverse implication, show that every Sierpinski product is spectral by comparing it with
-- the inverse limit of its finite-coordinate restriction system, then transfer spectrality back
-- from the constructibly closed range via the embedding homeomorphism.
/-- Lemma 5.23.13: a space is spectral if and only if it embeds into a product of copies of the
Sierpinski space `Prop` with range closed in the constructible topology on that product. -/
theorem spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology :
    SpectralSpace X ↔
      ∃ (ι : Type u) (f : C(X, ι → Prop)),
        IsEmbedding f ∧
          IsClosed[constructibleTopology (ι → Prop)] (range f) := by
  constructor
  · intro hX
    letI : SpectralSpace X := hX
    letI : SpectralSpace (CompactOpens X → Prop) := spectralSpaceSierpinskiProduct
    -- The source proof uses quasi-compact opens as coordinates, which is exactly `CompactOpens X`.
    refine
      ⟨CompactOpens X, compactOpenSierpinskiMap X, compactOpenSierpinskiMap_isEmbedding X, ?_⟩
    exact (compactOpenSierpinskiMap_isSpectralMap X).isClosed_range_constructibleTopology
  · rintro ⟨ι, f, hf, hclosed⟩
    letI : SpectralSpace (ι → Prop) := spectralSpaceSierpinskiProduct
    have hRangeSpectral : SpectralSpace (range f) :=
      spectralSpace_subtype_of_isClosed_constructibleTopology hclosed
    have hpre : (f ⁻¹' range f : Set X) = Set.univ := by
      ext x
      simp
    let ePre : (f ⁻¹' range f) ≃ₜ range f :=
      hf.homeomorphOfSubsetRange (s := range f) (by intro y hy; exact hy)
    let eRange : (Set.univ : Set X) ≃ₜ range f := by
      -- The embedding identifies `X` with its range because the preimage of the range is `univ`.
      exact (Homeomorph.setCongr hpre.symm).trans ePre
    let e : X ≃ₜ range f := (Homeomorph.Set.univ X).symm.trans eRange
    letI : SpectralSpace (range f) := hRangeSpectral
    letI : CompactSpace X := e.symm.compactSpace
    exact e.isOpenEmbedding.spectralSpace

end
