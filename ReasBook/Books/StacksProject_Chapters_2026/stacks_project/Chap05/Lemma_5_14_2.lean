module

public import Mathlib.Topology.Sets.Compacts
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Category.TopCat.Opens

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v u}} {C : Cone F}

/-
Domain-style sampling for cofiltered limits in `TopCat`:
- owner abstraction for the limit topology:
  `TopCat.isTopologicalBasis_cofiltered_limit`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open`,
  `IsCompact.elim_finite_subcover`

Source/core/bridge triage:
- `source-facing`: the Stacks statements that opens in a cofiltered limit are unions of stagewise
  pullbacks, and that quasi-compact opens descend to a single stage;
- `core/canonical`: the basis owner
  `TopCat.isTopologicalBasis_cofiltered_limit`, specialized here to the basis of all open subsets
  on each stage;
- `bridge/view`: the resulting stagewise union and single-stage pullback descriptions.

Primitive data is only the canonical basis on the limiting cone point. The displayed union and
single-stage descent statements are derived API from that owner and from compactness, so the file
should reuse the owner basis directly rather than introducing a parallel public wrapper.
-/

private def projectionPreimageBasis (C : Cone F) : Set (Set C.pt) :=
  {W : Set C.pt | ∃ (j : J) (U : Opens (F.obj j)), W = C.π.app j ⁻¹' (U : Set (F.obj j))}

private theorem isTopologicalBasis_projectionPreimageBasis (hC : IsLimit C) :
    IsTopologicalBasis (projectionPreimageBasis C) := by
  rw [show projectionPreimageBasis C =
      {W : Set C.pt | ∃ (j : J) (U : Set (F.obj j)), IsOpen U ∧ W = C.π.app j ⁻¹' U} by
      ext W
      constructor
      · rintro ⟨j, U, rfl⟩
        exact ⟨j, (U : Set (F.obj j)), U.isOpen, rfl⟩
      · rintro ⟨j, U, hU, rfl⟩
        exact ⟨j, ⟨U, hU⟩, rfl⟩]
  simpa using
    (TopCat.isTopologicalBasis_cofiltered_limit.{u, v, w} F C hC
      (fun j ↦ {U : Set (F.obj j) | IsOpen U})
      (fun _ ↦ isTopologicalBasis_opens)
      (fun _ ↦ isOpen_univ)
      (fun _ _ _ hU₁ hU₂ ↦ hU₁.inter hU₂)
      (fun _ _ f _ hU ↦ hU.preimage (F.map f).hom.continuous))

-- Proof sketch: apply `TopCat.isTopologicalBasis_cofiltered_limit` with the basis of all open sets
-- on each `F.obj j`; then use `IsTopologicalBasis.open_eq_sUnion` to write an open subset of the
-- limit as a union of basic opens, each of which is the preimage of an open subset from one stage.
/-- Lemma 5.14.2 (1): every open subset of a cofiltered limit of topological spaces is a union of
preimages of open subsets from the spaces in the diagram. -/
theorem open_eq_iUnion_preimage_of_isLimit (hC : IsLimit C) (W : Opens C.pt) :
    ∃ U : ∀ j, Opens (F.obj j), (W : Set C.pt) = ⋃ j, C.π.app j ⁻¹' (U j : Set (F.obj j)) := by
  let hBasis := isTopologicalBasis_projectionPreimageBasis hC
  let U : ∀ j, Opens (F.obj j) := fun j ↦
    ⟨⋃₀ {V : Set (F.obj j) | IsOpen V ∧ C.π.app j ⁻¹' V ⊆ (W : Set C.pt)},
      isOpen_sUnion fun V hV ↦ hV.1⟩
  refine ⟨U, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨B, hB, hxB, hBW⟩ := hBasis.exists_subset_of_mem_open hx W.isOpen
      rcases hB with ⟨j, V, rfl⟩
      refine mem_iUnion.2 ⟨j, ?_⟩
      exact mem_preimage.2 <| mem_sUnion.2 ⟨V, ⟨V.isOpen, hBW⟩, mem_preimage.1 hxB⟩
    · intro hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨j, hx⟩
      rcases mem_sUnion.1 (mem_preimage.1 hx) with ⟨V, hV, hxV⟩
      exact hV.2 (show x ∈ C.π.app j ⁻¹' V from hxV)

-- Proof sketch: use the canonical preimage basis on the limit together with
-- `eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open` to write the quasi-compact open as a
-- finite union of projection-pullback basic opens; then use cofilteredness to dominate the
-- finitely many stages and pull everything back to a single open subset upstairs.
/-- Lemma 5.14.2 (2): every quasi-compact open subset of a cofiltered limit of topological spaces
is the preimage of an open subset from a single space in the diagram. -/
theorem compact_open_eq_preimage_of_isLimit (hC : IsLimit C) (W : CompactOpens C.pt) :
    ∃ (j : J) (U : Opens (F.obj j)), (W : Set C.pt) = C.π.app j ⁻¹' (U : Set (F.obj j)) := by
  classical
  have hBasis : IsTopologicalBasis (projectionPreimageBasis C) :=
    isTopologicalBasis_projectionPreimageBasis hC
  obtain ⟨s, hsW⟩ :=
    eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open
      (projectionPreimageBasis C) hBasis
      (W : Set C.pt) W.isCompact W.isOpen
  choose j U hU_eq using fun V : s ↦ V.1.2
  let G : Finset J := Finset.univ.image j
  obtain ⟨j₀, hj₀⟩ := IsCofiltered.inf_objs_exists G
  have hj : ∀ V : s, j V ∈ G := fun V ↦ Finset.mem_image.mpr ⟨V, Finset.mem_univ _, rfl⟩
  let g : ∀ V : s, j₀ ⟶ j V := fun V ↦ (hj₀ (hj V)).some
  let U₀ : Opens (F.obj j₀) := ⨆ V : s, (Opens.map (F.map (g V))).obj (U V)
  have hπ {i j : J} (f : i ⟶ j) (x : C.pt) :
      C.π.app j x = F.map f (C.π.app i x) := by
    rw [← CategoryTheory.comp_apply]
    exact congrArg (fun g : C.pt ⟶ F.obj j ↦ g x) (C.w f).symm
  refine ⟨j₀, U₀, ?_⟩
  ext x
  constructor
  · intro hx
    rw [hsW] at hx
    rcases mem_sUnion.1 hx with ⟨V, hVs, hxV⟩
    rcases hVs with ⟨V', hV's, rfl⟩
    let V'' : s := ⟨V', hV's⟩
    rw [hU_eq V''] at hxV
    refine mem_preimage.2 <| Opens.mem_iSup.2 ⟨V'', ?_⟩
    change F.map (g V'') (C.π.app j₀ x) ∈ U V''
    rw [← hπ (g V'') x]
    exact mem_preimage.1 hxV
  · intro hx
    have hxU₀ : C.π.app j₀ x ∈ U₀ := mem_preimage.1 hx
    rw [Opens.mem_iSup] at hxU₀
    rcases hxU₀ with ⟨V, hxV⟩
    rw [hsW]
    refine mem_sUnion.2 ⟨V.1.1, ⟨V.1, V.2, rfl⟩, ?_⟩
    rw [hU_eq V]
    refine mem_preimage.2 ?_
    change F.map (g V) (C.π.app j₀ x) ∈ U V at hxV
    exact (hπ (g V) x).symm ▸ hxV
