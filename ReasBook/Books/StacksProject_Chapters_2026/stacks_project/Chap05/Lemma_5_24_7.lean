module

public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.NNReal.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.NhdsKer
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_5
import stacks_project.Chap05.Lemma_5_24_1
import stacks_project.Chap05.Lemma_5_24_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits
open TopologicalSpace.Opens

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- Helper for Lemma 5.24.7: every constructible-topology open neighborhood contains a
constructible neighborhood of each of its points. -/
theorem exists_constructible_subset_of_mem_open_constructibleTopology
    {U : Set X} (hU : IsOpen[constructibleTopology X] U) {x : X} (hx : x ∈ U) :
    ∃ C : Set X, IsConstructible C ∧ x ∈ C ∧ C ⊆ U := by
  -- Route correction: instead of separating by later chapter API, induct directly on the
  -- `GenerateOpen` presentation of the constructible topology.
  change TopologicalSpace.GenerateOpen (constructibleTopologySubbasis X) U at hU
  induction hU generalizing x with
  | basic s hs =>
      rcases hs with hs | hs
      · -- A compact open subbasic set is already constructible.
        exact ⟨s, hs.2.isConstructible hs.1, hx, subset_rfl⟩
      · -- The complementary subbasic sets are complements of compact opens, hence constructible.
        have hs_compl_constructible : IsConstructible sᶜ := by
          exact hs.2.isConstructible hs.1.isOpen_compl
        exact ⟨s, by simpa using hs_compl_constructible.compl, hx, subset_rfl⟩
  | univ =>
      -- The whole space is constructible because a spectral space is quasi-compact.
      exact ⟨univ, isCompact_univ.isConstructible isOpen_univ, by simp, subset_rfl⟩
  | inter s t hs ht ihs iht =>
      rcases hx with ⟨hxS, hxT⟩
      rcases ihs hxS with ⟨Cs, hCs_constructible, hxCs, hCs_subset⟩
      rcases iht hxT with ⟨Ct, hCt_constructible, hxCt, hCt_subset⟩
      -- Intersect the two constructible neighborhoods supplied by the induction hypotheses.
      exact
        ⟨Cs ∩ Ct, hCs_constructible.inter hCt_constructible, ⟨hxCs, hxCt⟩,
          Set.inter_subset_inter hCs_subset hCt_subset⟩
  | sUnion S hS ih =>
      rcases Set.mem_sUnion.mp hx with ⟨V, hV, hxV⟩
      rcases ih V hV hxV with ⟨C, hC, hxC, hCU⟩
      -- A point of a union already lies in one stage, so keep the stagewise constructible witness.
      exact ⟨C, hC, hxC, hCU.trans (Set.subset_sUnion_of_mem hV)⟩

/-- In a spectral space, a subset is closed in the constructible topology exactly when it admits
the source-style presentation as an intersection of constructible subsets. -/
theorem isClosed_constructibleTopology_iff_eq_sInter_constructible (W : Set X) :
    IsClosed[constructibleTopology X] W ↔
      ∃ S : Set (Set X), (∀ Z ∈ S, IsConstructible Z) ∧ W = ⋂₀ S := by
  constructor
  · intro hW
    let S : Set (Set X) := { Z : Set X | IsConstructible Z ∧ W ⊆ Z }
    refine ⟨S, fun Z hZ ↦ hZ.1, ?_⟩
    apply subset_antisymm
    · intro x hx
      exact Set.mem_sInter.2 fun Z hZ ↦ hZ.2 hx
    · intro x hx
      by_contra hxW
      have hW_open : IsOpen[constructibleTopology X] Wᶜ := by
        let _ : TopologicalSpace X := constructibleTopology X
        exact hW.isOpen_compl
      obtain ⟨C, hC, hxC, hCW⟩ :=
        exists_constructible_subset_of_mem_open_constructibleTopology hW_open hxW
      have hC_compl_mem : Cᶜ ∈ S := by
        refine ⟨by simpa using hC.compl, ?_⟩
        intro y hyW hyC
        exact (hCW hyC) hyW
      have hxCcompl : x ∉ Cᶜ := by
        simpa using hxC
      exact hxCcompl (Set.mem_sInter.1 hx _ hC_compl_mem)
  · rintro ⟨S, hS, rfl⟩
    -- Constructible subsets are clopen in the constructible topology, so arbitrary intersections
    -- of them are constructibly closed.
    exact @isClosed_sInter X (constructibleTopology X) S fun Z hZ ↦
      (isClopen_constructibleTopology_of_isConstructible (hS Z hZ)).1

end

section

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for Lemma 5.24.7:
- primary domain: inverse limits in `TopCat` built from compact-open subspaces of a spectral space;
- inspected owner declarations:
  `CompactOpens`,
  `TopCat.nonempty_isLimit_iff_eq_induced`,
  `TopCat.isLimit_of_underlying_limit_of_preimage_basis`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction: the source-facing cone `compactOpenIntersectionCone W S hW`, with the
  chapter-level spectral-limit theorem reused only for the downstream spectrality consequence;
- primitive data: a subset `W`, a family `S : Set (CompactOpens X)`, and the equality
  `W = ⋂ U ∈ S, (U : Set X)`;
- derived API: the limiting-cone theorem and the resulting spectral-space instance on `W`.

Source/core/bridge triage:
- `source-facing`: the explicit cone exhibiting a directed nonempty intersection of compact opens
  as an inverse limit;
- `core/canonical`: `TopCat.nonempty_isLimit_iff_eq_induced` and
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- `bridge/view`: the internal comparison isomorphism from
  `IsLimit.conePointUniqueUpToIso` between the source-facing cone and `TopCat.limitCone`.

No earlier Chapter 5 file provides this exact compact-open intersection cone. The owner-level reuse
point is therefore the canonical `TopCat` limit criterion, not a replacement of the source-facing
cone by a parallel wrapper.
-/

/-- A point of an intersection presentation by compact opens lies in every displayed stage. -/
theorem mem_of_mem_iInter_compactOpens {W : Set X} {S : Set (CompactOpens X)}
    (hW : W = ⋂ U ∈ S, (U : Set X)) {x : X} (hx : x ∈ W) {U : CompactOpens X} (hU : U ∈ S) :
    x ∈ (U : Set X) := by
  rw [hW] at hx
  have hx' : ∀ V ∈ S, x ∈ (V : Set X) := by
    simpa [Set.mem_iInter] using hx
  exact hx' U hU

/-- The open-subspace diagram indexed by a family of compact opens, ordered by reverse inclusion. -/
def compactOpenDiagram (S : Set (CompactOpens X)) : S ⥤ Opens (TopCat.of X) where
  obj U := U.1.toOpens
  map hij := homOfLE hij.le
  map_id U := by
    simp
  map_comp hij hjk := by
    simp

/-- The `TopCat` diagram of compact-open stages attached to an intersection presentation. -/
abbrev compactOpenIntersectionDiagram (S : Set (CompactOpens X)) : S ⥤ TopCat :=
  compactOpenDiagram S ⋙ Opens.toTopCat (TopCat.of X)

def compactOpenIntersectionConeApp
    (W : Set X) (S : Set (CompactOpens X)) (hW : W = ⋂ U ∈ S, (U : Set X)) (U : S) :
    TopCat.of W ⟶ (compactOpenIntersectionDiagram S).obj U :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, mem_of_mem_iInter_compactOpens hW x.2 U.2⟩,
      continuous_subtype_val.subtype_mk
        (fun x ↦ mem_of_mem_iInter_compactOpens hW x.2 U.2)⟩

/-- The canonical cone from an intersection subtype to the diagram of the corresponding compact
open subspaces. -/
def compactOpenIntersectionCone
    (W : Set X) (S : Set (CompactOpens X)) (hW : W = ⋂ U ∈ S, (U : Set X)) :
    Cone (compactOpenIntersectionDiagram S) where
  pt := TopCat.of W
  π :=
    { app := compactOpenIntersectionConeApp W S hW
      naturality := by
        intro U V hUV
        ext x
        rfl }

theorem induced_compactOpenIntersectionConeApp
    (W : Set X) (S : Set (CompactOpens X)) (hW : W = ⋂ U ∈ S, (U : Set X)) (U : S) :
    TopologicalSpace.induced (compactOpenIntersectionConeApp W S hW U)
      ((compactOpenIntersectionDiagram S).obj U).str = (TopCat.of W).str := by
  change TopologicalSpace.induced (compactOpenIntersectionConeApp W S hW U)
      (TopologicalSpace.induced Subtype.val inferInstance) =
    TopologicalSpace.induced Subtype.val inferInstance
  rw [induced_compose]
  rfl

theorem val_eq_of_section_of_compactOpenIntersectionDiagram
    (S : Set (CompactOpens X)) (hDirected : DirectedOn (· ≥ ·) S)
    (s : ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).sections) (U V : S) :
    ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) U).1 =
      ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) V).1 := by
  obtain ⟨Z, hZS, hZU, hZV⟩ := hDirected U.1 U.2 V.1 V.2
  let Z' : S := ⟨Z, hZS⟩
  have hZU_eq :
      (((compactOpenIntersectionDiagram S).map (show Z' ⟶ U from homOfLE hZU))
        ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
      (s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) U :=
    s.2 (show Z' ⟶ U from homOfLE hZU)
  have hZV_eq :
      (((compactOpenIntersectionDiagram S).map (show Z' ⟶ V from homOfLE hZV))
        ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
      (s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) V :=
    s.2 (show Z' ⟶ V from homOfLE hZV)
  have hZU_val :
      Subtype.val
          (((compactOpenIntersectionDiagram S).map (show Z' ⟶ U from homOfLE hZU))
            ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
        Subtype.val
          ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) U) := by
    simpa [compactOpenIntersectionDiagram, compactOpenDiagram] using congrArg Subtype.val hZU_eq
  have hZV_val :
      Subtype.val
          (((compactOpenIntersectionDiagram S).map (show Z' ⟶ V from homOfLE hZV))
            ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) Z')) =
        Subtype.val
          ((s : ∀ T : S, ((compactOpenIntersectionDiagram S) ⋙ forget TopCat).obj T) V) := by
    simpa [compactOpenIntersectionDiagram, compactOpenDiagram] using congrArg Subtype.val hZV_eq
  exact hZU_val.symm.trans hZV_val

def isLimit_compactOpenIntersectionCone_of_directed_forget
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    IsLimit ((forget TopCat).mapCone (compactOpenIntersectionCone W S hW)) := by
  classical
  let F : S ⥤ Type _ := (compactOpenIntersectionDiagram S) ⋙ forget TopCat
  refine Classical.choice <| (Types.isLimit_iff_bijective_sectionOfCone _).2 ?_
  let U₀ : S := Classical.choice hS_nonempty.to_subtype
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hU₀ :
        ((Types.sectionOfCone ((forget TopCat).mapCone (compactOpenIntersectionCone W S hW)) x).1 U₀) =
          ((Types.sectionOfCone ((forget TopCat).mapCone (compactOpenIntersectionCone W S hW))
            y).1 U₀) := by
      exact congrArg (fun t ↦ t.1 U₀) hxy
    apply Subtype.ext
    simpa only [Types.sectionOfCone, Functor.mapCone_pt, compactOpenIntersectionCone,
      compactOpenIntersectionConeApp] using congrArg Subtype.val hU₀
  · intro s
    let x : X := ((s : ∀ U : S, F.obj U) U₀).1
    have hx_mem : ∀ V : CompactOpens X, V ∈ S → x ∈ (V : Set X) := by
      intro V hV
      have hUV :
          x = ((s : ∀ U : S, F.obj U) ⟨V, hV⟩).1 := by
        simpa [F, x] using
          val_eq_of_section_of_compactOpenIntersectionDiagram S hDirected s U₀ ⟨V, hV⟩
      exact hUV ▸ ((s : ∀ U : S, F.obj U) ⟨V, hV⟩).2
    have hxW : x ∈ W := by
      rw [hW]
      simpa [Set.mem_iInter] using hx_mem
    refine ⟨⟨x, hxW⟩, ?_⟩
    apply Subtype.ext
    funext V
    apply Subtype.ext
    change x = ((s : ∀ U : S, F.obj U) V).1
    simpa [F, x] using
      val_eq_of_section_of_compactOpenIntersectionDiagram S hDirected s U₀ V

theorem compactOpenIntersectionCone_pt_eq_iInf_induced
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) :
    (compactOpenIntersectionCone W S hW).pt.str =
      ⨅ U : S, ((compactOpenIntersectionDiagram S).obj U).str.induced
        ((compactOpenIntersectionCone W S hW).π.app U) := by
  classical
  let U₀ : S := Classical.choice hS_nonempty.to_subtype
  have hinduced :
      ∀ U : S,
        ((compactOpenIntersectionDiagram S).obj U).str.induced
            ((compactOpenIntersectionCone W S hW).π.app U) =
          (compactOpenIntersectionCone W S hW).pt.str := by
    intro U
    simpa [compactOpenIntersectionCone] using induced_compactOpenIntersectionConeApp W S hW U
  apply le_antisymm
  · exact le_iInf fun U ↦ (hinduced U).ge
  · exact (iInf_le (fun U : S ↦
      ((compactOpenIntersectionDiagram S).obj U).str.induced
        ((compactOpenIntersectionCone W S hW).π.app U)) U₀).trans (hinduced U₀).le

/-- Lemma 5.24.7 (b): a directed nonempty intersection of quasi-compact opens is the inverse
limit of the associated diagram of open subspaces, expressed by the canonical cone. -/
def isLimit_compactOpenIntersectionCone_of_directed
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    IsLimit (compactOpenIntersectionCone W S hW) := by
  classical
  let hforget :=
    isLimit_compactOpenIntersectionCone_of_directed_forget W S hS_nonempty hW hDirected
  exact Classical.choice <|
    (TopCat.nonempty_isLimit_iff_eq_induced (compactOpenIntersectionCone W S hW) hforget).2
      (compactOpenIntersectionCone_pt_eq_iInf_induced W S hS_nonempty hW)

end

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

-- Proof sketch: compare the five clauses by the Stacks argument. Constructible-topology closedness
-- gives quasi-compactness via the compact constructible topology; quasi-compact generalizing
-- subsets are sets of specializations of quasi-compact subsets and hence intersections of
-- quasi-compact opens; finite-intersection refinements package such intersections into a directed
-- family of compact opens.
/-- A subset presented as an intersection of constructible subsets. -/
def constructibleIntersectionPresentation (W : Set X) : Prop :=
  ∃ S : Set (Set X), (∀ Z ∈ S, IsConstructible Z) ∧ W = ⋂₀ S

/-- Lemma 5.24.7 (1): `W` is an intersection of constructible subsets and is stable under
generalization. -/
def compactGeneralizingClause1 (W : Set X) : Prop :=
  constructibleIntersectionPresentation W ∧ StableUnderGeneralization W

/-- Lemma 5.24.7 (2): `W` is quasi-compact and is stable under generalization. -/
def compactGeneralizingClause2 (W : Set X) : Prop :=
  IsCompact W ∧ StableUnderGeneralization W

/-- Lemma 5.24.7 (3): `W` is the set of points specializing to a quasi-compact subset. -/
def compactGeneralizingClause3 (W : Set X) : Prop :=
  ∃ E : Set X, IsCompact E ∧ W = nhdsKer E

/-- Lemma 5.24.7 (4): `W` is an intersection of quasi-compact open subsets. -/
def compactGeneralizingClause4 (W : Set X) : Prop :=
  ∃ S : Set (CompactOpens X), W = ⋂ U ∈ S, (U : Set X)

/-- A subset is the directed intersection of the displayed family of compact open subsets. -/
def IsDirectedCompactOpenIntersection
    (W : Set X) (S : Set (CompactOpens X)) : Prop :=
  W = ⋂ U ∈ S, (U : Set X) ∧ DirectedOn (· ≥ ·) S

/-- Lemma 5.24.7 (5): `W` is the intersection of a directed nonempty family of quasi-compact
open subsets. -/
def compactGeneralizingClause5 (W : Set X) : Prop :=
  ∃ S : Set (CompactOpens X), S.Nonempty ∧ IsDirectedCompactOpenIntersection W S

/-- Helper for Lemma 5.24.7: the specialization closure `nhdsKer E` of a compact subset is the
intersection of all compact opens containing that subset. -/
theorem nhdsKer_eq_iInter_compactOpens_of_isCompact (E : Set X) (hE : IsCompact E) :
    nhdsKer E = ⋂ U ∈ { V : CompactOpens X | E ⊆ (V : Set X) }, (U : Set X) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iInter]
    intro U
    rw [Set.mem_iInter]
    intro hEU
    have hx_singleton : ({x} : Set X) ⊆ nhdsKer E := by
      simpa [Set.singleton_subset_iff] using hx
    exact (subset_nhdsKer_iff.mp hx_singleton) (U : Set X) U.isOpen hEU (by simp)
  · intro hx
    -- To prove `x ∈ nhdsKer E`, it suffices to check every open neighborhood of `E`.
    rw [← Set.singleton_subset_iff, subset_nhdsKer_iff]
    intro O hO hEO
    obtain ⟨V, hV_compact, hV_open, hEV, hVO⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between hE hO hEO
    let K : CompactOpens X := ⟨⟨V, hV_compact⟩, hV_open⟩
    have hxK : x ∈ (K : Set X) := by
      have hx' :
          ∀ U : CompactOpens X, U ∈ { V : CompactOpens X | E ⊆ (V : Set X) } →
            x ∈ (U : Set X) := by
        simpa [Set.mem_iInter] using hx
      exact hx' K hEV
    exact Set.singleton_subset_iff.2 (hVO hxK)

-- Proof sketch: prove the TFAE chain from the Stacks argument, using
-- `isClosed_constructibleTopology_iff_eq_sInter_constructible` to pass between constructible
-- presentations and constructible-topology closedness, and then the compact-open intersection
-- criteria developed above.
/-- The five clause predicates attached to Lemma 5.24.7 are equivalent. -/
theorem compact_generalizing_subset_tfae (W : Set X) :
    List.TFAE
      [ compactGeneralizingClause1 W,
        compactGeneralizingClause2 W,
        compactGeneralizingClause3 W,
        compactGeneralizingClause4 W,
        compactGeneralizingClause5 W ] :=
  by
  tfae_have 1 → 2 := by
    rintro ⟨hPresentation, hGen⟩
    have hPatchClosed : IsClosed[constructibleTopology X] W := by
      exact (isClosed_constructibleTopology_iff_eq_sInter_constructible W).2 hPresentation
    have hPatchCompact : @IsCompact X (constructibleTopology X) W := by
      exact
        @IsClosed.isCompact X (constructibleTopology X)
          W constructibleTopology_compactSpace_of_spectralSpace hPatchClosed
    have hContToOriginal : @Continuous X X (constructibleTopology X) ‹TopologicalSpace X› id := by
      rw [continuous_def]
      intro s hs
      exact isOpen_constructibleTopology_of_isOpen_spectralSpaceDiagram hs
    -- Transport compactness back to the original topology along the identity map.
    refine ⟨by
      simpa using
        @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X› W id
          hPatchCompact hContToOriginal, hGen⟩
  tfae_have 2 → 3 := by
    rintro ⟨hCompact, hGen⟩
    refine ⟨W, hCompact, ?_⟩
    apply subset_antisymm
    · exact subset_nhdsKer
    · intro x hx
      rcases mem_nhdsKer_iff_specializes.mp hx with ⟨y, hyW, hxy⟩
      exact hGen hxy hyW
  tfae_have 3 → 5 := by
    rintro ⟨E, hE, rfl⟩
    let S : Set (CompactOpens X) := { U : CompactOpens X | E ⊆ (U : Set X) }
    refine ⟨S, ?_, ?_⟩
    · exact ⟨⊤, by simp [S]⟩
    · refine ⟨nhdsKer_eq_iInter_compactOpens_of_isCompact E hE, ?_⟩
      intro U hU V hV
      refine ⟨U ⊓ V, ?_, inf_le_left, inf_le_right⟩
      intro x hx
      simpa [CompactOpens.coe_inf] using ⟨hU hx, hV hx⟩
  tfae_have 5 → 4 := by
    rintro ⟨S, _hS, hWS⟩
    exact ⟨S, hWS.1⟩
  tfae_have 4 → 1 := by
    rintro ⟨S, hW⟩
    let T : Set (Set X) := Set.range fun U : S ↦ ((U.1 : CompactOpens X) : Set X)
    refine ⟨?_, ?_⟩
    · refine ⟨T, ?_, ?_⟩
      · intro Z hZ
        rcases hZ with ⟨U, rfl⟩
        exact U.1.isCompact.isConstructible U.1.isOpen
      · ext x
        rw [hW]
        simp [T, Set.mem_iInter]
    · intro x y hxy hy
      rw [hW] at hy ⊢
      have hy' : ∀ V : CompactOpens X, V ∈ S → x ∈ (V : Set X) := by
        simpa [Set.mem_iInter] using hy
      exact
        Set.mem_iInter.2 fun V ↦
          Set.mem_iInter.2 fun hV ↦
            V.isOpen.stableUnderGeneralization hxy (hy' V hV)
  tfae_finish

/-- Lemma 5.24.7 (a): a directed nonempty intersection of quasi-compact opens in a spectral
space is spectral. -/
theorem spectralSpace_of_compactOpenDirectedIntersection
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) :
    SpectralSpace W := by
  letI : Nonempty S := hS_nonempty.to_subtype
  letI : IsCodirectedOrder S :=
    directedOn_univ_iff.mp fun U _ V _ ↦ by
      obtain ⟨Z, hZS, hZU, hZV⟩ := hDirected U.1 U.2 V.1 V.2
      exact ⟨⟨Z, hZS⟩, trivial, hZU, hZV⟩
  letI (U : S) : SpectralSpace ↥((compactOpenIntersectionDiagram S).obj U) := by
    letI : CompactSpace ↥((Opens.toTopCat (TopCat.of X)).obj U.1.toOpens) := by
      change CompactSpace ↥(U.1.toOpens)
      exact isCompact_iff_compactSpace.mp U.1.isCompact
    let V : Opens (TopCat.of X) := U.1.toOpens
    have hOpenEmbedding : IsOpenEmbedding (Opens.inclusion' V) :=
      Opens.isOpenEmbedding V
    exact hOpenEmbedding.spectralSpace
  have hF : ∀ ⦃U V : S⦄ (hUV : U ⟶ V), IsSpectralMap ((compactOpenIntersectionDiagram S).map hUV) := by
    intro U V hUV
    have hOpenEmbedding :
        IsOpenEmbedding ((compactOpenIntersectionDiagram S).map hUV) := by
      simpa [compactOpenIntersectionDiagram, compactOpenDiagram] using
        (Opens.isOpenEmbedding_of_le (show U.1.toOpens ≤ V.1.toOpens from hUV.le))
    refine ⟨hOpenEmbedding.continuous, fun T hT_open hT_comp ↦ ?_⟩
    have hT_retro : IsRetrocompact T :=
      (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hT_open).2 hT_comp
    have hpre_retro :
        IsRetrocompact (((compactOpenIntersectionDiagram S).map hUV) ⁻¹' T) :=
      hT_retro.preimage_of_isOpenEmbedding hOpenEmbedding
    exact
      (QuasiSeparatedSpace.isRetrocompact_iff_isCompact
        (hT_open.preimage hOpenEmbedding.continuous)).1 hpre_retro
  haveI : SpectralSpace ↥((TopCat.limitCone (compactOpenIntersectionDiagram S)).pt) :=
    spectralSpace_of_isLimit_of_cofiltered_spectral_diagram
      (TopCat.limitConeIsLimit (compactOpenIntersectionDiagram S)) hF
  have e : W ≃ₜ ↥((TopCat.limitCone (compactOpenIntersectionDiagram S)).pt) := by
    simpa [compactOpenIntersectionCone] using
      TopCat.homeoOfIso
        (IsLimit.conePointUniqueUpToIso
          (isLimit_compactOpenIntersectionCone_of_directed W S hS_nonempty hW hDirected)
          (TopCat.limitConeIsLimit (compactOpenIntersectionDiagram S)))
  letI : CompactSpace W := e.symm.compactSpace
  exact e.isOpenEmbedding.spectralSpace

-- Proof sketch: intersect each stage `U ∈ S` with the closed complement of the ambient open
-- neighborhood; the resulting constructible subsets have empty intersection in the spectral
-- complement, so quasi-compactness of the constructible topology yields one stage already
-- contained in the neighborhood.
/-- Lemma 5.24.7 (c): any open neighborhood of a directed nonempty compact-open intersection
contains one stage of the presentation. -/
theorem exists_stage_subset_of_isOpen_of_compactOpenDirectedIntersection
    (W : Set X) (S : Set (CompactOpens X)) (hS_nonempty : S.Nonempty)
    (hW : W = ⋂ U ∈ S, (U : Set X)) (hDirected : DirectedOn (· ≥ ·) S) {U : Set X}
    (hU : IsOpen U) (hWU : W ⊆ U) :
    ∃ V : CompactOpens X, V ∈ S ∧ (V : Set X) ⊆ U := by
  let Z : Set X := Uᶜ
  have hZ_closed_patch : IsClosed[constructibleTopology X] Z := by
    exact @IsOpen.isClosed_compl X (constructibleTopology X) U
      (isOpen_constructibleTopology_of_isOpen_spectralSpaceDiagram hU)
  let _ : SpectralSpace Z := spectralSpace_subtype_of_isClosed_constructibleTopology hZ_closed_patch
  let T : { V : CompactOpens X // V ∈ S } → Set Z := fun V ↦ Subtype.val ⁻¹' (V.1 : Set X)
  have hT_closed_patch :
      ∀ V : { V : CompactOpens X // V ∈ S }, IsClosed[constructibleTopology Z] (T V) := by
    intro V
    have hTV_open : IsOpen (T V) := V.1.isOpen.preimage continuous_subtype_val
    have hTV_compact : IsCompact (T V) := by
      have hImageCompact : IsCompact ((V.1 : Set X) ∩ Z) := by
        simpa [Z, Set.inter_comm] using V.1.isCompact.inter_right hU.isClosed_compl
      rw [Subtype.isCompact_iff]
      simpa [T, Set.image_preimage_eq_inter_range, Subtype.range_val, Set.inter_assoc,
        Set.inter_comm, Set.inter_left_comm] using hImageCompact
    have hTV_constructible : IsConstructible (T V) := hTV_compact.isConstructible hTV_open
    exact (isClopen_constructibleTopology_of_isConstructible hTV_constructible).1
  have hInter_empty : (⋂ V, T V) = (∅ : Set Z) := by
    ext z
    constructor
    · intro hz
      have hz_all : ∀ V : CompactOpens X, V ∈ S → (z : X) ∈ (V : Set X) := by
        intro V hV
        exact Set.mem_iInter.1 hz ⟨V, hV⟩
      have hzW : (z : X) ∈ W := by
        rw [hW]
        simpa [Set.mem_iInter] using hz_all
      exact (z.2 (hWU hzW)).elim
    · simp
  have hFinite_empty :
      ∃ t : Finset { V : CompactOpens X // V ∈ S }, (⋂ V ∈ t, T V) = (∅ : Set Z) := by
    have hPatchCompactZ : @CompactSpace Z (constructibleTopology Z) :=
      constructibleTopology_compactSpace_of_spectralSpace
    have hEmpty' : ((Set.univ : Set Z) ∩ ⋂ V, T V) = (∅ : Set Z) := by
      simp [hInter_empty]
    letI : TopologicalSpace Z := constructibleTopology Z
    letI : CompactSpace Z := hPatchCompactZ
    obtain ⟨t, ht⟩ :=
      (show IsCompact (Set.univ : Set Z) from isCompact_univ).elim_finite_subfamily_closed T
        (fun i ↦ show IsClosed (T i) from hT_closed_patch i) hEmpty'
    exact ⟨t, by simpa using ht⟩
  obtain ⟨t, ht⟩ := hFinite_empty
  have hRefine :
      ∀ t : Finset { V : CompactOpens X // V ∈ S },
        ∃ V : CompactOpens X, V ∈ S ∧ ∀ i ∈ t, V ≤ i.1 := by
    intro t
    classical
    induction t using Finset.induction_on with
    | empty =>
        rcases hS_nonempty with ⟨V, hV⟩
        exact ⟨V, hV, by intro i hi; simp at hi⟩
    | @insert i t hi ih =>
        rcases ih with ⟨V, hVS, hVle⟩
        obtain ⟨W', hW'S, hW'i, hW'V⟩ := hDirected i.1 i.2 V hVS
        refine ⟨W', hW'S, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjt
        · exact hW'i
        · exact hW'V.trans (hVle j hjt)
  obtain ⟨V, hVS, hVle⟩ := hRefine t
  have hTV_empty : T ⟨V, hVS⟩ = (∅ : Set Z) := by
    ext z
    constructor
    · intro hz
      have hzFinite : z ∈ ⋂ i ∈ t, T i := by
        refine Set.mem_iInter.2 fun i ↦ Set.mem_iInter.2 fun hi ↦ ?_
        exact hVle i hi hz
      have : False := by
        simp [ht] at hzFinite
      exact this.elim
    · simp
  refine ⟨V, hVS, ?_⟩
  intro x hxV
  by_contra hxU
  have hxTrace : (⟨x, hxU⟩ : Z) ∈ T ⟨V, hVS⟩ := hxV
  simp [hTV_empty] at hxTrace

end
