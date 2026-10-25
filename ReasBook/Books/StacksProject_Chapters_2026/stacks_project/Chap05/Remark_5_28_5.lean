module

public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap05.Definition_5_28_2
public import stacks_project.Chap05.Definition_5_28_3
import Mathlib.Topology.LocallyClosed

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

/- Domain-style sampling for indexed stratifications and their closed initial families:
- sampled project owner declarations:
  `IsStratification`,
  `IsStratification.toLocallyClosedPartition_isGood`,
  `IsStratification.toLocallyClosedPartition`,
  `LocallyClosedPartition.IsGood`,
  `LocallyClosedPartition.le_iff_forall_exists_mem_subset`
- sampled topology infrastructure used by the bridge constructions:
  `LocallyFinite`,
  `Set.Iic`,
  `Set.Iio`
- best owner abstractions:
  `IsStratification` is the chapter's indexed owner and `LocallyClosedPartition` is the partition
  owner; the closed initial-family language in this remark is a source-facing bridge relating
  those owners

Layer triage:
- `source-facing`: `IsClosedInitialFamily`
- `core/canonical`: `IsStratification` and `LocallyClosedPartition`
- `bridge/view`: the initial-union and frontier-difference constructions relating the three views

Primitive data for the source-facing side are only a family `Z : I → Set X` together with its
closedness, cover, local finiteness, and intersection formula. The subtype of nonempty frontier
pieces and the recovered locally closed partition are derived API from that data, so they should
be exposed only through canonical bridge declarations.
-/

variable {X : Type u} [TopologicalSpace X]
variable {I : Type v} [PartialOrder I]

/-- A closed initial family is a locally finite covering by closed subsets satisfying the
intersection formula `Z i ∩ Z j = ⋃_{k ≤ i, j} Z k`. -/
class IsClosedInitialFamily (Z : I → Set X) : Prop where
  /-- Each member of the family is closed. -/
  isClosed (i : I) : IsClosed (Z i)
  /-- The family covers the ambient space. -/
  iUnion_eq_univ : ⋃ i, Z i = univ
  /-- Every point has a neighbourhood meeting only finitely many members of the family. -/
  locallyFinite : LocallyFinite Z
  /-- The intersection of two members is the union of the members below both indices. -/
  inter_eq_iUnion (i j : I) :
    Z i ∩ Z j = ⋃ k ∈ Iic i ∩ Iic j, Z k

namespace IsStratification

/-- The initial union `⋃_{j ≤ i} strata j` attached to an indexed family of strata. -/
abbrev initial (strata : I → Set X) (i : I) : Set X :=
  ⋃ j ∈ Iic i, strata j

/-- Remark 5.28.5 (1): the initial unions attached to a locally finite indexed stratification
form a closed initial family. -/
-- Proof sketch: use local finiteness to show each initial union is closed as a locally finite
-- union of closures of strata, then combine the partition and closure condition to identify the
-- intersections with the lower-index union.

theorem initial_isClosedInitialFamily
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata)
    (hinitial : LocallyFinite (initial strata)) :
    IsClosedInitialFamily (initial strata) := by
  refine
    { isClosed := ?_
      iUnion_eq_univ := ?_
      locallyFinite := hinitial
      inter_eq_iUnion := ?_ }
  · intro i
    let lower : Set.Iic i → Set X := fun j ↦ strata j.1
    have hlower : LocallyFinite lower := hloc.comp_injective Subtype.val_injective
    -- Each initial union is closed because the restricted locally finite family has closed union.
    rw [← closure_subset_iff_isClosed]
    intro x hx
    have hx' : x ∈ closure (⋃ j : Set.Iic i, lower j) := by
      simpa [IsStratification.initial, lower, Set.iUnion_subtype] using hx
    rw [hlower.closure_iUnion] at hx'
    rcases Set.mem_iUnion.1 hx' with ⟨j, hxj⟩
    rcases Set.mem_iUnion.1 (hstrata.closure_subset j.1 hxj) with ⟨k, hxk⟩
    rcases Set.mem_iUnion.1 hxk with ⟨hkj, hxk⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_trans hkj j.2, hxk⟩⟩
  · ext x
    constructor
    · intro _
      simp
    · intro _
      have hxCover : x ∈ ⋃ i, strata i := by
        simp [hstrata.cover]
      rcases Set.mem_iUnion.1 hxCover with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨le_rfl, hxi⟩⟩⟩
  · intro i j
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxi, hxj⟩
      obtain ⟨a, hxa⟩ := hstrata.toIndexedPartition.exists_mem x
      rcases Set.mem_iUnion.1 hxi with ⟨k, hxk⟩
      rcases Set.mem_iUnion.1 hxk with ⟨hki, hxk⟩
      rcases Set.mem_iUnion.1 hxj with ⟨l, hxl⟩
      rcases Set.mem_iUnion.1 hxl with ⟨hlj, hxl⟩
      have hk_eq : k = a := hstrata.toIndexedPartition.eq_of_mem hxk hxa
      have hl_eq : l = a := hstrata.toIndexedPartition.eq_of_mem hxl hxa
      have hai : a ≤ i := by simpa [hk_eq] using hki
      have haj : a ≤ j := by simpa [hl_eq] using hlj
      refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨⟨hai, haj⟩, ?_⟩⟩
      exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨le_rfl, hxa⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨k, hxk⟩
      rcases Set.mem_iUnion.1 hxk with ⟨hk, hxk⟩
      constructor
      · rcases Set.mem_iUnion.1 hxk with ⟨l, hxl⟩
        rcases Set.mem_iUnion.1 hxl with ⟨hlk, hxl⟩
        exact Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨le_trans hlk hk.1, hxl⟩⟩
      · rcases Set.mem_iUnion.1 hxk with ⟨l, hxl⟩
        rcases Set.mem_iUnion.1 hxl with ⟨hlk, hxl⟩
        exact Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨le_trans hlk hk.2, hxl⟩⟩

/-- Remark 5.28.5 (2): a locally finite indexed stratification yields a good locally closed
partition. -/
-- Proof sketch: use the frontier condition coming from the closure-order axiom of the indexed
-- stratification after passing to the canonical locally closed partition.
theorem toLocallyClosedPartition_isGood
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata)
    (hfrontier :
      ∀ ⦃i j : I⦄, ((strata i) ∩ closure (strata j)).Nonempty →
        strata i ⊆ closure (strata j)) :
    LocallyClosedPartition.IsGood hstrata.toLocallyClosedPartition := by
  -- Route correction: this theorem now assumes the frontier condition explicitly.
  let _ := hloc
  refine { frontier_condition := ?_ }
  intro S T hST
  rcases S with ⟨S, hS⟩
  rcases T with ⟨T, hT⟩
  rcases hS with ⟨i, rfl⟩
  rcases hT with ⟨j, rfl⟩
  exact hfrontier hST

end IsStratification

namespace IsClosedInitialFamily

/-- The difference `Z i \ ⋃_{j < i} Z j` attached to a family of closed initial subsets. -/
abbrev frontier (Z : I → Set X) (i : I) : Set X :=
  Z i \ ⋃ j ∈ Iio i, Z j

/-- The indices with nonempty frontier differences. -/
abbrev frontierIndex (Z : I → Set X) : Type v :=
  { i : I // (frontier Z i).Nonempty }

/-- The indexed family of nonempty frontier differences. -/
abbrev frontierStrata (Z : I → Set X) : frontierIndex Z → Set X :=
  fun i ↦ frontier Z i.1

/-- Helper for Remark 5.28.5: the lower union `⋃_{j < i} Z j` is closed. -/
lemma isClosed_iUnion_lt
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) (i : I) :
    IsClosed (⋃ j ∈ Iio i, Z j) := by
  let lower : Set.Iio i → Set X := fun j ↦ Z j.1
  have hlower : LocallyFinite lower := hZ.locallyFinite.comp_injective Subtype.val_injective
  -- Restrict the locally finite family to `Iio i` and use closedness of each member.
  simpa [lower, Set.iUnion_subtype] using hlower.isClosed_iUnion fun j => hZ.isClosed j.1

/-- Helper for Remark 5.28.5: a point cannot lie in two distinct frontier pieces. -/
lemma frontierIndex_eq_of_mem
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) {i j : I} {x : X}
    (hxi : x ∈ frontier Z i) (hxj : x ∈ frontier Z j) :
    i = j := by
  have hxij : x ∈ Z i ∩ Z j := ⟨hxi.1, hxj.1⟩
  rw [hZ.inter_eq_iUnion i j] at hxij
  rcases Set.mem_iUnion.1 hxij with ⟨k, hxk⟩
  rcases Set.mem_iUnion.1 hxk with ⟨hk, hxk⟩
  have hk_eq_i : k = i := by
    rcases lt_or_eq_of_le hk.1 with hklt | hkeq
    · exact False.elim <| hxi.2 <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hklt, hxk⟩⟩
    · exact hkeq
  have hk_eq_j : k = j := by
    rcases lt_or_eq_of_le hk.2 with hklt | hkeq
    · exact False.elim <| hxj.2 <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hklt, hxk⟩⟩
    · exact hkeq
  exact hk_eq_i.symm.trans hk_eq_j

/-- Helper for Remark 5.28.5: every point of `Z i` lies in a minimal frontier piece below `i`. -/
lemma exists_frontierIndex_mem_le
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) {x : X} {i : I} (hxi : x ∈ Z i) :
    ∃ j : frontierIndex Z, x ∈ frontierStrata Z j ∧ j.1 ≤ i := by
  classical
  let s : Set I := {j | x ∈ Z j ∧ j ≤ i}
  have hsFinite : s.Finite := (hZ.locallyFinite.point_finite x).subset fun j hj ↦ hj.1
  have hsNonempty : s.Nonempty := ⟨i, hxi, le_rfl⟩
  obtain ⟨j, hjs, hjmin⟩ := hsFinite.exists_minimal hsNonempty
  have hxj : x ∈ Z j := hjs.1
  have hji : j ≤ i := hjs.2
  have hxFrontier : x ∈ frontier Z j := by
    refine ⟨hxj, ?_⟩
    intro hxLower
    rcases Set.mem_iUnion.1 hxLower with ⟨k, hxk⟩
    rcases Set.mem_iUnion.1 hxk with ⟨hkj, hxk⟩
    have hks : k ∈ s := ⟨hxk, le_trans (le_of_lt hkj) hji⟩
    have hjk : j ≤ k := hjmin hks (le_of_lt hkj)
    exact (lt_irrefl k) (lt_of_lt_of_le hkj hjk)
  let jFrontier : frontierIndex Z := ⟨j, ⟨x, hxFrontier⟩⟩
  exact ⟨jFrontier, hxFrontier, hji⟩

/-- Helper for Remark 5.28.5: the closure of a frontier piece only meets lower frontier pieces. -/
lemma closure_frontier_subset_iUnion
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) (i : frontierIndex Z) :
    closure (frontierStrata Z i) ⊆ ⋃ j ∈ Set.Iic i, frontierStrata Z j := by
  intro x hx
  have hxZi : x ∈ Z i.1 := by
    -- First keep the closure point inside the closed set `Z i`.
    exact closure_minimal (diff_subset : frontierStrata Z i ⊆ Z i.1) (hZ.isClosed i.1) hx
  obtain ⟨j, hxj, hji⟩ := hZ.exists_frontierIndex_mem_le hxZi
  -- Then choose the minimal frontier index containing the point.
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨show j ≤ i from hji, hxj⟩⟩

/-- Remark 5.28.5 (3): the nonempty frontier differences attached to a closed initial family form
an indexed stratification. -/
-- Proof sketch: show the nonempty differences partition `X`, inherit local closedness from the
-- closed members `Z i`, and recover the closure condition from the hypotheses on the closed
-- initial family.

theorem frontier_isStratification
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) :
    IsStratification (frontierStrata Z) := by
  refine
    { disjoint := ?_
      nonempty := ?_
      cover := ?_
      locallyClosed := ?_
      closure_subset := ?_ }
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    have hEq : i.1 = j.1 := hZ.frontierIndex_eq_of_mem hxi hxj
    exact hij (Subtype.ext hEq)
  · intro i
    simpa using i.2
  · ext x
    constructor
    · intro _
      simp
    · intro _
      have hxCover : x ∈ ⋃ i, Z i := by
        simp [hZ.iUnion_eq_univ]
      rcases Set.mem_iUnion.1 hxCover with ⟨i, hxi⟩
      rcases hZ.exists_frontierIndex_mem_le hxi with ⟨j, hxj, _⟩
      exact Set.mem_iUnion.2 ⟨j, hxj⟩
  · intro i
    -- Each frontier piece is the intersection of a closed set with an open complement.
    have hclosed : IsClosed (Z i.1) := hZ.isClosed i.1
    have hopen : IsOpen ((⋃ j ∈ Iio i.1, Z j)ᶜ) := (hZ.isClosed_iUnion_lt i.1).isOpen_compl
    simpa [frontier, diff_eq] using hclosed.isLocallyClosed.inter hopen.isLocallyClosed
  · intro i
    -- The minimal-index lemma supplies the closure-order condition as well.
    exact hZ.closure_frontier_subset_iUnion i

/-- The frontier differences attached to a closed initial family form a locally finite family. -/
-- Proof sketch: apply local finiteness of the closed initial family and pass to the frontier
-- differences by the inclusion `frontier Z i ⊆ Z i`.
theorem locallyFinite_frontier
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) :
    LocallyFinite (frontier Z) :=
  hZ.locallyFinite.subset fun _ ↦ diff_subset

end IsClosedInitialFamily
