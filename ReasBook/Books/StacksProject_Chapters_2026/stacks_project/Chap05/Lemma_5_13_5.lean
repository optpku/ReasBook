module

public import Mathlib.Topology.Sets.OpenCover
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Compactness.Paracompact
import stacks_project.Chap05.Lemma_5_13_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u v w z

section

variable {X : Type u} [TopologicalSpace X]

variable [CompactSpace X] [T2Space X]
variable {ι : Type v}

/- Domain-style sampling for tuplewise shrinking of open covers:
- primary domain: shrinking lemmas for open covers in compact normal spaces
- source-facing owner for the ambient cover data: `TopologicalSpace.IsOpenCover`
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.exists_shrinking`,
  `exists_iUnion_eq_closure_subset`,
  `TopologicalSpace.IsOpenCover.comap`,
  `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`

Layer triage:
- `source-facing`: the Stacks tuplewise shrinking statement below
- `core/canonical`: the fixed-cover owner `TopologicalSpace.IsOpenCover`
- `bridge/view`: the prescribed tuplewise ambient open families, viewed only as covers of the
  corresponding finite intersections

Primitive data are only the open cover `U` and the prescribed tuplewise cover family `W`. The
covering property of each tuplewise family is the equality
`⋂ a, U (s a) = ⋃ k, W s k`; the shrinking family, its closure control, and the tuplewise
subordination are derived theorem output, so they should not be packaged into a separate public
structure or a second exact-interface wrapper theorem. The public statement keeps the source-facing
compact Hausdorff hypotheses, while normality is left implicit for the later proof through the
standard compact-Hausdorff-to-normal instance.
-/

namespace TopologicalSpace.IsOpenCover

/-- Helper for Lemma 5.13.5: every member of a prescribed tuplewise cover lies in each ambient
factor of the corresponding intersection. -/
private lemma tuplewise_cover_member_subset
    {p : ℕ} {U : ι → Opens X}
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X))
    (s : Fin (p + 1) → ι) (k : κ s) (a : Fin (p + 1)) :
    (W s k : Set X) ⊆ U (s a) := by
  -- Rewrite membership in one cover piece through the covering equality of the full intersection.
  intro x hx
  have hx' : x ∈ ⋂ b : Fin (p + 1), (U (s b) : Set X) := by
    rw [hW_cover s]
    exact mem_iUnion.2 ⟨k, hx⟩
  exact mem_iInter.1 hx' a

/-- Helper for Lemma 5.13.5: tuples with the same range cut out the same ambient intersection of
the original cover. -/
private lemma tuplewise_iInter_eq_of_same_range
    {q : ℕ} {U : ι → Opens X}
    {s : Fin (q + 1) → ι} {t : Fin (q + 2) → ι}
    (hRange : Set.range t = Set.range s) :
    (⋂ a : Fin (q + 2), (U (t a) : Set X)) = ⋂ a : Fin (q + 1), (U (s a) : Set X) := by
  ext x
  constructor
  · intro hx
    -- Transfer each lower-order ambient factor across the equality of tuple ranges.
    refine mem_iInter.2 ?_
    intro a
    have hs : s a ∈ Set.range t := by
      rw [hRange]
      exact ⟨a, rfl⟩
    rcases hs with ⟨b, hb⟩
    exact hb ▸ mem_iInter.1 hx b
  · intro hx
    -- The converse direction is identical after swapping the two tuples.
    refine mem_iInter.2 ?_
    intro a
    have ht : t a ∈ Set.range s := by
      rw [← hRange]
      exact ⟨a, rfl⟩
    rcases ht with ⟨b, hb⟩
    exact hb ▸ mem_iInter.1 hx b

/-- Helper for Lemma 5.13.5: every lower-order tuple admits a one-step extension with the same
range by repeating its first coordinate. -/
private lemma same_range_extension_exists
    {q : ℕ} (s : Fin (q + 1) → ι) :
    Nonempty {t : Fin (q + 2) → ι // Set.range t = Set.range s} := by
  refine ⟨⟨Fin.snoc s (s 0), ?_⟩⟩
  -- The repeated last coordinate contributes no new values, and every old value survives.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨a, rfl⟩
    rcases a.eq_castSucc_or_eq_last with ⟨b, rfl⟩ | rfl
    · exact ⟨b, by simp⟩
    · exact ⟨0, by simp⟩
  · intro hx
    rcases hx with ⟨a, rfl⟩
    exact ⟨a.castSucc, by simp⟩

/-- Helper for Lemma 5.13.5: over a finite ambient index type, the covers attached to all
`(q + 2)`-tuples with the same underlying range admit a common finite refinement. -/
private theorem common_refinement_cover_of_same_range
    {q : ℕ} [Fintype ι]
    {U : ι → Opens X}
    {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    (hW_cover : ∀ t : Fin (q + 2) → ι,
      (⋂ a : Fin (q + 2), (U (t a) : Set X)) = ⋃ k, (W t k : Set X))
    (s : Fin (q + 1) → ι) :
    let Ext := {t : Fin (q + 2) → ι // Set.range t = Set.range s}
    let WCommon : (∀ e : Ext, κ e.1) → Opens X :=
      fun m ↦ Finset.univ.inf fun e : Ext ↦ W e.1 (m e)
    (⋂ a : Fin (q + 1), (U (s a) : Set X)) = ⋃ m, (WCommon m : Set X) := by
  classical
  simp only
  ext x
  constructor
  · intro hx
    let picks : ∀ e : {t : Fin (q + 2) → ι // Set.range t = Set.range s}, κ e.1 := fun e ↦ by
      -- Choose, for each same-range extension, one covering piece containing `x`.
      have hx' : x ∈ ⋂ a : Fin (q + 2), (U (e.1 a) : Set X) := by
        rw [tuplewise_iInter_eq_of_same_range e.2]
        exact hx
      rw [hW_cover e.1] at hx'
      exact Classical.choose (mem_iUnion.1 hx')
    refine mem_iUnion.2 ⟨picks, ?_⟩
    change x ∈ ((Finset.univ.inf fun e : {t : Fin (q + 2) → ι // Set.range t = Set.range s} ↦
      W e.1 (picks e) : Opens X) : Set X)
    have hxAll : x ∈ ⋂ e : {t : Fin (q + 2) → ι // Set.range t = Set.range s},
        (W e.1 (picks e) : Set X) := by
      -- The chosen tuple of indices places `x` in every refinement factor simultaneously.
      refine mem_iInter.2 ?_
      intro e
      have hx' : x ∈ ⋂ a : Fin (q + 2), (U (e.1 a) : Set X) := by
        rw [tuplewise_iInter_eq_of_same_range e.2]
        exact hx
      rw [hW_cover e.1] at hx'
      exact Classical.choose_spec (mem_iUnion.1 hx')
    simpa using hxAll
  · intro hx
    rcases mem_iUnion.1 hx with ⟨m, hx⟩
    have hxAll : x ∈ ⋂ e : {t : Fin (q + 2) → ι // Set.range t = Set.range s},
        (W e.1 (m e) : Set X) := by
      -- Membership in the finite lattice inf is exactly simultaneous membership in all factors.
      simpa using hx
    rcases same_range_extension_exists s with ⟨e0⟩
    refine mem_iInter.2 ?_
    intro a
    -- One same-range extension is enough to recover every ambient factor `U (s a)`.
    have hxPiece : x ∈ W e0.1 (m e0) := (mem_iInter.1 hxAll) e0
    have hs : s a ∈ Set.range e0.1 := by
      rw [e0.2]
      exact ⟨a, rfl⟩
    rcases hs with ⟨b, hb⟩
    exact hb ▸ tuplewise_cover_member_subset W hW_cover e0.1 (m e0) b hxPiece

/-- Helper for Lemma 5.13.5: the finite same-range common refinement can be reindexed by a `Fin n`
set of choices, so its parameter space stays in the original universe `w`. -/
private theorem common_refinement_cover_of_same_range_indexed
    {q : ℕ} [Fintype ι]
    {U : ι → Opens X}
    {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    (hW_cover : ∀ t : Fin (q + 2) → ι,
      (⋂ a : Fin (q + 2), (U (t a) : Set X)) = ⋃ k, (W t k : Set X))
    (s : Fin (q + 1) → ι) :
    ∃ n : ℕ, ∃ e : Fin n ≃ {t : Fin (q + 2) → ι // Set.range t = Set.range s},
      (⋂ a : Fin (q + 1), (U (s a) : Set X)) =
        ⋃ m : (∀ a : Fin n, κ ((e a).1)),
          ((Finset.univ.inf fun a : Fin n ↦ W (e a).1 (m a) : Opens X) : Set X) := by
  classical
  let Ext := {t : Fin (q + 2) → ι // Set.range t = Set.range s}
  let n : ℕ := Fintype.card Ext
  let e : Fin n ≃ Ext := (Fintype.equivFin Ext).symm
  refine ⟨n, e, ?_⟩
  ext x
  constructor
  · intro hx
    let picks : ∀ a : Fin n, κ ((e a).1) := fun a ↦ by
      -- Choose one covering piece for each same-range extension in the finite enumeration.
      have hx' : x ∈ ⋂ b : Fin (q + 2), (U ((e a).1 b) : Set X) := by
        rw [tuplewise_iInter_eq_of_same_range (e a).2]
        exact hx
      rw [hW_cover (e a).1] at hx'
      exact Classical.choose (mem_iUnion.1 hx')
    refine mem_iUnion.2 ⟨picks, ?_⟩
    change x ∈ ((Finset.univ.inf fun a : Fin n ↦ W (e a).1 (picks a) : Opens X) : Set X)
    have hxAll : x ∈ ⋂ a : Fin n, (W (e a).1 (picks a) : Set X) := by
      -- The chosen finite tuple of indices places `x` in every common-refinement factor.
      refine mem_iInter.2 ?_
      intro a
      have hx' : x ∈ ⋂ b : Fin (q + 2), (U ((e a).1 b) : Set X) := by
        rw [tuplewise_iInter_eq_of_same_range (e a).2]
        exact hx
      rw [hW_cover (e a).1] at hx'
      exact Classical.choose_spec (mem_iUnion.1 hx')
    simpa using hxAll
  · intro hx
    rcases mem_iUnion.1 hx with ⟨m, hx⟩
    have hxAll : x ∈ ⋂ a : Fin n, (W (e a).1 (m a) : Set X) := by
      -- Membership in the finite inf means membership in every enumerated factor.
      simpa using hx
    rcases same_range_extension_exists s with ⟨e0⟩
    refine mem_iInter.2 ?_
    intro a
    -- One enumerated same-range extension is enough to recover each ambient factor `U (s a)`.
    have hxPiece :
        x ∈ W ((e (e.symm e0)).1) (m (e.symm e0)) := (mem_iInter.1 hxAll) (e.symm e0)
    have hs : s a ∈ Set.range e0.1 := by
      rw [e0.2]
      exact ⟨a, rfl⟩
    rcases hs with ⟨b, hb⟩
    have hAmbient : x ∈ U (((e (e.symm e0)).1) b) :=
      tuplewise_cover_member_subset W hW_cover ((e (e.symm e0)).1) (m (e.symm e0)) b hxPiece
    have hAmbient' : x ∈ U (e0.1 b) := by
      simpa using hAmbient
    exact hb ▸ hAmbient'

/-- Helper for Lemma 5.13.5: a noninjective tuple can be shortened by deleting one coordinate
while keeping the same range. -/
private lemma repeated_tuple_range_reduction_succAbove
    {q : ℕ} {σ : Fin (q + 2) → ι} (hσ : ¬ Function.Injective σ) :
    ∃ j : Fin (q + 2), Set.range (fun a : Fin (q + 1) ↦ σ (j.succAbove a)) = Set.range σ := by
  have hσ' : ¬ ∀ a b, σ a = σ b → a = b := by
    simpa [Function.Injective] using hσ
  push Not at hσ'
  rcases hσ' with ⟨i, j, hijVal, hij⟩
  refine ⟨j, ?_⟩
  -- Deleting one coordinate preserves the range because its value reappears at the repeated one.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨a, rfl⟩
    exact ⟨j.succAbove a, rfl⟩
  · intro hx
    rcases hx with ⟨b, rfl⟩
    by_cases hb : b = j
    · subst hb
      rcases Fin.exists_succAbove_eq hij with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [ha] using hijVal
    · rcases Fin.exists_succAbove_eq hb with ⟨a, ha⟩
      exact ⟨a, by simp [ha]⟩

/-- Helper for Lemma 5.13.5: deleting one repeated coordinate from a noninjective tuple preserves
its range. -/
private lemma repeated_tuple_range_reduction
    {q : ℕ} {σ : Fin (q + 2) → ι} (hσ : ¬ Function.Injective σ) :
    ∃ s : Fin (q + 1) → ι, Set.range s = Set.range σ := by
  rcases repeated_tuple_range_reduction_succAbove hσ with ⟨j, hj⟩
  -- Forget the deleted coordinate once its range-preservation property is established.
  exact ⟨fun a ↦ σ (j.succAbove a), hj⟩

/-- Helper for Lemma 5.13.5: deleting one coordinate from a tuple only enlarges the corresponding
intersection of shrinking opens. -/
private lemma tuplewise_iInter_subset_succAbove
    {q : ℕ} {J : Type z} {V : J → Opens X}
    (jTuple : Fin (q + 2) → J) (j : Fin (q + 2)) :
    (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) ⊆
      ⋂ a : Fin (q + 1), (V (jTuple (j.succAbove a)) : Set X) := by
  -- Every factor in the shortened tuple already appears among the original factors.
  intro x hx
  refine mem_iInter.2 ?_
  intro a
  exact (mem_iInter.1 hx) (j.succAbove a)

/-- Helper for Lemma 5.13.5: once a same-range extension is selected from the finite enumeration,
one component of the finite common refinement already lands in the corresponding original cover
piece. -/
private lemma enumerated_common_refinement_factor_transport
    {q : ℕ} {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    {nCommon : (Fin (q + 1) → ι) → ℕ}
    (enumCommon :
      ∀ s : Fin (q + 1) → ι,
        Fin (nCommon s) ≃ {t : Fin (q + 2) → ι // Set.range t = Set.range s})
    {s : Fin (q + 1) → ι} {σ : Fin (q + 2) → ι}
    (hRange : Set.range σ = Set.range s)
    (m : ∀ a : Fin (nCommon s), κ ((enumCommon s a).1)) :
    ∃ k : κ σ,
      ((Finset.univ.inf fun a : Fin (nCommon s) ↦ W (enumCommon s a).1 (m a) : Opens X) :
        Set X) ⊆ W σ k := by
  let eσ : {t : Fin (q + 2) → ι // Set.range t = Set.range s} := ⟨σ, hRange⟩
  let aσ : Fin (nCommon s) := (enumCommon s).symm eσ
  have hTarget : σ = (enumCommon s aσ).1 := by
    -- Rewrite the target tuple through the chosen enumeration inverse.
    symm
    exact congrArg Subtype.val ((enumCommon s).apply_symm_apply eσ)
  rw [hTarget]
  refine ⟨m aσ, ?_⟩
  -- One factor of the finite lattice inf is obtained by monotonicity.
  intro x hx
  exact (show (Finset.univ.inf fun a : Fin (nCommon s) ↦ W (enumCommon s a).1 (m a) : Opens X) ≤
      W (enumCommon s aσ).1 (m aσ) from Finset.inf_le (by simp)) hx

/-- A tuplewise shrinking refinement of an open cover consists of a shrinking whose realized
`(p + 1)`-fold intersections are either empty or contained in one member of the prescribed
tuplewise cover of the corresponding intersection of the original cover. -/
class IsTuplewiseShrinkingRefinement
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    {J : Type z} (V : J → Opens X) (α : J → ι) : Prop where
  isOpenCover : IsOpenCover V
  closure_subset (j : J) : closure (V j : Set X) ⊆ U (α j)
  tuplewise_subordinate (jTuple : Fin (p + 1) → J) :
    (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) = ∅ ∨
      ∃ k : κ (fun a ↦ α (jTuple a)),
        (⋂ a : Fin (p + 1), (V (jTuple a) : Set X)) ⊆ W (fun a ↦ α (jTuple a)) k

/-- Helper for Lemma 5.13.5: the induction hypothesis on the lower-order common refinement already
controls every tuple whose ambient labels have a repetition. -/
private lemma tuplewise_subordinate_of_repeated_alpha
    {q : ℕ} {U : ι → Opens X} (hU : IsOpenCover U)
    {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    {nCommon : (Fin (q + 1) → ι) → ℕ}
    (enumCommon :
      ∀ s : Fin (q + 1) → ι,
        Fin (nCommon s) ≃ {t : Fin (q + 2) → ι // Set.range t = Set.range s})
    {J : Type z} {V : J → Opens X} {α : J → ι}
    (hRefCommon :
      @IsTuplewiseShrinkingRefinement X _ ι U hU q
        (fun s : Fin (q + 1) → ι ↦ ∀ a : Fin (nCommon s), κ ((enumCommon s a).1))
        (fun s m ↦ Finset.univ.inf fun a : Fin (nCommon s) ↦ W (enumCommon s a).1 (m a))
        J V α)
    (jTuple : Fin (q + 2) → J)
    (hNoninj : ¬ Function.Injective (fun a ↦ α (jTuple a))) :
    (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) = ∅ ∨
      ∃ k : κ (fun a ↦ α (jTuple a)),
        (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) ⊆ W (fun a ↦ α (jTuple a)) k := by
  classical
  rcases repeated_tuple_range_reduction_succAbove
      (σ := fun a ↦ α (jTuple a)) hNoninj with ⟨j, hjRange⟩
  let s : Fin (q + 1) → ι := fun a ↦ α (jTuple (j.succAbove a))
  have hShort :
      (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) ⊆
        ⋂ a : Fin (q + 1), (V (jTuple (j.succAbove a)) : Set X) :=
    tuplewise_iInter_subset_succAbove jTuple j
  -- Apply the lower-order refinement to the tuple with one repeated coordinate deleted.
  rcases hRefCommon.tuplewise_subordinate (fun a ↦ jTuple (j.succAbove a)) with hEmpty | ⟨m, hm⟩
  · left
    -- The full intersection is contained in an empty shortened intersection, hence empty.
    apply Set.Subset.antisymm
    · intro x hx
      have hxShort : x ∈ ⋂ a : Fin (q + 1), (V (jTuple (j.succAbove a)) : Set X) := hShort hx
      rwa [hEmpty] at hxShort
    · simp
  · right
    let σ : Fin (q + 2) → ι := fun a ↦ α (jTuple a)
    rcases enumerated_common_refinement_factor_transport
        (W := W) enumCommon (s := s) (σ := σ) hjRange.symm m with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    -- First place the full intersection inside the finite common refinement, then project to the
    -- enumerated factor corresponding to the original tuple.
    intro x hx
    exact hk (hm (hShort hx))

/-- Helper for Lemma 5.13.5: tuplewise witnesses transport across a factor map as soon as every
new open is contained in the corresponding old open. -/
private lemma factor_map_preserves_tuplewise_subordination
    {q : ℕ} {J : Type*} {J' : Type*}
    {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    {V : J → Opens X} {V' : J' → Opens X}
    {α : J → ι}
    (β : J' → J)
    (hSubset : ∀ j', (V' j' : Set X) ⊆ V (β j'))
    (jTuple : Fin (q + 2) → J')
    (hOld :
      (⋂ a : Fin (q + 2), (V (β (jTuple a)) : Set X)) = ∅ ∨
        ∃ k : κ (fun a ↦ α (β (jTuple a))),
          (⋂ a : Fin (q + 2), (V (β (jTuple a)) : Set X)) ⊆
            W (fun a ↦ α (β (jTuple a))) k) :
    (⋂ a : Fin (q + 2), (V' (jTuple a) : Set X)) = ∅ ∨
      ∃ k : κ (fun a ↦ α (β (jTuple a))),
        (⋂ a : Fin (q + 2), (V' (jTuple a) : Set X)) ⊆
          W (fun a ↦ α (β (jTuple a))) k := by
  have hInterSubset :
      (⋂ a : Fin (q + 2), (V' (jTuple a) : Set X)) ⊆
        ⋂ a : Fin (q + 2), (V (β (jTuple a)) : Set X) := by
    -- Every new tuple intersection sits inside the corresponding old tuple intersection.
    intro x hx
    refine mem_iInter.2 ?_
    intro a
    exact hSubset (jTuple a) ((mem_iInter.1 hx) a)
  rcases hOld with hEmpty | ⟨k, hk⟩
  · left
    -- If the old tuple intersection is empty, the new smaller intersection is empty as well.
    apply Set.Subset.antisymm
    · intro x hx
      have hxOld : x ∈ ⋂ a : Fin (q + 2), (V (β (jTuple a)) : Set X) := hInterSubset hx
      simpa [hEmpty] using hxOld
    · simp
  · right
    -- A witness for the old tuple remains a witness after restricting each factor.
    refine ⟨k, ?_⟩
    intro x hx
    exact hk (hInterSubset hx)

/-- Helper for Lemma 5.13.5: finitely many open covers of the same open set admit a simultaneous
common refinement obtained by intersecting one chosen member from each cover. -/
private theorem common_refinement_of_finite_open_covers
    {T : Type*} [Fintype T]
    {η : T → Type*} [∀ t : T, Nonempty (η t)]
    (Base : Opens X)
    (A : ∀ t : T, η t → Opens X)
    (hCover : ∀ t : T, (Base : Set X) = ⋃ e, (A t e : Set X)) :
    (Base : Set X) =
      ⋃ m : (∀ t : T, η t),
        ((Base ⊓ Finset.univ.inf fun t : T ↦ A t (m t) : Opens X) : Set X) := by
  classical
  ext x
  constructor
  · intro hxBase
    let picks : ∀ t : T, η t := fun t ↦ by
      -- Choose one member from each finite cover containing the current point.
      have hxCover : x ∈ ⋃ e, (A t e : Set X) := by
        simpa [hCover t] using hxBase
      exact Classical.choose (mem_iUnion.1 hxCover)
    refine mem_iUnion.2 ⟨picks, ?_⟩
    change x ∈ (Base : Set X) ∩
      (((Finset.univ.inf fun t : T ↦ A t (picks t) : Opens X) : Opens X) : Set X)
    refine ⟨hxBase, ?_⟩
    have hxAll : x ∈ ⋂ t : T, (A t (picks t) : Set X) := by
      -- The chosen tuple of opens places `x` in every factor of the common refinement.
      refine mem_iInter.2 ?_
      intro t
      have hxCover : x ∈ ⋃ e, (A t e : Set X) := by
        simpa [hCover t] using hxBase
      exact Classical.choose_spec (mem_iUnion.1 hxCover)
    rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simpa using hxAll
  · intro hx
    rcases mem_iUnion.1 hx with ⟨m, hx⟩
    -- Each common-refinement piece remains inside the original base open.
    simpa using hx.1

/-- Helper for Lemma 5.13.5: after a one-step split at coordinate `0`, an injective source
signature forces any newly created summand to occur only at that split coordinate. -/
private lemma injective_signature_sum_inr_eq_zero
    {q : ℕ} {J : Type*} {K : Type*}
    {α : J → ι} {σ : Fin (q + 2) → ι}
    (hσ : Function.Injective σ)
    (τ : Fin (q + 2) → J)
    (hτ : (fun a ↦ α (τ a)) = σ)
    (jTuple : Fin (q + 2) → J ⊕ K)
    (hLabel : (fun a ↦ α (Sum.elim id (fun _ : K ↦ τ 0) (jTuple a))) = σ)
    {a : Fin (q + 2)} {k : K}
    (ha : jTuple a = Sum.inr k) :
    a = 0 := by
  -- Compare the source label at the new summand with the original split coordinate.
  have hτ0 : α (τ 0) = σ 0 := by
    simpa using congrArg (fun f ↦ f 0) hτ
  have haσ : α (τ 0) = σ a := by
    simpa [ha] using congrArg (fun f ↦ f a) hLabel
  -- Injectivity of the source signature pins the new summand to coordinate `0`.
  exact hσ (haσ.symm.trans hτ0)

/-- Helper for Lemma 5.13.5: once a threaded refinement sits inside the original shrinking family,
the old repeated-label branch and new injective-lift branch already give the full tuplewise
refinement. -/
private theorem isTuplewiseShrinkingRefinement_of_factor_map_and_injective_control
    {q : ℕ} [Fintype ι]
    {U : ι → Opens X} (hU : IsOpenCover U)
    {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    {J : Type*} (V : J → Opens X) (α : J → ι)
    {J' : Type*} (V' : J' → Opens X) (β : J' → J)
    (hCover : IsOpenCover V')
    (hClosure : ∀ j' : J', closure (V' j' : Set X) ⊆ U (α (β j')))
    (hSubset : ∀ j', (V' j' : Set X) ⊆ V (β j'))
    (hRepeated :
      ∀ jTuple : Fin (q + 2) → J,
        ¬ Function.Injective (fun a ↦ α (jTuple a)) →
          (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) = ∅ ∨
            ∃ k : κ (fun a ↦ α (jTuple a)),
              (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) ⊆
                W (fun a ↦ α (jTuple a)) k)
    (hInjective :
      ∀ jTuple₀ : Fin (q + 2) → J,
        Function.Injective (fun a ↦ α (jTuple₀ a)) →
          ∀ jTuple' : Fin (q + 2) → J',
            (fun a ↦ β (jTuple' a)) = jTuple₀ →
              (⋂ a : Fin (q + 2), (V' (jTuple' a) : Set X)) = ∅ ∨
                ∃ k : κ (fun a ↦ α (jTuple₀ a)),
                  (⋂ a : Fin (q + 2), (V' (jTuple' a) : Set X)) ⊆
                    W (fun a ↦ α (jTuple₀ a)) k) :
    IsTuplewiseShrinkingRefinement hU (q + 1) W V' (fun j' ↦ α (β j')) := by
  refine ⟨hCover, hClosure, ?_⟩
  intro jTuple'
  by_cases hInj : Function.Injective (fun a ↦ α (β (jTuple' a)))
  · -- The injective case is discharged by the threaded control on lifts of original tuples.
    simpa using hInjective (fun a ↦ β (jTuple' a)) hInj jTuple' rfl
  · -- Otherwise the tuple factors through an old repeated-label tuple, so the old witness
    -- transports across the factor map.
    exact factor_map_preserves_tuplewise_subordination W β hSubset jTuple'
      (hRepeated (fun a ↦ β (jTuple' a)) hInj)

/-- Helper for Lemma 5.13.5: once the repeated-label tuples are already controlled, the remaining
injective signatures should be removed by the finite bad-tuple descent from the source proof. -/
private theorem injective_signature_descent
    [Fintype ι]
    {U : ι → Opens X} (hU : IsOpenCover U)
    {q : ℕ}
    {κ : (Fin (q + 2) → ι) → Type w}
    (W : ∀ t : Fin (q + 2) → ι, κ t → Opens X)
    (hW_cover : ∀ t : Fin (q + 2) → ι,
      (⋂ a : Fin (q + 2), (U (t a) : Set X)) = ⋃ k, (W t k : Set X))
    {J : Type z} [Fintype J]
    (V : J → Opens X) (α : J → ι)
    (hCover : IsOpenCover V)
    (hClosure : ∀ j : J, closure (V j : Set X) ⊆ U (α j))
    (hRepeated :
      ∀ jTuple : Fin (q + 2) → J,
        ¬ Function.Injective (fun a ↦ α (jTuple a)) →
          (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) = ∅ ∨
            ∃ k : κ (fun a ↦ α (jTuple a)),
              (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) ⊆ W (fun a ↦ α (jTuple a)) k) :
    ∃ (J' : Type (max u v w)) (_ : Fintype J') (V' : J' → Opens X) (α' : J' → ι),
      IsTuplewiseShrinkingRefinement hU (q + 1) W V' α' := by
  classical
  suffices hAux :
    ∃ (J' : Type (max u v w)) (_ : Fintype J') (V' : J' → Opens X) (β : J' → J),
      IsOpenCover V' ∧
        (∀ j' : J', closure (V' j' : Set X) ⊆ U (α (β j'))) ∧
        (∀ j' : J', (V' j' : Set X) ⊆ V (β j')) ∧
        (∀ jTuple₀ : Fin (q + 2) → J,
          Function.Injective (fun a ↦ α (jTuple₀ a)) →
            ∀ jTuple' : Fin (q + 2) → J',
              (fun a ↦ β (jTuple' a)) = jTuple₀ →
                (⋂ a : Fin (q + 2), (V' (jTuple' a) : Set X)) = ∅ ∨
                  ∃ k : κ (fun a ↦ α (jTuple₀ a)),
                    (⋂ a : Fin (q + 2), (V' (jTuple' a) : Set X)) ⊆
                      W (fun a ↦ α (jTuple₀ a)) k) by
    rcases hAux with ⟨J', hJ', V', β, hCover', hClosure', hSubset', hInjective'⟩
    refine ⟨J', hJ', V', fun j' ↦ α (β j'), ?_⟩
    -- Combine the old repeated-label branch with threaded control of injective lifts.
    exact isTuplewiseShrinkingRefinement_of_factor_map_and_injective_control
      hU W V α V' β hCover' hClosure' hSubset' hRepeated hInjective'
  -- Route correction: the repeated-label branch is already solved. For injective source tuples we
  -- simultaneously split the `0`-coordinate open into a remainder piece and finitely many
  -- `W σ k`-pieces, then take the finite common refinement of all these split covers.
  let InjTuple : Type z :=
    {jTuple : Fin (q + 2) → J // Function.Injective (fun a ↦ α (jTuple a))}
  let σ : InjTuple → (Fin (q + 2) → ι) := fun s a ↦ α (s.1 a)
  let tailClosed : InjTuple → Set X := fun s ↦
    ⋂ a : Fin (q + 1), closure (V (s.1 a.succ) : Set X)
  have hTailClosed : ∀ s : InjTuple, IsClosed (tailClosed s) := by
    -- The tail intersection is closed because every factor is a closure.
    intro s
    exact isClosed_iInter fun a ↦ isClosed_closure
  let compactIntersection : InjTuple → Set X := fun s ↦
    closure (V (s.1 0) : Set X) ∩ tailClosed s
  have hCompactIntersection : ∀ s : InjTuple, IsCompact (compactIntersection s) := by
    -- Compactness comes from the compact first closure intersected with the closed tail.
    intro s
    have hCompactClosure : IsCompact (closure (V (s.1 0) : Set X)) := by
      refine (isCompact_univ : IsCompact (Set.univ : Set X)).of_isClosed_subset isClosed_closure ?_
      simp
    exact hCompactClosure.inter_right (hTailClosed s)
  have hCompactIntersection_subset :
      ∀ s : InjTuple,
        compactIntersection s ⊆ ⋃ k : κ (σ s), (W (σ s) k : Set X) := by
    intro s x hx
    have hxAmbient : x ∈ ⋂ a : Fin (q + 2), (U (σ s a) : Set X) := by
      -- Every point in the compact closure intersection lies in the corresponding ambient
      -- `(q + 2)`-fold intersection by the shrinking condition on each coordinate.
      refine mem_iInter.2 ?_
      intro a
      cases a using Fin.cases with
      | zero =>
          exact hClosure (s.1 0) hx.1
      | succ a =>
          exact hClosure (s.1 a.succ) ((mem_iInter.1 hx.2) a)
    rw [hW_cover (σ s)] at hxAmbient
    exact hxAmbient
  have hK_exists :
      ∀ s : InjTuple, ∃ K : Finset (κ (σ s)),
        compactIntersection s ⊆ ⋃ k : ↥K, (W (σ s) k.1 : Set X) := by
    intro s
    rcases (hCompactIntersection s).elim_finite_subcover
        (fun k : κ (σ s) ↦ (W (σ s) k : Set X))
        (fun k ↦ (W (σ s) k).isOpen)
        (hCompactIntersection_subset s) with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro x hx
    rcases mem_iUnion₂.1 (hK hx) with ⟨k, hk, hxk⟩
    exact mem_iUnion.2 ⟨⟨k, hk⟩, hxk⟩
  choose K hK_cover using hK_exists
  have hBaseOpen : ∀ j : J, IsOpen (V j : Set X) := by
    intro j
    simpa using (V j).isOpen
  have hRemainderOpen : ∀ j : J, ∀ s : InjTuple, IsOpen ((V j : Set X) \ tailClosed s) := by
    intro j s
    simpa [Set.diff_eq, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
      (hBaseOpen j).inter (hTailClosed s).isOpen_compl
  let splitOpen :
      J → (s : InjTuple) → Option ↥(K s) → Opens X := fun j s o ↦
        if h : s.1 0 = j then
          match o with
          | none =>
              ⟨(V j : Set X) \ tailClosed s,
                hRemainderOpen j s⟩
          | some k =>
              V j ⊓ W (σ s) k.1
        else
          V j
  have hSplitCover :
      ∀ s : InjTuple,
        (V (s.1 0) : Set X) = ⋃ o : Option ↥(K s), (splitOpen (s.1 0) s o : Set X) := by
    intro s
    ext x
    constructor
    · intro hxV
      by_cases hxTail : x ∈ tailClosed s
      · have hxCompact : x ∈ compactIntersection s := ⟨subset_closure hxV, hxTail⟩
        have hxK : x ∈ ⋃ k : ↥(K s), (W (σ s) k.1 : Set X) := hK_cover s hxCompact
        rcases mem_iUnion.1 hxK with ⟨k, hxk⟩
        refine mem_iUnion.2 ⟨some k, ?_⟩
        simpa [splitOpen] using show x ∈ (V (s.1 0) : Set X) ∩ (W (σ s) k.1 : Set X) from
          ⟨hxV, hxk⟩
      · refine mem_iUnion.2 ⟨none, ?_⟩
        simpa [splitOpen, hxTail] using show x ∈ (V (s.1 0) : Set X) \ tailClosed s from
          ⟨hxV, hxTail⟩
    · intro hx
      rcases mem_iUnion.1 hx with ⟨o, ho⟩
      cases o with
      | none =>
          have ho' : x ∈ (V (s.1 0) : Set X) ∧ x ∉ tailClosed s := by
            simpa [splitOpen] using ho
          exact ho'.1
      | some k =>
          have ho' : x ∈ (V (s.1 0) : Set X) ∧ x ∈ W (σ s) k.1 := by
            simpa [splitOpen] using ho
          exact ho'.1
  have hSingleCover :
      ∀ j : J, ∀ s : InjTuple, (V j : Set X) = ⋃ o : Option ↥(K s), (splitOpen j s o : Set X) := by
    intro j s
    by_cases h : s.1 0 = j
    · subst j
      simpa using hSplitCover s
    · ext x
      simp [splitOpen, h]
  let AllChoice := ∀ s : InjTuple, Option ↥(K s)
  let Jtmp := J × AllChoice
  let Vtmp : Jtmp → Opens X := fun jm ↦
    V jm.1 ⊓ Finset.univ.inf fun s : InjTuple ↦ splitOpen jm.1 s (jm.2 s)
  have hVtmp_common :
      ∀ j : J,
        (V j : Set X) = ⋃ m : AllChoice, (Vtmp (j, m) : Set X) := by
    intro j
    simpa [Vtmp] using
      common_refinement_of_finite_open_covers (Base := V j) (A := splitOpen j) (hCover := hSingleCover j)
  have hVtmp_cover_set : (⋃ jm : Jtmp, (Vtmp jm : Set X)) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hCover.exists_mem x with ⟨j, hxj⟩
      have hxj' : x ∈ ⋃ m : AllChoice, (Vtmp (j, m) : Set X) := by
        rw [← hVtmp_common j]
        exact hxj
      rcases mem_iUnion.1 hxj' with ⟨m, hxm⟩
      exact mem_iUnion.2 ⟨(j, m), hxm⟩
  have hVtmp_cover : IsOpenCover Vtmp := by
    exact IsOpenCover.of_sets (fun jm ↦ (Vtmp jm).isOpen) hVtmp_cover_set
  have hVtmp_subset : ∀ jm : Jtmp, (Vtmp jm : Set X) ⊆ V jm.1 := by
    intro jm x hx
    simpa [Vtmp] using hx.1
  have hVtmp_split :
      ∀ jm : Jtmp, ∀ s : InjTuple, (Vtmp jm : Set X) ⊆ splitOpen jm.1 s (jm.2 s) := by
    intro jm s x hx
    have hxInf :
        x ∈ (((Finset.univ.inf fun t : InjTuple ↦ splitOpen jm.1 t (jm.2 t) : Opens X) :
          Opens X) : Set X) := by
      simpa [Vtmp] using hx.2
    exact
      (show
          (Finset.univ.inf fun t : InjTuple ↦ splitOpen jm.1 t (jm.2 t) : Opens X) ≤
            splitOpen jm.1 s (jm.2 s) from
          Finset.inf_le (by simp)) hxInf
  let J' : Type (max u v w) := ULift.{max u v w} (Fin (Fintype.card Jtmp))
  let decode : J' → Jtmp := fun j' ↦ (Fintype.equivFin Jtmp).symm j'.down
  let encode : Jtmp → J' := fun jm ↦ ⟨Fintype.equivFin Jtmp jm⟩
  let V' : J' → Opens X := fun j' ↦ Vtmp (decode j')
  let β : J' → J := fun j' ↦ (decode j').1
  have hV'_cover_set : (⋃ j' : J', (V' j' : Set X)) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      have hxTmp : x ∈ ⋃ jm : Jtmp, (Vtmp jm : Set X) := by
        rw [hVtmp_cover_set]
        simp
      rcases mem_iUnion.1 hxTmp with ⟨jm, hxm⟩
      exact mem_iUnion.2 ⟨encode jm, by simpa [V', decode, encode] using hxm⟩
  have hV'_cover : IsOpenCover V' := by
    exact IsOpenCover.of_sets (fun j' ↦ (V' j').isOpen) hV'_cover_set
  have hV'_closure :
      ∀ j' : J', closure (V' j' : Set X) ⊆ U (α (β j')) := by
    intro j'
    exact (closure_mono (by simpa [V', β, decode] using hVtmp_subset (decode j'))).trans
      (hClosure ((decode j').1))
  have hV'_subset : ∀ j' : J', (V' j' : Set X) ⊆ V (β j') := by
    intro j'
    simpa [V', β, decode] using hVtmp_subset (decode j')
  have hInjective' :
      ∀ jTuple₀ : Fin (q + 2) → J,
        Function.Injective (fun a ↦ α (jTuple₀ a)) →
          ∀ jTuple' : Fin (q + 2) → J',
            (fun a ↦ β (jTuple' a)) = jTuple₀ →
              (⋂ a : Fin (q + 2), (V' (jTuple' a) : Set X)) = ∅ ∨
                ∃ k : κ (fun a ↦ α (jTuple₀ a)),
                  (⋂ a : Fin (q + 2), (V' (jTuple' a) : Set X)) ⊆
                    W (fun a ↦ α (jTuple₀ a)) k := by
    intro jTuple₀ hInj jTuple' hβ
    let s0 : InjTuple := ⟨jTuple₀, hInj⟩
    have hβ_eq : ∀ a : Fin (q + 2), (decode (jTuple' a)).1 = jTuple₀ a := by
      intro a
      simpa [β] using congrArg (fun f ↦ f a) hβ
    cases hChoice : (decode (jTuple' 0)).2 s0 with
    | none =>
        left
        apply Set.Subset.antisymm
        · intro x hx
          have hx0' : x ∈ (Vtmp (decode (jTuple' 0)) : Set X) := by
            simpa [V'] using (mem_iInter.1 hx) 0
          have hxSplit0 : x ∈ splitOpen (jTuple₀ 0) s0 none := by
            simpa [hβ_eq 0, hChoice] using hVtmp_split (decode (jTuple' 0)) s0 hx0'
          have hs0 : s0.1 0 = jTuple₀ 0 := rfl
          have hxR : x ∈ (V (jTuple₀ 0) : Set X) \ tailClosed s0 := by
            simpa [splitOpen, hs0] using hxSplit0
          have hxTail : x ∈ tailClosed s0 := by
            refine mem_iInter.2 ?_
            intro a
            have hxSucc : x ∈ (V' (jTuple' a.succ) : Set X) := (mem_iInter.1 hx) a.succ
            have hxOld : x ∈ V ((decode (jTuple' a.succ)).1) := by
              simpa [β] using hV'_subset (jTuple' a.succ) hxSucc
            have hxOld' : x ∈ V (jTuple₀ a.succ) := by
              rw [hβ_eq a.succ] at hxOld
              exact hxOld
            exact subset_closure hxOld'
          exact (hxR.2 hxTail).elim
        · simp
    | some k =>
        right
        refine ⟨k.1, ?_⟩
        intro x hx
        have hx0' : x ∈ (Vtmp (decode (jTuple' 0)) : Set X) := by
          simpa [V'] using (mem_iInter.1 hx) 0
        have hxSplitk : x ∈ splitOpen (jTuple₀ 0) s0 (some k) := by
          simpa [hβ_eq 0, hChoice] using hVtmp_split (decode (jTuple' 0)) s0 hx0'
        have hs0 : s0.1 0 = jTuple₀ 0 := rfl
        have hxPiece :
            x ∈ (V (jTuple₀ 0) : Set X) ∩ (W (fun a ↦ α (jTuple₀ a)) k.1 : Set X) := by
          simpa [splitOpen, hs0, σ] using hxSplitk
        exact hxPiece.2
  exact ⟨J', inferInstance, V', β, hV'_cover, hV'_closure, hV'_subset, hInjective'⟩

/-- Helper for Lemma 5.13.5: in the base case `p = 0`, shrinking the sigma-indexed cover by the
individual prescribed opens already gives the required tuplewise refinement. -/
private theorem exists_tuplewise_shrinking_refinement_zero
    {U : ι → Opens X} (hU : IsOpenCover U)
    {κ : (Fin 1 → ι) → Type w}
    (W : ∀ s : Fin 1 → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin 1 → ι,
      (⋂ a : Fin 1, (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement hU 0 W V α := by
  classical
  let J0 : Type (max v w) := Σ i : ι, κ (fun _ : Fin 1 ↦ i)
  let W0 : J0 → Opens X := fun j ↦ W (fun _ : Fin 1 ↦ j.1) j.2
  have hW0_cover_set : (⋃ j : J0, (W0 j : Set X)) = Set.univ := by
    -- Each point lies in some ambient `U i`, hence in one member of the prescribed cover over `U i`.
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hU.exists_mem x with ⟨i, hxi⟩
      have hxi' : x ∈ ⋃ k, (W (fun _ : Fin 1 ↦ i) k : Set X) := by
        rw [← hW_cover (fun _ : Fin 1 ↦ i)]
        simpa using hxi
      rcases mem_iUnion.1 hxi' with ⟨k, hxk⟩
      exact mem_iUnion.2 ⟨⟨i, k⟩, hxk⟩
  have hW0_cover : IsOpenCover W0 := by
    simpa [W0] using IsOpenCover.of_sets (fun j ↦ (W0 j).isOpen) hW0_cover_set
  rcases hW0_cover.exists_shrinking with ⟨V, hV_cover, hV_closure⟩
  let V' : ULift.{u} J0 → Opens X := fun j ↦ V j.down
  let α' : ULift.{u} J0 → ι := fun j ↦ j.down.1
  have hV'_cover_set : (⋃ j : ULift.{u} J0, (V' j : Set X)) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hV_cover.exists_mem x with ⟨j, hxj⟩
      exact mem_iUnion.2 ⟨⟨j⟩, by simpa [V'] using hxj⟩
  have hV'_cover : IsOpenCover V' := by
    simpa [V'] using IsOpenCover.of_sets (fun j ↦ (V' j).isOpen) hV'_cover_set
  refine ⟨ULift.{u} J0, V', α', ?_⟩
  refine ⟨hV'_cover, ?_, ?_⟩
  · -- The shrinking closures land in the selected prescribed piece, hence in the ambient `U i`.
    intro j
    exact (hV_closure j.down).trans <|
      tuplewise_cover_member_subset W hW_cover (fun _ : Fin 1 ↦ j.down.1) j.down.2 0
  · -- For a `1`-tuple, the intersection is just the chosen open itself.
    intro jTuple
    have hα :
        (fun a : Fin 1 ↦ α' (jTuple a)) = fun _ : Fin 1 ↦ (jTuple 0).down.1 := by
      funext a
      fin_cases a
      rfl
    -- Rewrite the dependent target tuple to the unique `Fin 1` coordinate before choosing `k`.
    rw [hα]
    refine Or.inr ?_
    refine ⟨(jTuple 0).down.2, ?_⟩
    intro x hx
    have hxV : x ∈ (V ((jTuple 0).down) : Set X) := by
      simpa [V'] using (mem_iInter.1 hx) 0
    have hxClosure : x ∈ closure (V ((jTuple 0).down) : Set X) := subset_closure hxV
    have hxW : x ∈ W (fun _ : Fin 1 ↦ (jTuple 0).down.1) (jTuple 0).down.2 :=
      hV_closure ((jTuple 0).down) hxClosure
    simpa [α'] using hxW

/-- Helper for Lemma 5.13.5: when the ambient index type is finite and `p = 0`, a finite
subcover of the base-case shrinking gives a finite output index type. -/
private theorem exists_tuplewise_shrinking_refinement_zero_finite
    [Fintype ι]
    {U : ι → Opens X} (hU : IsOpenCover U)
    {κ : (Fin 1 → ι) → Type w}
    (W : ∀ s : Fin 1 → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin 1 → ι,
      (⋂ a : Fin 1, (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (_ : Fintype J), ∃ (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement hU 0 W V α := by
  classical
  rcases exists_tuplewise_shrinking_refinement_zero hU W hW_cover with ⟨J0, V0, α0, hRef0⟩
  rcases (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun j : J0 ↦ (V0 j : Set X))
      (fun j ↦ (V0 j).isOpen)
      hRef0.isOpenCover.iSup_set_eq_univ.ge with ⟨t, ht⟩
  let J : Type (max u v w) := ↥t
  let V : J → Opens X := fun j ↦ V0 j.1
  let α : J → ι := fun j ↦ α0 j.1
  have hV_cover_set : (⋃ j : J, (V j : Set X)) = Set.univ := by
    -- Restrict the original shrinking to a finite subcover of `X`.
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases mem_iUnion₂.1 (ht (by simp)) with ⟨j, hj, hxj⟩
      exact mem_iUnion.2 ⟨⟨j, hj⟩, by simpa [V] using hxj⟩
  have hV_cover : IsOpenCover V := by
    simpa [V] using IsOpenCover.of_sets (fun j ↦ (V j).isOpen) hV_cover_set
  refine ⟨J, inferInstance, V, α, ?_⟩
  refine ⟨hV_cover, ?_, ?_⟩
  · -- Closure control is inherited from the unrestricted base-case shrinking.
    intro j
    simpa [V, α] using hRef0.closure_subset j.1
  · -- The tuplewise containment condition is unchanged after reindexing by the finite subtype.
    intro jTuple
    simpa [V, α] using hRef0.tuplewise_subordinate (fun a ↦ (jTuple a).1)

/-- Helper for Lemma 5.13.5: the source proof's induction runs on finite ambient index types and
produces a finite shrinking index type as well. -/
private theorem exists_tuplewise_shrinking_refinement_finite
    [Fintype ι]
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (_ : Fintype J), ∃ (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement hU p W V α := by
  classical
  induction p with
  | zero =>
      -- The finite base case is the unrestricted base case followed by a finite subcover cutdown.
      simpa using exists_tuplewise_shrinking_refinement_zero_finite hU W hW_cover
  | succ q ih =>
      let nCommon : (Fin (q + 1) → ι) → ℕ := fun s ↦
        Classical.choose (common_refinement_cover_of_same_range_indexed (q := q) W hW_cover s)
      let enumCommon :
          ∀ s : Fin (q + 1) → ι,
            Fin (nCommon s) ≃ {t : Fin (q + 2) → ι // Set.range t = Set.range s} := fun s ↦
          Classical.choose
            (Classical.choose_spec (common_refinement_cover_of_same_range_indexed
              (q := q) W hW_cover s))
      let κCommon : (Fin (q + 1) → ι) → Type w := fun s ↦
        ∀ a : Fin (nCommon s), κ ((enumCommon s a).1)
      let WCommon : ∀ s : Fin (q + 1) → ι, κCommon s → Opens X := fun s m ↦
        Finset.univ.inf fun a : Fin (nCommon s) ↦ W (enumCommon s a).1 (m a)
      have hWCommonCover : ∀ s : Fin (q + 1) → ι,
          (⋂ a : Fin (q + 1), (U (s a) : Set X)) = ⋃ m, (WCommon s m : Set X) := by
        intro s
        -- The common refinement for each lower-order tuple is chosen from the finite enumeration
        -- of all same-range extensions to `(q + 2)`-tuples.
        change
          (⋂ a : Fin (q + 1), (U (s a) : Set X)) =
            ⋃ m : (∀ a : Fin (nCommon s), κ ((enumCommon s a).1)),
              ((Finset.univ.inf fun a : Fin (nCommon s) ↦
                W (enumCommon s a).1 (m a) : Opens X) : Set X)
        exact Classical.choose_spec (Classical.choose_spec
          (common_refinement_cover_of_same_range_indexed (q := q) W hW_cover s))
      rcases ih (κ := κCommon) WCommon hWCommonCover with ⟨J, hJ, V, α, hRefCommon⟩
      have hRepeated :
          ∀ jTuple : Fin (q + 2) → J,
            ¬ Function.Injective (fun a ↦ α (jTuple a)) →
              (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) = ∅ ∨
                ∃ k : κ (fun a ↦ α (jTuple a)),
                  (⋂ a : Fin (q + 2), (V (jTuple a) : Set X)) ⊆
                    W (fun a ↦ α (jTuple a)) k := by
        intro jTuple hNoninj
        -- The lower-order common refinement already proves the repeated-label branch.
        exact tuplewise_subordinate_of_repeated_alpha hU W enumCommon hRefCommon jTuple hNoninj
      -- The remaining source-proof step is the finite descent on injective bad signatures.
      exact injective_signature_descent hU W hW_cover V α hRefCommon.isOpenCover
        (fun j ↦ hRefCommon.closure_subset j) hRepeated

/-- Helper for Lemma 5.13.5: compactness reduces the general ambient cover to the finite-index
induction target obtained from a finite subcover of `U`. -/
private theorem exists_tuplewise_shrinking_refinement_reduce_to_finite
    (hfinite :
      ∀ {ι' : Type v} [Fintype ι'] {U : ι' → Opens X} (hU : IsOpenCover U) (p : ℕ)
        {κ : (Fin (p + 1) → ι') → Type w}
        (W : ∀ s : Fin (p + 1) → ι', κ s → Opens X)
        (hW_cover : ∀ s : Fin (p + 1) → ι',
          (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)),
        ∃ (J : Type (max u v w)) (_ : Fintype J), ∃ (V : J → Opens X) (α : J → ι'),
          IsTuplewiseShrinkingRefinement hU p W V α)
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement hU p W V α := by
  classical
  rcases (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun i : ι ↦ (U i : Set X))
      (fun i ↦ (U i).isOpen)
      hU.iSup_set_eq_univ.ge with ⟨t, ht⟩
  let ι₀ : Type v := ↥t
  let U₀ : ι₀ → Opens X := fun i ↦ U i.1
  let κ₀ : (Fin (p + 1) → ι₀) → Type w := fun s ↦ κ (fun a ↦ (s a).1)
  let W₀ : ∀ s : Fin (p + 1) → ι₀, κ₀ s → Opens X := fun s k ↦ W (fun a ↦ (s a).1) k
  have hU₀_cover_set : (⋃ i : ι₀, (U₀ i : Set X)) = Set.univ := by
    -- The finite subtype indexed by the chosen subcover still covers all of `X`.
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases mem_iUnion₂.1 (ht (by simp)) with ⟨i, hi, hxi⟩
      exact mem_iUnion.2 ⟨⟨i, hi⟩, by simpa [U₀] using hxi⟩
  have hU₀_cover : IsOpenCover U₀ := by
    simpa [U₀] using IsOpenCover.of_sets (fun i ↦ (U₀ i).isOpen) hU₀_cover_set
  have hW₀_cover : ∀ s : Fin (p + 1) → ι₀,
      (⋂ a : Fin (p + 1), (U₀ (s a) : Set X)) = ⋃ k, (W₀ s k : Set X) := by
    -- The prescribed tuplewise covers are unchanged after passing to the finite subtype.
    intro s
    simpa [U₀, κ₀, W₀] using hW_cover (fun a ↦ (s a).1)
  rcases hfinite hU₀_cover p W₀ hW₀_cover with ⟨J, _, V, α₀, hRef₀⟩
  let α : J → ι := fun j ↦ (α₀ j).1
  refine ⟨J, V, α, ?_⟩
  refine ⟨hRef₀.isOpenCover, ?_, ?_⟩
  · -- Closure control transfers through the subtype-valued label map.
    intro j
    simpa [U₀, α] using hRef₀.closure_subset j
  · -- The tuplewise subordinate witness is identical after forgetting the subtype proof.
    intro jTuple
    simpa [κ₀, W₀, α] using hRef₀.tuplewise_subordinate jTuple

-- Proof sketch: first apply the compact-Hausdorff shrinking lemma to the original cover. Then
-- argue by induction on `p`: repeated source indices are handled by a common refinement of the
-- lower-fold intersection covers, while pairwise distinct source indices are treated by iteratively
-- cutting offending opens into finitely many pieces subordinate to the prescribed cover of the
-- corresponding `(p + 1)`-fold intersection, decreasing the bad-tuple count until it vanishes.
/-- Lemma 5.13.5: a quasi-compact Hausdorff open cover admits a shrinking refinement whose
closures stay inside the original cover and whose realized `(p + 1)`-fold intersections are either
empty or lie in one member of the prescribed open cover of the corresponding `(p + 1)`-fold
intersection of the original cover. -/
theorem exists_tuplewise_shrinking_refinement
    {U : ι → Opens X} (hU : IsOpenCover U) (p : ℕ)
    {κ : (Fin (p + 1) → ι) → Type w}
    (W : ∀ s : Fin (p + 1) → ι, κ s → Opens X)
    (hW_cover : ∀ s : Fin (p + 1) → ι,
      (⋂ a : Fin (p + 1), (U (s a) : Set X)) = ⋃ k, (W s k : Set X)) :
    ∃ (J : Type (max u v w)) (V : J → Opens X) (α : J → ι),
      IsTuplewiseShrinkingRefinement hU p W V α := by
  classical
  cases p with
  | zero =>
      -- The base case is exactly the sigma-indexed shrinking constructed above.
      simpa using exists_tuplewise_shrinking_refinement_zero hU W hW_cover
  | succ q =>
      -- First reduce to a finite ambient index type; the remaining induction lives entirely in
      -- the private finite theorem above, matching the source proof's finite bad-tuple descent.
      exact exists_tuplewise_shrinking_refinement_reduce_to_finite
        exists_tuplewise_shrinking_refinement_finite hU (q + 1) W hW_cover

end TopologicalSpace.IsOpenCover

end
