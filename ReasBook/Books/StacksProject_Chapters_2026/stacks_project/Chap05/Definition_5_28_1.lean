module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.Separation.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

/- Domain-style sampling for partitions with topological regularity:
- inspected canonical partition declarations in mathlib:
  `Setoid.Partitions`,
  `Setoid.Partitions.toSet`,
  `Setoid.Partitions.isPartition`,
  and `Setoid.Partition.orderIso`
- best owner abstraction: `Setoid.Partitions X`

Layer triage:
- `source-facing`: `LocallyClosedPartition X`
- `core/canonical`: the underlying owner `Setoid.Partitions X`
- `bridge/view`: the refinement order and the singleton example

Primitive data are a partition together with local closedness of each actual part, i.e. the owner
subtype `toPartitions.toSet`. The set-theoretic partition facts and refinement API are derived.
-/

/-- Definition 5.28.1: a partition of a topological space is a decomposition into locally closed
subsets. -/
structure LocallyClosedPartition (X : Type u) [TopologicalSpace X] where
  toPartitions : Setoid.Partitions X
  locallyClosed (s : toPartitions.toSet) : IsLocallyClosed (s : Set X)

namespace LocallyClosedPartition

variable {X : Type u} [TopologicalSpace X]

/-- The set of parts of a locally closed partition. -/
abbrev toSet (P : LocallyClosedPartition X) : Set (Set X) :=
  P.toPartitions.toSet

@[ext]
theorem ext {P Q : LocallyClosedPartition X} (h : P.toSet = Q.toSet) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      simp only [toSet] at h
      have hpq : p = q := (Setoid.Partitions.ext_iff _ _).2 h
      cases hpq
      simp

/-- Explicit-set accessor for the local closedness of a part. -/
theorem locallyClosed_of_mem (P : LocallyClosedPartition X) {s : Set X} (hs : s ∈ P.toSet) :
    IsLocallyClosed s :=
  P.locallyClosed ⟨s, hs⟩

/-- The parts of a locally closed partition form a set-theoretic partition of the whole space. -/
theorem isPartition (P : LocallyClosedPartition X) : Setoid.IsPartition P.toSet :=
  P.toPartitions.isPartition

instance : PartialOrder (LocallyClosedPartition X) :=
  PartialOrder.lift toPartitions fun _ _ h ↦
    ext <| Setoid.Partitions.ext_iff _ _ |>.1 h

omit [TopologicalSpace X] in
/-- A part of the discrete partition is exactly a singleton. -/
theorem mem_singletons_toSet_iff {s : Set X} :
    s ∈ ((⊥ : Setoid.Partitions X).toSet) ↔ ∃ x : X, s = ({x} : Set X) := by
  change s ∈ (⊥ : Setoid X).classes ↔ _
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    ext y
    simp
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    ext y
    simp

/-- The partition of a `T₁` space into singleton strata. -/
def singletons (X : Type u) [TopologicalSpace X] [T1Space X] : LocallyClosedPartition X where
  toPartitions := ⊥
  locallyClosed s := by
    rcases mem_singletons_toSet_iff.mp s.2 with ⟨x, hs⟩
    simpa [hs] using isClosed_singleton.isLocallyClosed

/-- Refinement is equivalently the statement that each part of the finer partition is contained in
some part of the coarser partition. -/
theorem le_iff_forall_exists_mem_subset {P Q : LocallyClosedPartition X} :
    P ≤ Q ↔ ∀ ⦃s : Set X⦄, s ∈ P.toSet → ∃ t ∈ Q.toSet, s ⊆ t := by
  let hP := P.isPartition.2
  let hQ := Q.isPartition.2
  constructor
  · intro hPQ s hs
    obtain ⟨x, hx⟩ := Setoid.nonempty_of_mem_partition P.isPartition hs
    obtain ⟨t, htx, _⟩ := hQ x
    refine ⟨t, htx.1, ?_⟩
    intro y hy
    have hxy : Setoid.mkClasses P.toSet hP x y := by
      rw [Setoid.eq_eqv_class_of_mem hP hs hy] at hx
      exact hx
    exact hPQ hxy t htx.1 htx.2
  · intro hPQ x y hxy s hs hx_s
    obtain ⟨u, hux, _⟩ := hP x
    obtain ⟨t, htQ, hut⟩ := hPQ hux.1
    have hx_t : x ∈ t := hut hux.2
    have hy_t : y ∈ t := hut (hxy u hux.1 hux.2)
    have hts : t = s := Setoid.eq_of_mem_eqv_class hQ htQ hx_t hs hx_s
    simpa [hts] using hy_t

end LocallyClosedPartition
