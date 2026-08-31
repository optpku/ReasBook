module

public import stacks_project.Chap05.Definition_5_28_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for good stratifications of a topological space:
- inspected project declarations in the same chapter/domain:
  `LocallyClosedPartition`,
  `LocallyClosedPartition.toSet`,
  `LocallyClosedPartition.singletons`,
  and the later indexed owner `IsStratification`
- best owner abstraction for this source item: `LocallyClosedPartition.IsGood`

Layer triage:
- `source-facing`: the frontier condition on a locally closed partition
- `core/canonical`: `LocallyClosedPartition.IsGood`
- `bridge/view`: Lemma `5.28.6` turns a good partition into an indexed `IsStratification`

Primitive data are only the frontier condition on actual parts of `P`, i.e. elements of the owner
subtype `P.toSet`. Membership proofs for arbitrary `Set X` are derived accessors and should not be
the primitive field shape.
-/

namespace LocallyClosedPartition

/-- Definition 5.28.2: a good stratification of a topological space is a locally closed partition
whose strata satisfy the frontier condition that whenever one stratum meets the closure of
another, it is contained in that closure. -/
class IsGood (P : LocallyClosedPartition X) : Prop where
  frontier_condition (S T : P.toSet) (hST : ((S : Set X) ∩ closure (T : Set X)).Nonempty) :
      (S : Set X) ⊆ closure (T : Set X)

/-- Explicit-set accessor for the frontier condition on parts of a good partition. -/
theorem frontier_condition_of_mem {P : LocallyClosedPartition X} [hP : IsGood P]
    {S T : Set X} (hS : S ∈ P.toSet) (hT : T ∈ P.toSet)
    (hST : (S ∩ closure T).Nonempty) :
    S ⊆ closure T :=
  hP.frontier_condition ⟨S, hS⟩ ⟨T, hT⟩ hST

/-- The singleton partition of a `T₁` space is a good stratification. -/
instance [T1Space X] : IsGood (singletons X) where
  frontier_condition := by
    intro S T h
    rcases S with ⟨S, hS⟩
    rcases T with ⟨T, hT⟩
    rcases hS with ⟨x, rfl⟩
    rcases hT with ⟨y, rfl⟩
    have hx : x ∈ closure ({y} : Set X) := by
      rcases h with ⟨z, hz, hzclosure⟩
      simpa only [Set.mem_singleton_iff.mp hz] using hzclosure
    intro z hz
    have hz' : z = x := by
      simpa using hz
    subst z
    simpa [closure_singleton] using hx

end LocallyClosedPartition
