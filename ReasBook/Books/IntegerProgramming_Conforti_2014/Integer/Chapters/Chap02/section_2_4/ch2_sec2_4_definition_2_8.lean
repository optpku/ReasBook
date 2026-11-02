module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_9.Optimization

public section

namespace SetFamilyOptimization

variable {m n : ℕ}

/-- Definition 2.8 (1) [Packing, partitioning, covering and their 0/1 formulations]:
A finite subset `s` of `Fin n` is a packing of `family` when each member `family i`
meets `s` in at most one point. -/
def IsPacking (family : Fin m → Finset (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ i, (s ∩ family i).card ≤ 1

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_definition_2_8.lean
Unfolding specification for `IsPacking`. -/
theorem isPacking_iff
    {family : Fin m → Finset (Fin n)} {s : Finset (Fin n)} :
    IsPacking family s ↔ ∀ i, (s ∩ family i).card ≤ 1 := by
  -- Unfolding `IsPacking` makes the two sides definitionally identical.
  rfl

/-- Definition 2.8 (2) [Packing, partitioning, covering and their 0/1 formulations]:
A finite subset `s` of `Fin n` is a partitioning of `family` when each member `family i`
meets `s` in exactly one point. -/
def IsPartitioning (family : Fin m → Finset (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ i, (s ∩ family i).card = 1

/-- Unfolding specification for `IsPartitioning`. -/
theorem isPartitioning_iff
    {family : Fin m → Finset (Fin n)} {s : Finset (Fin n)} :
    IsPartitioning family s ↔ ∀ i, (s ∩ family i).card = 1 := by
  -- Unfolding `IsPartitioning` makes the two sides definitionally identical.
  rfl

/-- Definition 2.8 (3) [Packing, partitioning, covering and their 0/1 formulations]:
A finite subset `s` of `Fin n` is a covering of `family` when each member `family i`
meets `s` in at least one point. -/
def IsCovering (family : Fin m → Finset (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ i, 1 ≤ (s ∩ family i).card

/-- Unfolding specification for `IsCovering`. -/
theorem isCovering_iff
    {family : Fin m → Finset (Fin n)} {s : Finset (Fin n)} :
    IsCovering family s ↔ ∀ i, 1 ≤ (s ∩ family i).card := by
  -- Unfolding `IsCovering` makes the two sides definitionally identical.
  rfl

end SetFamilyOptimization

/- Definition 2.8 (4) [Packing, partitioning, covering and their 0/1 formulations]:
The canonical `0/1` vector owner for the packing formulation is
`SetFamilyOptimization.packingFeasibleSet`, together with its membership specification. -/
#check SetFamilyOptimization.packingFeasibleSet
#check SetFamilyOptimization.mem_packingFeasibleSet_iff

/- Definition 2.8 (5) [Packing, partitioning, covering and their 0/1 formulations]:
The canonical `0/1` vector owner for the partitioning formulation is
`SetFamilyOptimization.partitioningFeasibleSet`, together with its membership specification. -/
#check SetFamilyOptimization.partitioningFeasibleSet
#check SetFamilyOptimization.mem_partitioningFeasibleSet_iff

/- Definition 2.8 (6) [Packing, partitioning, covering and their 0/1 formulations]:
The canonical `0/1` vector owner for the covering formulation is
`SetFamilyOptimization.coveringFeasibleSet`, together with its membership specification. -/
#check SetFamilyOptimization.coveringFeasibleSet
#check SetFamilyOptimization.mem_coveringFeasibleSet_iff
