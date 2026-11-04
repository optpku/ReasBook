/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_proposition_1_2.Partition

public section

open MilpBranchAndBound

section Proposition12

variable {n m : ℕ}

/-- Proposition 1.2 (1) [Branching partition]. If the branching value `f` is
nonintegral, then the two Definition 1.8 branch sets are disjoint. The
extracted source omits the needed hypothesis `Int.fract f ≠ 0`, so it is
stated explicitly here. -/
theorem branchingPartitionDisjointOfFrac
    (S : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ)
    (hf_frac : Int.fract f ≠ 0) :
    leftBranchFeasibleSet S j f ∩ rightBranchFeasibleSet S j f = (∅ : Set (MixedRealPoint n m)) :=
  Set.disjoint_iff_inter_eq_empty.mp
    (BranchFeasibleSet.disjoint_of_fract_ne_zero S j f hf_frac)

/-- Proposition 1.2 (2) [Branching partition]. The branched coordinate is
integral on `S`, so the left and right Definition 1.8 branch sets cover `S`.
The extracted source also asserts disjointness, but that clause needs the extra
hypothesis `Int.fract f ≠ 0` and is recorded separately as
`branchingPartitionDisjointOfFrac`. -/
theorem branchingPartitionCover
    (S : Set (MixedRealPoint n m))
    (hS : S ⊆ mixed_integer_lattice n m)
    (j : Fin n)
    (f : ℝ) :
    leftBranchFeasibleSet S j f ∪ rightBranchFeasibleSet S j f = S := by
  apply Set.Subset.antisymm
  · intro xy hxy
    rw [Set.mem_union] at hxy
    rcases hxy with hxy | hxy
    · exact (mem_leftBranchFeasibleSet_iff.mp hxy).1
    · exact (mem_rightBranchFeasibleSet_iff.mp hxy).1
  · exact BranchFeasibleSet.subset_union_of_subset_mixed_integer_lattice S hS j f

end Proposition12

end
