/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_definition_1_8

public section

open scoped MixedIntegerNotation

namespace MilpBranchAndBound

section Proposition12Partition

variable {n m : ℕ}

namespace BranchFeasibleSet

/-- The two Definition 1.8 branch feasible sets are disjoint when the branching value has
nonzero fractional part. This is the canonical set-theoretic form of Proposition 1.2 (1). -/
theorem disjoint_of_fract_ne_zero
    (S : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ)
    (hf_frac : Int.fract f ≠ 0) :
    Disjoint (leftBranchFeasibleSet S j f) (rightBranchFeasibleSet S j f) := by
  refine Set.disjoint_left.2 ?_
  intro xy hxy_left hxy_right
  have hleft := (mem_leftBranchFeasibleSet_iff.mp hxy_left).2
  have hright := (mem_rightBranchFeasibleSet_iff.mp hxy_right).2
  have hceil_le_floor_real : (Int.ceil f : ℝ) ≤ Int.floor f :=
    le_trans hright hleft
  have hceil_le_floor : Int.ceil f ≤ Int.floor f := by
    exact_mod_cast hceil_le_floor_real
  have hfloor_lt_ceil : Int.floor f < Int.ceil f := by
    rw [(Int.ceil_eq_floor_add_one_iff_notMem f).2 ((Int.fract_ne_zero_iff).mp hf_frac)]
    exact Int.lt_add_one_iff.mpr le_rfl
  exact (not_lt_of_ge hceil_le_floor) hfloor_lt_ceil

/-- An integral feasible point of `S` lies in at least one of the two Definition 1.8 branch
feasible sets at coordinate `j`. -/
theorem mem_union_of_mem_mixed_integer_lattice
    {S : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m}
    (hxyS : xy ∈ S)
    (hxy_int : xy ∈ mixed_integer_lattice n m) :
    xy ∈ leftBranchFeasibleSet S j f ∨ xy ∈ rightBranchFeasibleSet S j f := by
  rcases mem_mixed_integer_lattice_exists_iff.mp hxy_int with ⟨z, hz⟩
  have hzj : xy.1 j = (z j : ℝ) := by
    simpa [Function.comp] using congrFun hz j
  by_cases hzle : z j ≤ Int.floor f
  · left
    rw [mem_leftBranchFeasibleSet_iff]
    refine ⟨hxyS, ?_⟩
    exact by
      have hzle_real : ((z j : ℤ) : ℝ) ≤ Int.floor f := by
        exact_mod_cast hzle
      simpa [hzj] using hzle_real
  · right
    rw [mem_rightBranchFeasibleSet_iff]
    refine ⟨hxyS, ?_⟩
    have hfloor_lt_z : Int.floor f < z j := lt_of_not_ge hzle
    have hceil_le_z : Int.ceil f ≤ z j := by
      exact le_trans (Int.ceil_le_floor_add_one f) (Int.add_one_le_iff.mpr hfloor_lt_z)
    have hceil_le_z_real : (Int.ceil f : ℝ) ≤ (z j : ℝ) := by
      exact_mod_cast hceil_le_z
    simpa [hzj] using hceil_le_z_real

/-- If every point of `S` is mixed-integer feasible, then `S` is contained in the union of the
two Definition 1.8 branch feasible sets. -/
theorem subset_union_of_subset_mixed_integer_lattice
    (S : Set (MixedRealPoint n m))
    (hS : S ⊆ mixed_integer_lattice n m)
    (j : Fin n)
    (f : ℝ) :
    S ⊆ leftBranchFeasibleSet S j f ∪ rightBranchFeasibleSet S j f := by
  intro xy hxy
  exact mem_union_of_mem_mixed_integer_lattice hxy (hS hxy)

end BranchFeasibleSet

end Proposition12Partition

end MilpBranchAndBound

end
