/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_10.IncidenceMatrix
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_10.PackingPartitioning
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_9.Optimization
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_5_definition_2_25.SetCovering

public section

/-!
Incidence matrix and matrix formulations.

This item is formalized by the reusable constructor `Matrix.incidenceMatrix`, the
matrix-side packing and partitioning owners `SetPacking.feasibleSet` and
`SetPartitioning.feasibleSet`, and the existing matrix-side covering owner
`SetCovering.feasibleSet`.
-/

/- The canonical owners for the incidence matrix and the matrix-side packing, partitioning, and
covering feasible regions are the declarations below. -/
#check Matrix.incidenceMatrix
#check Matrix.incidenceMatrix_apply
#check Matrix.incidenceMatrix_mulVec_apply
#check SetPacking.feasibleSet
#check SetPacking.mem_feasibleSet_iff
#check SetPartitioning.feasibleSet
#check SetPartitioning.mem_feasibleSet_iff
#check SetCovering.feasibleSet
#check SetCovering.mem_feasibleSet_iff

namespace SetFamilyOptimization

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_definition_2_10.lean

Definition 2.10 (1): the family-side packing feasible region from Definition 2.9 agrees with
the matrix-side packing feasible region of the incidence matrix of the family. -/
theorem packingFeasibleSet_eq_incidenceMatrix
    {m n : ℕ} (family : Fin m → Finset (Fin n)) :
    packingFeasibleSet family =
      SetPacking.feasibleSet (Matrix.incidenceMatrix family) := by
  -- Compare the two feasible regions pointwise, retaining their common binary condition.
  ext x
  rw [mem_packingFeasibleSet_iff, SetPacking.mem_feasibleSet_iff]
  constructor
  · rintro ⟨hbinary, hrows⟩
    refine ⟨hbinary, ?_⟩
    -- The matrix inequality is precisely the family of row-sum inequalities.
    rw [Pi.le_def]
    intro i
    simpa only [Matrix.incidenceMatrix_mulVec_apply, Pi.one_apply] using hrows i
  · rintro ⟨hbinary, hmatrix⟩
    refine ⟨hbinary, ?_⟩
    -- Evaluate the pointwise matrix inequality at each incidence row.
    rw [Pi.le_def] at hmatrix
    intro i
    simpa only [Matrix.incidenceMatrix_mulVec_apply, Pi.one_apply] using hmatrix i

/-- Definition 2.10 (2): the family-side partitioning feasible region from Definition 2.9 agrees
with the matrix-side partitioning feasible region of the incidence matrix of the family. -/
theorem partitioningFeasibleSet_eq_incidenceMatrix
    {m n : ℕ} (family : Fin m → Finset (Fin n)) :
    partitioningFeasibleSet family =
      SetPartitioning.feasibleSet (Matrix.incidenceMatrix family) := by
  -- Compare membership and separate the shared binary condition from the row equations.
  ext x
  rw [mem_partitioningFeasibleSet_iff, SetPartitioning.mem_feasibleSet_iff]
  constructor
  · rintro ⟨hbinary, hrows⟩
    refine ⟨hbinary, ?_⟩
    -- Assemble the matrix-vector equation from its incidence-row components.
    funext i
    simpa only [Matrix.incidenceMatrix_mulVec_apply, Pi.one_apply] using hrows i
  · rintro ⟨hbinary, hmatrix⟩
    refine ⟨hbinary, ?_⟩
    -- Recover each family equation by evaluating the matrix-vector equality.
    intro i
    simpa only [Matrix.incidenceMatrix_mulVec_apply, Pi.one_apply] using congrFun hmatrix i

/-- Definition 2.10 (3): the family-side covering feasible region from Definition 2.9 agrees
with the matrix-side covering feasible region of the incidence matrix of the family. -/
theorem coveringFeasibleSet_eq_incidenceMatrix
    {m n : ℕ} (family : Fin m → Finset (Fin n)) :
    coveringFeasibleSet family =
      SetCovering.feasibleSet (Matrix.incidenceMatrix family) := by
  -- Compare the two feasible regions pointwise, retaining their common binary condition.
  ext x
  rw [mem_coveringFeasibleSet_iff, SetCovering.mem_feasibleSet_iff]
  constructor
  · rintro ⟨hbinary, hrows⟩
    refine ⟨hbinary, ?_⟩
    -- The matrix lower bound is exactly the family of covering inequalities.
    rw [Pi.le_def]
    intro i
    simpa only [Matrix.incidenceMatrix_mulVec_apply, Pi.one_apply] using hrows i
  · rintro ⟨hbinary, hmatrix⟩
    refine ⟨hbinary, ?_⟩
    -- Evaluate the pointwise lower bound at each incidence row.
    rw [Pi.le_def] at hmatrix
    intro i
    simpa only [Matrix.incidenceMatrix_mulVec_apply, Pi.one_apply] using hmatrix i

#print axioms packingFeasibleSet_eq_incidenceMatrix
#print axioms partitioningFeasibleSet_eq_incidenceMatrix
#print axioms coveringFeasibleSet_eq_incidenceMatrix

end SetFamilyOptimization

end
