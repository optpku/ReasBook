/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace Set

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

-- Route correction: the file uses the imported project notion `IsCone = (Ioi 0) • _`,
-- so the proofs proceed through the `sInter` universal property of that existing notion.

-- Proof sketch: for the forward direction, rewrite `IsCone K` using the existing project
-- definition and unpack membership in a pointwise scalar multiple; for the reverse direction,
-- use the nonnegative-scalar closure hypothesis with `1 ≥ 0` and the existing characterization
-- of `IsCone`.
/-- The project predicate `IsCone` is the positive-scalar cone convention used earlier in the
book.  It is not the closed-under-`0` convention; the latter would force every cone to contain
`0`, which is not the convention formalized in `Text_1_0_2`. -/
theorem isCone_iff_nonneg_smul_mem {K : Set X} :
    IsCone K ↔ K = (Ioi (0 : ℝ) : Set ℝ) • K := by
  -- This is exactly the imported project definition of `IsCone`.
  exact isCone_iff

/-- Helper for Definition 6.1: the intersection of any family of project cones is again a cone. -/
lemma isCone_sInter {S : Set (Set X)} (hS : ∀ K ∈ S, IsCone K) :
    IsCone (⋂₀ S) := by
  rw [isCone_iff_nonneg_smul_mem]
  refine Subset.antisymm ?_ ?_
  · -- The unit scalar shows that every point of the intersection is already a positive multiple.
    intro x hx
    have hone : (1 : ℝ) ∈ Ioi (0 : ℝ) := by
      simp
    have hEq : (1 : ℝ) • x = x := by
      simp
    exact Set.mem_smul.mpr ⟨1, hone, x, hx, hEq⟩
  · -- Unpack a positive multiple of a point in the intersection and check each set separately.
    intro x hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, hEq⟩
    rw [← hEq]
    refine Set.mem_sInter.mpr ?_
    intro K hK
    have hyK : y ∈ K := (Set.mem_sInter.mp hy) K hK
    have hconeK : IsCone K := hS K hK
    have hmem : a • y ∈ (Ioi (0 : ℝ) : Set ℝ) • K := by
      have hEq' : a • y = a • y := rfl
      exact Set.mem_smul.mpr ⟨a, ha, y, hyK, hEq'⟩
    exact (isCone_iff_nonneg_smul_mem.mp hconeK).symm ▸ hmem

/-- Definition 6.1: the conical hull `cone C` is the intersection of all cones containing `C`,
hence the smallest cone containing `C`. -/
def conicalHull (C : Set X) : Set X :=
  sInter {K : Set X | IsCone K ∧ C ⊆ K}

-- Proof sketch: if `x ∈ C`, then `x` belongs to every cone `K` with `C ⊆ K`; therefore `x`
-- belongs to the intersection defining `cone C`.
/-- Every set is contained in its conical hull. -/
theorem subset_conicalHull (C : Set X) :
    C ⊆ conicalHull C := by
  -- A point of `C` belongs to every cone in the defining intersection.
  refine Set.subset_sInter ?_
  intro K hK
  exact hK.2

-- Proof sketch: intersect the closure-under-nonnegative-scalars property over all cones that
-- contain `C`, using the companion characterization `isCone_iff_nonneg_smul_mem`.
/-- The conical hull of a set is a cone. -/
theorem isCone_conicalHull (C : Set X) :
    IsCone (conicalHull C) := by
  -- The defining family consists entirely of cones, so the generic `sInter` lemma applies.
  simpa [conicalHull] using
    (isCone_sInter
      (S := {K : Set X | IsCone K ∧ C ⊆ K})
      (fun K hK ↦ hK.1))

-- Proof sketch: `cone C` is one of the sets in the defining intersection of cones containing
-- `C`, so membership in the intersection gives the desired inclusion.
/-- The conical hull is contained in every cone that contains the original set. -/
theorem conicalHull_min {C K : Set X} (hK : IsCone K) (hCK : C ⊆ K) :
    conicalHull C ⊆ K := by
  -- The witness `K` belongs to the defining family of the intersection.
  have hmem : K ∈ {K : Set X | IsCone K ∧ C ⊆ K} := And.intro hK hCK
  simpa [conicalHull] using
    (Set.sInter_subset_of_mem hmem : sInter {K : Set X | IsCone K ∧ C ⊆ K} ⊆ K)

end

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- The closed conical hull of a set is the intersection of all closed cones containing it. -/
def closedConicalHull (C : Set X) : Set X :=
  sInter {K : Set X | IsCone K ∧ IsClosed K ∧ C ⊆ K}

-- Proof sketch: if `x ∈ C`, then `x` belongs to every closed cone `K` containing `C`; hence `x`
-- belongs to the intersection defining `closedConicalHull C`.
/-- Every set is contained in its closed conical hull. -/
theorem subset_closedConicalHull (C : Set X) :
    C ⊆ closedConicalHull C := by
  -- A point of `C` belongs to every closed cone in the defining family.
  refine Set.subset_sInter ?_
  intro K hK
  exact hK.2.2

-- Proof sketch: intersections of closed sets are closed, and every set in the defining family of
-- `closedConicalHull C` is closed by construction.
/-- The closed conical hull is a closed set. -/
theorem isClosed_closedConicalHull (C : Set X) :
    IsClosed (closedConicalHull C) := by
  -- Closedness is inherited pointwise from the defining intersection family.
  refine isClosed_sInter ?_
  intro K hK
  exact hK.2.1

-- Proof sketch: intersect the cone property over all closed cones that contain `C`, exactly as
-- for `conicalHull`, using the characterization of `IsCone` by nonnegative scalar closure.
/-- The closed conical hull of a set is a cone. -/
theorem isCone_closedConicalHull (C : Set X) :
    IsCone (closedConicalHull C) := by
  -- The closed defining family is still a family of cones, so reuse `isCone_sInter`.
  simpa [closedConicalHull] using
    (isCone_sInter
      (S := {K : Set X | IsCone K ∧ IsClosed K ∧ C ⊆ K})
      (fun K hK ↦ hK.1))

-- Proof sketch: `closedConicalHull C` is defined as the intersection of all closed cones
-- containing `C`, so it is contained in any specific closed cone `K` containing `C`.
/-- The closed conical hull is contained in every closed cone that contains the original set. -/
theorem closedConicalHull_min {C K : Set X} (hKcone : IsCone K) (hKclosed : IsClosed K)
    (hCK : C ⊆ K) :
    closedConicalHull C ⊆ K := by
  -- The witness `K` belongs to the defining family of closed cones containing `C`.
  have hmem : K ∈ {K : Set X | IsCone K ∧ IsClosed K ∧ C ⊆ K} :=
    And.intro hKcone (And.intro hKclosed hCK)
  simpa [closedConicalHull] using
    (Set.sInter_subset_of_mem hmem :
      sInter {K : Set X | IsCone K ∧ IsClosed K ∧ C ⊆ K} ⊆ K)

end

end Set
