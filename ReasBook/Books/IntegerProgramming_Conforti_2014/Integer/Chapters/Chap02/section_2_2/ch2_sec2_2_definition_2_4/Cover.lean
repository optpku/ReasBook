module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic

public section

universe u

section KnapsackCover

variable {ι : Type u}

/-- A finite subset `C` is a cover when the total weight on `C` exceeds the knapsack capacity. -/
class IsKnapsackCover
    (weights : ι → ℕ) (capacity : ℕ) (C : Finset ι) : Prop where
  /-- The total weight on the cover is larger than the capacity. -/
  sum_gt_capacity : capacity < C.sum weights

/-- `IsKnapsackCover weights capacity C` unfolds to the overweight inequality on `C`. -/
theorem isKnapsackCover_iff
    (weights : ι → ℕ) (capacity : ℕ) (C : Finset ι) :
    IsKnapsackCover weights capacity C ↔ capacity < C.sum weights := by
  constructor
  · intro h
    -- Read the defining inequality from the cover structure field.
    exact h.sum_gt_capacity
  · intro h
    -- Rebuild the one-field cover structure from the overweight inequality.
    exact ⟨h⟩

section Minimal

variable [DecidableEq ι]

/-- A cover is minimal when removing any chosen index makes the remaining weight sum feasible. -/
class IsMinimalKnapsackCover
    (weights : ι → ℕ) (capacity : ℕ) (C : Finset ι) : Prop
    extends IsKnapsackCover weights capacity C where
  /-- Erasing any selected index from a minimal cover yields a feasible weight sum. -/
  erase_sum_le : ∀ i ∈ C, (C.erase i).sum weights ≤ capacity

/-- An `IsMinimalKnapsackCover` instance canonically supplies the underlying cover. -/
instance isMinimalKnapsackCover_to_isKnapsackCover
    (weights : ι → ℕ) (capacity : ℕ) (C : Finset ι)
    [h : IsMinimalKnapsackCover weights capacity C] :
    IsKnapsackCover weights capacity C :=
  h.toIsKnapsackCover

/-- `IsMinimalKnapsackCover weights capacity C` means that `C` is a cover and every single-index
erasure satisfies the capacity bound. -/
theorem isMinimalKnapsackCover_iff
    (weights : ι → ℕ) (capacity : ℕ) (C : Finset ι) :
    IsMinimalKnapsackCover weights capacity C ↔
      IsKnapsackCover weights capacity C ∧
        ∀ i ∈ C, (C.erase i).sum weights ≤ capacity := by
  constructor
  · intro h
    constructor
    · -- Project the inherited cover data from the minimal-cover structure.
      exact h.toIsKnapsackCover
    · -- Project the feasibility inequalities for each single-index erasure.
      exact h.erase_sum_le
  · intro h
    rcases h with ⟨hCover, hErase⟩
    -- Repackage the cover inequality and erase inequalities into the structure.
    exact
      { toIsKnapsackCover := hCover
        erase_sum_le := hErase }

namespace IsKnapsackCover

/-- Every knapsack cover contains a minimal knapsack cover. -/
theorem exists_isMinimalKnapsackCover_subset
    {weights : ι → ℕ} {capacity : ℕ} {J : Finset ι}
    (hJCover : IsKnapsackCover weights capacity J) :
    ∃ C ⊆ J, IsMinimalKnapsackCover weights capacity C := by
  let candidates : Finset (Finset ι) :=
    J.powerset.filter (fun C ↦ capacity < C.sum weights)
  have hCandidatesNonempty : candidates.Nonempty := by
    refine ⟨J, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact Finset.mem_powerset.mpr (fun _ h ↦ h)
    · exact (isKnapsackCover_iff weights capacity J).mp hJCover
  obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image candidates Finset.card hCandidatesNonempty
  have hCsubset : C ⊆ J :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hCmem).1
  have hCCover : IsKnapsackCover weights capacity C :=
    (isKnapsackCover_iff weights capacity C).2 (Finset.mem_filter.mp hCmem).2
  refine ⟨C, hCsubset, ?_⟩
  refine (isMinimalKnapsackCover_iff weights capacity C).2 ?_
  constructor
  · exact hCCover
  · intro i hi
    by_contra hEraseLe
    have hEraseMem : C.erase i ∈ candidates := by
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Finset.mem_powerset.mpr (fun j hj ↦ hCsubset ((Finset.erase_subset i C) hj))
      · exact lt_of_not_ge hEraseLe
    have hCardLe : C.card ≤ (C.erase i).card := hCmin (C.erase i) hEraseMem
    have hCardLt : (C.erase i).card < C.card := Finset.card_erase_lt_of_mem hi
    exact (Nat.not_le_of_lt hCardLt) hCardLe

end IsKnapsackCover

end Minimal

/-- The right-hand side `|C| - 1` of the cover inequality attached to `C`. -/
def cover_inequality_rhs (C : Finset ι) : ℝ :=
  (C.card : ℝ) - 1

/-- `cover_inequality_rhs C` unfolds to `(C.card : ℝ) - 1`. -/
theorem cover_inequality_rhs_eq
    (C : Finset ι) :
    cover_inequality_rhs C = (C.card : ℝ) - 1 := by
  -- Unfold the numeric right-hand side of the cover inequality.
  rfl

end KnapsackCover
