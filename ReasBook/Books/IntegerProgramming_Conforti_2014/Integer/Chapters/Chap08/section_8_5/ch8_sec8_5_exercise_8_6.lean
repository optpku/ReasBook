import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Finite.Lemmas
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_remark_8_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: the domain-sampling pass identified Example 8.14 as the owner of the
-- generalized-assignment LP-feasibility predicate and the machine-wise `0,1` knapsack block
-- family. This file therefore keeps only the Exercise 8.6 Lagrangian-relaxation layer local and
-- reuses those upstream generalized-assignment declarations directly.

noncomputable section

section Exercise86

/-- The Example 8.14 block-coefficient family specialized to the Exercise 8.6 item sizes `a_i`,
constant in the machine index. -/
def generalized_assignment_capacity_coeffs {m n : ℕ}
    (a : Fin m → ℝ) : Fin m → Fin n → ℝ :=
  fun i _ ↦ a i

/-- `generalized_assignment_capacity_coeffs a` is constant in the machine index. -/
@[simp] theorem generalized_assignment_capacity_coeffs_apply {m n : ℕ}
    (a : Fin m → ℝ) (i : Fin m) (j : Fin n) :
    generalized_assignment_capacity_coeffs a i j = a i :=
  rfl

/-- The objective value `∑_i ∑_j c_ij x_ij` of a binary generalized-assignment pattern. -/
def generalized_assignment_objective {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (x : Fin m → Fin n → Bool) : ℝ :=
  ∑ i, ∑ j, c i j * bool_entry (x i j)

/-- `generalized_assignment_objective c x` unfolds to `∑_i ∑_j c_ij x_ij`. -/
theorem generalized_assignment_objective_eq_sum {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (x : Fin m → Fin n → Bool) :
    generalized_assignment_objective c x = ∑ i, ∑ j, c i j * bool_entry (x i j) :=
  rfl

/-- The base set obtained by keeping only the assignment constraints `∑_j x_ij ≤ 1`
and the binary restrictions. This is the easy set used when the capacity constraints are
dualized. -/
def generalized_assignment_assignment_base_set {m n : ℕ} : Set (Fin m → Fin n → Bool) :=
  {x | ∀ i, ∑ j, bool_entry (x i j) ≤ 1}

/-- Membership in `generalized_assignment_assignment_base_set` means exactly that every item is
assigned to at most one machine. -/
theorem mem_generalized_assignment_assignment_base_set_iff {m n : ℕ}
    {x : Fin m → Fin n → Bool} :
    x ∈ generalized_assignment_assignment_base_set ↔
      ∀ i, ∑ j, bool_entry (x i j) ≤ 1 :=
  Iff.rfl

/-- The base set obtained by keeping only the capacity constraints
`∑_i a_i x_ij ≤ b_j` and the binary restrictions. This is the easy set used when the
assignment constraints are dualized. -/
def generalized_assignment_capacity_base_set {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) : Set (Fin m → Fin n → Bool) :=
  {x |
    ∀ j, (fun i ↦ x i j) ∈ generalized_assignment_block_patterns
      (generalized_assignment_capacity_coeffs a) b j
  }

/-- Membership in `generalized_assignment_capacity_base_set a b` is exactly the family of
machine-wise knapsack inequalities `∑_i a_i x_ij ≤ b_j`. -/
theorem mem_generalized_assignment_capacity_base_set_iff {m n : ℕ}
    {a : Fin m → ℝ} {b : Fin n → ℝ} {x : Fin m → Fin n → Bool} :
    x ∈ generalized_assignment_capacity_base_set a b ↔
      ∀ j, ∑ i, a i * bool_entry (x i j) ≤ b j := by
  simp [generalized_assignment_capacity_base_set, mem_generalized_assignment_block_patterns_iff]

/-- The LP-relaxation value of the generalized assignment problem. -/
def generalized_assignment_lp_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sSup
    ((fun x : Fin m → Fin n → ℝ ↦ ∑ i, ∑ j, c i j * x i j) ''
      {x | generalized_assignment_lp_feasible (generalized_assignment_capacity_coeffs a) b x})

/-- `generalized_assignment_lp_value a b c` unfolds to the supremum of the linear objective over
the LP-feasible set. -/
theorem generalized_assignment_lp_value_eq_sSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_lp_value a b c =
      sSup
        ((fun x : Fin m → Fin n → ℝ ↦ ∑ i, ∑ j, c i j * x i j) ''
          {x |
            generalized_assignment_lp_feasible
              (generalized_assignment_capacity_coeffs a) b x}) :=
  rfl

/-- The Lagrangian relaxation value obtained by dualizing the capacity constraints
`∑_i a_i x_ij ≤ b_j` with nonnegative multipliers `μ_j` and keeping the assignment constraints
and the binary restrictions in the base set. -/
def generalized_assignment_capacity_relaxed_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) : ℝ :=
  sSup
    ((fun x : Fin m → Fin n → Bool ↦
        generalized_assignment_objective c x +
          ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))) ''
      generalized_assignment_assignment_base_set)

/-- `generalized_assignment_capacity_relaxed_value a b c μ` unfolds to the supremum of the
capacity-relaxed Lagrangian objective over `generalized_assignment_assignment_base_set`. -/
theorem generalized_assignment_capacity_relaxed_value_eq_sSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_value a b c μ =
      sSup
        ((fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))) ''
          generalized_assignment_assignment_base_set) :=
  rfl

/-- The Lagrangian dual obtained by dualizing the capacity constraints. -/
def generalized_assignment_capacity_relaxed_dual_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf
    ((fun μ : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c μ) ''
      Set.Ici (0 : Fin n → ℝ))

/-- `generalized_assignment_capacity_relaxed_dual_value a b c` unfolds to the infimum of the
capacity-relaxed values over all nonnegative multiplier vectors `μ`. -/
theorem generalized_assignment_capacity_relaxed_dual_value_eq_sInf {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_dual_value a b c =
      sInf
        ((fun μ : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c μ) ''
          Set.Ici (0 : Fin n → ℝ)) :=
  rfl

/-- The Lagrangian relaxation value obtained by dualizing the assignment constraints
`∑_j x_ij ≤ 1` with nonnegative multipliers `λ_i` and keeping the capacity constraints and the
binary restrictions in the base set. -/
def generalized_assignment_assignment_relaxed_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) : ℝ :=
  sSup
    ((fun x : Fin m → Fin n → Bool ↦
        generalized_assignment_objective c x +
          ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
      generalized_assignment_capacity_base_set a b)

/-- `generalized_assignment_assignment_relaxed_value a b c λ` unfolds to the supremum of the
assignment-relaxed Lagrangian objective over `generalized_assignment_capacity_base_set a b`. -/
theorem generalized_assignment_assignment_relaxed_value_eq_sSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) :
    generalized_assignment_assignment_relaxed_value a b c lam =
      sSup
        ((fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
          generalized_assignment_capacity_base_set a b) :=
  rfl

/-- The Lagrangian dual obtained by dualizing the assignment constraints. -/
def generalized_assignment_assignment_relaxed_dual_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) : ℝ :=
  sInf
    ((fun lam : Fin m → ℝ ↦ generalized_assignment_assignment_relaxed_value a b c lam) ''
      Set.Ici (0 : Fin m → ℝ))

/-- `generalized_assignment_assignment_relaxed_dual_value a b c` unfolds to the infimum of the
assignment-relaxed values over all nonnegative multiplier vectors `λ`. -/
theorem generalized_assignment_assignment_relaxed_dual_value_eq_sInf {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_assignment_relaxed_dual_value a b c =
      sInf
        ((fun lam : Fin m → ℝ ↦ generalized_assignment_assignment_relaxed_value a b c lam) ''
          Set.Ici (0 : Fin m → ℝ)) :=
  rfl

/-- The reduced-profit objective of the `j`th knapsack subproblem after dualizing the assignment
constraints. -/
def generalized_assignment_column_reduced_profit {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (j : Fin n) (z : Fin m → Bool) : ℝ :=
  ∑ i, (c i j - lam i) * bool_entry (z i)

/-- The reduced-profit contribution of item `i` under the capacity-relaxed Lagrangian:
choosing `none` gives value `0`, while choosing `some j` gives `c_ij - μ_j a_i`. -/
def generalized_assignment_item_choice_value {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) :
    Option (Fin n) → ℝ
  | none => 0
  | some j => c i j - μ j * a i

/-- Leaving item `i` unassigned contributes `0` to the capacity-relaxed objective. -/
@[simp] theorem generalized_assignment_item_choice_value_none {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) :
    generalized_assignment_item_choice_value a c μ i none = 0 :=
  rfl

/-- Assigning item `i` to machine `j` contributes the reduced profit `c_ij - μ_j a_i`. -/
@[simp] theorem generalized_assignment_item_choice_value_some {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    generalized_assignment_item_choice_value a c μ i (.some j) = c i j - μ j * a i :=
  rfl

-- Semantic recall note: `Real.sSup_empty` makes a bare `ℝ`-valued knapsack-value owner collapse
-- to `0` on empty block families, so only the knapsack-decomposition statement below keeps the
-- standing nonnegative-capacity hypothesis explicit.

/-- Helper for Exercise 8.6: if `x` maximizes `f` on a finite set `s`, then `sSup (f '' s)` is
exactly `f x`. -/
lemma sSup_image_eq_of_set_max {α : Type*}
    (s : Set α) (f : α → ℝ) (hs : s.Finite) {x : α}
    (hx : x ∈ s) (hmax : ∀ y ∈ s, f y ≤ f x) :
    sSup (f '' s) = f x := by
  refine le_antisymm ?_ ?_
  · -- The maximizing witness bounds every point in the finite image set from above.
    refine csSup_le ?_ ?_
    · exact ⟨f x, ⟨x, hx, rfl⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hmax y hy
  · -- The maximizing witness itself belongs to the image set.
    exact le_csSup (hs.image f).bddAbove ⟨x, hx, rfl⟩

/-- Helper for Exercise 8.6: under nonnegative capacities, the all-zero pattern belongs to every
machine knapsack family. -/
lemma zeroPattern_mem_generalizedAssignmentBlockPatterns {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (hb_nonneg : ∀ j, 0 ≤ b j) (j : Fin n) :
    (fun _ ↦ false) ∈
      generalized_assignment_block_patterns (generalized_assignment_capacity_coeffs a) b j := by
  -- The zero pattern contributes zero load, so only the right-hand side remains.
  rw [mem_generalized_assignment_block_patterns_iff]
  simpa [generalized_assignment_capacity_coeffs, bool_entry_false] using hb_nonneg j

/-- Helper for Exercise 8.6: the assignment-relaxed objective equals the constant term `∑ i, λ_i`
plus the machine-wise reduced-profit contributions. -/
lemma assignmentRelaxedObjective_eq_constant_add_columns {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (x : Fin m → Fin n → Bool) :
    generalized_assignment_objective c x +
        ∑ i, lam i * (1 - ∑ j, bool_entry (x i j)) =
      (∑ i, lam i) +
        ∑ j, generalized_assignment_column_reduced_profit c lam j (fun i ↦ x i j) := by
  -- Normalize row by row, then commute the double sum to regroup the terms by machine.
  calc
    generalized_assignment_objective c x +
        ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))
      = ∑ i,
          (∑ j, c i j * bool_entry (x i j) + lam i * (1 - ∑ j, bool_entry (x i j))) := by
            simp [generalized_assignment_objective, Finset.sum_add_distrib]
    _ = ∑ i, (lam i + ∑ j, (c i j - lam i) * bool_entry (x i j)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            ∑ j, c i j * bool_entry (x i j) + lam i * (1 - ∑ j, bool_entry (x i j))
              = ∑ j, c i j * bool_entry (x i j) +
                  (lam i - ∑ j, lam i * bool_entry (x i j)) := by
                    rw [mul_sub, mul_one, Finset.mul_sum]
            _ = lam i +
                (∑ j, c i j * bool_entry (x i j) - ∑ j, lam i * bool_entry (x i j)) := by
                  ring
            _ = lam i + ∑ j, (c i j - lam i) * bool_entry (x i j) := by
                  rw [← Finset.sum_sub_distrib]
                  refine congrArg (fun t ↦ lam i + t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
    _ = (∑ i, lam i) + ∑ i, ∑ j, (c i j - lam i) * bool_entry (x i j) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i, lam i) + ∑ j, ∑ i, (c i j - lam i) * bool_entry (x i j) := by
          congr 1
          simpa using
            (Finset.sum_comm :
              (∑ i, ∑ j, (c i j - lam i) * bool_entry (x i j)) =
                ∑ j, ∑ i, (c i j - lam i) * bool_entry (x i j))
    _ = (∑ i, lam i) +
        ∑ j, generalized_assignment_column_reduced_profit c lam j (fun i ↦ x i j) := by
          rfl

/-- Helper for Exercise 8.6: the assignment-relaxed value is the constant term plus the sum of
the machine-wise knapsack suprema. -/
lemma assignmentRelaxedValue_eq_constant_add_knapsackSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ)
    (hb_nonneg : ∀ j, 0 ≤ b j) :
    generalized_assignment_assignment_relaxed_value a b c lam =
      (∑ i, lam i) +
        ∑ j,
          sSup
            ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
              generalized_assignment_block_patterns
                (generalized_assignment_capacity_coeffs a) b j) := by
  classical
  have hzStar :
      ∀ j, ∃ z ∈ generalized_assignment_block_patterns
          (generalized_assignment_capacity_coeffs a) b j,
        ∀ z' ∈ generalized_assignment_block_patterns
            (generalized_assignment_capacity_coeffs a) b j,
          generalized_assignment_column_reduced_profit c lam j z' ≤
            generalized_assignment_column_reduced_profit c lam j z := by
    intro j
    -- The zero pattern witnesses nonemptiness of each machine block, so a finite maximizer exists.
    exact Finset.exists_max_image _ _
      ⟨fun _ ↦ false,
        zeroPattern_mem_generalizedAssignmentBlockPatterns a b hb_nonneg j⟩
  choose zStar hzStar_mem hzStar_max using hzStar
  let xStar : Fin m → Fin n → Bool := fun i j ↦ zStar j i
  have hxStar : xStar ∈ generalized_assignment_capacity_base_set a b := by
    -- Each column of `xStar` is the maximizing pattern chosen for that machine.
    intro j
    simpa [xStar] using hzStar_mem j
  have hcolumnSup :
      ∀ j,
        sSup
            ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
              generalized_assignment_block_patterns
                (generalized_assignment_capacity_coeffs a) b j) =
          generalized_assignment_column_reduced_profit c lam j (zStar j) := by
    intro j
    exact sSup_image_eq_of_set_max
      _
      _
      (generalized_assignment_block_patterns
        (generalized_assignment_capacity_coeffs a) b j).finite_toSet
      (by simpa using hzStar_mem j)
      (by
        intro z hz
        exact hzStar_max j z (by simpa using hz))
  have hImageBdd :
      BddAbove
        ((fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
          generalized_assignment_capacity_base_set a b) := by
    let hs : (generalized_assignment_capacity_base_set a b).Finite := Set.toFinite _
    simpa [hs] using
      (hs.image
        (fun x : Fin m → Fin n → Bool ↦
          generalized_assignment_objective c x +
            ∑ i, lam i * (1 - ∑ j, bool_entry (x i j)))).bddAbove
  rw [generalized_assignment_assignment_relaxed_value_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- Every feasible pattern is bounded above by the sum of the machine-wise suprema.
    refine csSup_le ?_ ?_
    · exact ⟨_, ⟨xStar, hxStar, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxCols :
          ∀ j, (fun i ↦ x i j) ∈ generalized_assignment_block_patterns
            (generalized_assignment_capacity_coeffs a) b j := hx
      calc
        generalized_assignment_objective c x +
            ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))
          = (∑ i, lam i) +
              ∑ j, generalized_assignment_column_reduced_profit c lam j (fun i ↦ x i j) := by
                rw [assignmentRelaxedObjective_eq_constant_add_columns]
        _ ≤ (∑ i, lam i) +
              ∑ j,
                sSup
                  ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
                    generalized_assignment_block_patterns
                      (generalized_assignment_capacity_coeffs a) b j) := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left
                    (Finset.sum_le_sum fun j _ ↦
                      le_csSup
                        ((generalized_assignment_block_patterns
                          (generalized_assignment_capacity_coeffs a) b j).finite_toSet.image _).bddAbove
                        ⟨fun i ↦ x i j, hxCols j, rfl⟩)
                    (∑ i, lam i)
  · -- Insert the assembled maximizing-column pattern into the defining supremum.
    have hcandidate :
        generalized_assignment_objective c xStar +
            ∑ i, lam i * (1 - ∑ j, bool_entry (xStar i j)) =
          (∑ i, lam i) +
            ∑ j,
              sSup
                ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
                  generalized_assignment_block_patterns
                    (generalized_assignment_capacity_coeffs a) b j) := by
      calc
        generalized_assignment_objective c xStar +
            ∑ i, lam i * (1 - ∑ j, bool_entry (xStar i j))
          = (∑ i, lam i) +
              ∑ j, generalized_assignment_column_reduced_profit c lam j (zStar j) := by
                simpa [xStar] using
                  assignmentRelaxedObjective_eq_constant_add_columns c lam xStar
        _ = (∑ i, lam i) +
            ∑ j,
              sSup
                ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
                  generalized_assignment_block_patterns
                    (generalized_assignment_capacity_coeffs a) b j) := by
                refine congrArg (fun t ↦ (∑ i, lam i) + t) ?_
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [hcolumnSup j]
    rw [← hcandidate]
    exact le_csSup hImageBdd ⟨xStar, hxStar, rfl⟩

/-- Helper for Exercise 8.6: the capacity-relaxed objective equals the constant term
`∑ j, μ_j b_j` plus the item-wise reduced-profit contributions. -/
lemma capacityRelaxedObjective_eq_constant_add_rows {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ)
    (μ : Fin n → ℝ) (x : Fin m → Fin n → Bool) :
    generalized_assignment_objective c x +
        ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j)) =
      (∑ j, μ j * b j) +
        ∑ i, ∑ j, (c i j - μ j * a i) * bool_entry (x i j) := by
  -- Normalize by machine first, then commute the double sum to group the terms by item.
  calc
    generalized_assignment_objective c x +
        ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))
      = (∑ j, ∑ i, c i j * bool_entry (x i j)) +
          ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j)) := by
            rw [generalized_assignment_objective]
            simpa using
              congrArg
                (fun t ↦ t + ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j)))
                (Finset.sum_comm :
                  (∑ i, ∑ j, c i j * bool_entry (x i j)) =
                    ∑ j, ∑ i, c i j * bool_entry (x i j))
    _ = ∑ j,
          (∑ i, c i j * bool_entry (x i j) + μ j * (b j - ∑ i, a i * bool_entry (x i j))) := by
            rw [← Finset.sum_add_distrib]
    _ = ∑ j, (μ j * b j + ∑ i, (c i j - μ j * a i) * bool_entry (x i j)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            ∑ i, c i j * bool_entry (x i j) + μ j * (b j - ∑ i, a i * bool_entry (x i j))
              = ∑ i, c i j * bool_entry (x i j) +
                  (μ j * b j - ∑ i, μ j * (a i * bool_entry (x i j))) := by
                    rw [mul_sub, Finset.mul_sum]
            _ = μ j * b j +
                (∑ i, c i j * bool_entry (x i j) - ∑ i, μ j * (a i * bool_entry (x i j))) := by
                  ring
            _ = μ j * b j + ∑ i, (c i j - μ j * a i) * bool_entry (x i j) := by
                  rw [← Finset.sum_sub_distrib]
                  refine congrArg (fun t ↦ μ j * b j + t) ?_
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  ring
    _ = (∑ j, μ j * b j) + ∑ j, ∑ i, (c i j - μ j * a i) * bool_entry (x i j) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j, μ j * b j) + ∑ i, ∑ j, (c i j - μ j * a i) * bool_entry (x i j) := by
          congr 1
          simpa using
            (Finset.sum_comm :
              (∑ j, ∑ i, (c i j - μ j * a i) * bool_entry (x i j)) =
                ∑ i, ∑ j, (c i j - μ j * a i) * bool_entry (x i j))

/-- Helper for Exercise 8.6: an at-most-one Boolean row is exactly the indicator of one
optional machine choice. -/
lemma rowAtMostOne_eq_optionIndicator {n : ℕ}
    (r : Fin n → Bool) (hr : ∑ j, bool_entry (r j) ≤ 1) :
    ∃ o : Option (Fin n), ∀ j, bool_entry (r j) = bool_entry (decide (o = some j)) := by
  classical
  by_cases hnone : ∀ j, r j = false
  · -- If no machine is chosen, the row is the indicator of `none`.
    refine ⟨none, ?_⟩
    intro j
    simp [hnone j]
  · -- Otherwise the unique active machine is the `some` witness.
    have hsome : ∃ j, r j = true := by
      rcases not_forall.mp hnone with ⟨j, hj⟩
      cases hrj : r j
      · simp [hrj] at hj
      · exact ⟨j, hrj⟩
    rcases hsome with ⟨j, hj⟩
    let lam : Fin n → ℝ := fun k ↦ bool_entry (r k)
    have h01 : ∀ k, lam k = 0 ∨ lam k = 1 := by
      intro k
      exact bool_entry_eq_zero_or_one (r k)
    have hsum_eq_one : ∑ k, lam k = 1 := by
      have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ lam k := by
        intro k hk
        exact bool_entry_nonneg (r k)
      have hj_le : lam j ≤ ∑ k, lam k := by
        exact Finset.single_le_sum hnonneg (by simp)
      have hj_one : lam j = 1 := by
        simp [lam, hj]
      linarith
    rcases existsUnique_eq_one_of_binary_master_weights ⟨hsum_eq_one, h01⟩ with
      ⟨jStar, hjStar, hjStar_unique⟩
    refine ⟨some jStar, ?_⟩
    intro k
    by_cases hk : k = jStar
    · -- At the active index, both sides are `1`.
      subst hk
      simp [lam] at hjStar
      simp [hjStar]
    · -- Away from the active index, the row must vanish because another `1` is impossible.
      have hk_zero : lam k = 0 := by
        rcases h01 k with hk0 | hk1
        · exact hk0
        · exfalso
          exact hk (hjStar_unique k hk1)
      calc
        bool_entry (r k) = 0 := by
          simpa [lam] using hk_zero
        _ = bool_entry (decide ((some jStar : Option (Fin n)) = some k)) := by
          have hne : jStar ≠ k := by
            exact fun h ↦ hk h.symm
          simp [hne]

/-- Helper for Exercise 8.6: rewriting an at-most-one row in `Option (Fin n)` normal form
turns its reduced-profit sum into the canonical single-choice value. -/
lemma rowContribution_eq_itemChoiceValue_of_optionIndicator {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ)
    (i : Fin m) (r : Fin n → Bool) (o : Option (Fin n))
    (hr : ∀ j, bool_entry (r j) = bool_entry (decide (o = some j))) :
    ∑ j, (c i j - μ j * a i) * bool_entry (r j) =
      generalized_assignment_item_choice_value a c μ i o := by
  -- Rewrite the row to the canonical indicator and then simplify the resulting sum.
  cases o with
  | none =>
      calc
        ∑ j, (c i j - μ j * a i) * bool_entry (r j)
          = ∑ j, (c i j - μ j * a i) * bool_entry (decide (none = some j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hr j]
        _ = generalized_assignment_item_choice_value a c μ i none := by
              simp
  | some j0 =>
      calc
        ∑ j, (c i j - μ j * a i) * bool_entry (r j)
          = ∑ j, (c i j - μ j * a i) * bool_entry (decide ((some j0) = some j)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hr j]
        _ = c i j0 - μ j0 * a i := by
              rw [Finset.sum_eq_single j0]
              · simp
              · intro j hj hj_ne
                have hne : j0 ≠ j := by
                  exact fun h ↦ hj_ne h.symm
                simp [hne]
              · intro hj_mem
                exact False.elim (hj_mem (by simp))
        _ = generalized_assignment_item_choice_value a c μ i (.some j0) := by
              simp

/-- Helper for Exercise 8.6: a Boolean row satisfying `∑ j, x_j ≤ 1` contributes at most the
best single-choice value among `none` and the machine choices `some j`. -/
lemma rowContribution_le_itemChoiceSup {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ)
    (i : Fin m) (r : Fin n → Bool) (hr : ∑ j, bool_entry (r j) ≤ 1) :
    ∑ j, (c i j - μ j * a i) * bool_entry (r j) ≤
      sSup ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
        Set.univ) :=
  by
  -- Normalize the row to the canonical `Option` indicator and insert that witness into the
  -- finite single-choice image set.
  classical
  obtain ⟨o, ho⟩ := rowAtMostOne_eq_optionIndicator r hr
  let hs : (Set.univ : Set (Option (Fin n))).Finite := Set.toFinite _
  calc
    ∑ j, (c i j - μ j * a i) * bool_entry (r j)
      = generalized_assignment_item_choice_value a c μ i o := by
          exact rowContribution_eq_itemChoiceValue_of_optionIndicator a c μ i r o ho
    _ ≤
        sSup ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
          Set.univ) := by
            exact le_csSup (hs.image _).bddAbove ⟨o, by simp, rfl⟩

/-- Helper for Exercise 8.6: the capacity-relaxed value is the constant term plus the sum of the
item-wise single-choice suprema. -/
lemma capacityRelaxedValue_eq_constant_add_singleChoiceSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_value a b c μ =
      (∑ j, μ j * b j) +
        ∑ i,
          sSup
            ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
              Set.univ) :=
  by
  classical
  let itemChoice : Fin m → Option (Fin n) → ℝ :=
    fun i o ↦ generalized_assignment_item_choice_value a c μ i o
  have hoStar :
      ∀ i, ∃ o : Option (Fin n), ∀ o' : Option (Fin n), itemChoice i o' ≤ itemChoice i o := by
    intro i
    let s : Finset (Option (Fin n)) := Finset.univ
    have hs_nonempty : s.Nonempty := ⟨none, by simp [s]⟩
    obtain ⟨o, ho_mem, hmax⟩ := s.exists_max_image (itemChoice i) hs_nonempty
    refine ⟨o, ?_⟩
    intro o'
    exact hmax o' (by simp [s])
  choose oStar hoStar_max using hoStar
  let xStar : Fin m → Fin n → Bool := fun i j ↦ decide (oStar i = some j)
  have hxStar : xStar ∈ generalized_assignment_assignment_base_set := by
    -- Each row of `xStar` is an `Option` indicator, so its Boolean mass is `0` or `1`.
    intro i
    cases ho : oStar i with
    | none =>
        simp [xStar, ho]
    | some j0 =>
        have hrow_sum : ∑ j, bool_entry (decide (j0 = j)) = 1 := by
          rw [Finset.sum_eq_single j0]
          · simp
          · intro j hj hj_ne
            have hne : j0 ≠ j := by
              exact fun h ↦ hj_ne h.symm
            simp [hne]
          · intro hj_mem
            exact False.elim (hj_mem (by simp))
        simpa [xStar, ho, hrow_sum]
  have hitemSup :
      ∀ i,
        sSup ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
          Set.univ) =
          generalized_assignment_item_choice_value a c μ i (oStar i) := by
    intro i
    exact sSup_image_eq_of_set_max
      Set.univ
      (fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o)
      (Set.toFinite _)
      (by simp)
      (by
        intro o ho
        exact hoStar_max i o)
  have hImageBdd :
      BddAbove
        ((fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))) ''
          generalized_assignment_assignment_base_set) := by
    let hs : (generalized_assignment_assignment_base_set : Set (Fin m → Fin n → Bool)).Finite :=
      Set.toFinite _
    simpa [hs] using
      (hs.image
        (fun x : Fin m → Fin n → Bool ↦
          generalized_assignment_objective c x +
            ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j)))).bddAbove
  rw [generalized_assignment_capacity_relaxed_value_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- Any feasible assignment row is dominated by the best single-choice value for that item.
    refine csSup_le ?_ ?_
    · exact ⟨_, ⟨xStar, hxStar, rfl⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      calc
        generalized_assignment_objective c x +
            ∑ j, μ j * (b j - ∑ i, a i * bool_entry (x i j))
          = (∑ j, μ j * b j) +
              ∑ i, ∑ j, (c i j - μ j * a i) * bool_entry (x i j) := by
                rw [capacityRelaxedObjective_eq_constant_add_rows]
        _ ≤ (∑ j, μ j * b j) +
              ∑ i,
                sSup
                  ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
                    Set.univ) := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left
                    (Finset.sum_le_sum fun i hi ↦
                      rowContribution_le_itemChoiceSup a c μ i (fun j ↦ x i j) (hx i))
                    (∑ j, μ j * b j)
  · -- The assembled maximizing assignment attains the sum of the row-wise suprema.
    have hcandidate :
        generalized_assignment_objective c xStar +
            ∑ j, μ j * (b j - ∑ i, a i * bool_entry (xStar i j)) =
          (∑ j, μ j * b j) +
            ∑ i,
              sSup
                ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
                  Set.univ) := by
      calc
        generalized_assignment_objective c xStar +
            ∑ j, μ j * (b j - ∑ i, a i * bool_entry (xStar i j))
          = (∑ j, μ j * b j) +
              ∑ i, ∑ j, (c i j - μ j * a i) * bool_entry (xStar i j) := by
                rw [capacityRelaxedObjective_eq_constant_add_rows]
        _ = (∑ j, μ j * b j) +
              ∑ i, generalized_assignment_item_choice_value a c μ i (oStar i) := by
                refine congrArg (fun t ↦ (∑ j, μ j * b j) + t) ?_
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact
                  rowContribution_eq_itemChoiceValue_of_optionIndicator
                    a c μ i (fun j ↦ xStar i j) (oStar i) (fun j ↦ rfl)
        _ = (∑ j, μ j * b j) +
              ∑ i,
                sSup
                  ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
                    Set.univ) := by
                refine congrArg (fun t ↦ (∑ j, μ j * b j) + t) ?_
                refine Finset.sum_congr rfl ?_
                intro i hi
                symm
                exact hitemSup i
    rw [← hcandidate]
    exact le_csSup hImageBdd ⟨xStar, hxStar, rfl⟩

/-- Helper for Exercise 8.6: the item-wise single-choice supremum is nonnegative because the
`none` choice always contributes `0`. -/
lemma itemChoiceSup_nonneg {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) (i : Fin m) :
    0 ≤
      sSup
        ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
          Set.univ) := by
  let hs : (Set.univ : Set (Option (Fin n))).Finite := Set.toFinite _
  -- Insert the `none` choice into the finite image set to get the lower bound `0 ≤ sup`.
  simpa using
    (le_csSup (hs.image _).bddAbove
      ⟨none, by simp, generalized_assignment_item_choice_value_none a c μ i⟩ :
      generalized_assignment_item_choice_value a c μ i none ≤
        sSup
          ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
            Set.univ))

/-- Helper for Exercise 8.6: if the capacity base set is nonempty, then choosing for each item
`i` the single-choice supremum as multiplier `λ_i` bounds the assignment-relaxed value by the
capacity-relaxed value computed with the same `μ`. -/
lemma assignmentRelaxedValue_le_capacityRelaxedValue_of_nonempty {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ)
    (hμ : 0 ≤ μ)
    (hbase : (generalized_assignment_capacity_base_set a b).Nonempty) :
    generalized_assignment_assignment_relaxed_value a b c
        (fun i ↦
          sSup
            ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
              Set.univ)) ≤
      generalized_assignment_capacity_relaxed_value a b c μ := by
  classical
  let lam : Fin m → ℝ := fun i ↦
    sSup
      ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
        Set.univ)
  rcases hbase with ⟨x₀, hx₀⟩
  rw [generalized_assignment_assignment_relaxed_value_eq_sSup]
  refine csSup_le ?_ ?_
  · -- The nonempty capacity base set gives a witness in the assignment-relaxed image set.
    exact ⟨_, ⟨x₀, hx₀, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hlam_nonneg : ∀ i, 0 ≤ lam i := by
      intro i
      exact itemChoiceSup_nonneg a c μ i
    have hchoice_ge :
        ∀ i j, c i j - μ j * a i ≤ lam i := by
      intro i j
      let hs : (Set.univ : Set (Option (Fin n))).Finite := Set.toFinite _
      -- Each concrete machine choice `some j` is one candidate in the defining supremum.
      exact
        le_csSup (hs.image _).bddAbove
          ⟨some j, by simp, generalized_assignment_item_choice_value_some a c μ i j⟩
    have hcolumnBound :
        ∀ j,
          generalized_assignment_column_reduced_profit c lam j (fun i ↦ x i j) ≤ μ j * b j := by
      intro j
      calc
        generalized_assignment_column_reduced_profit c lam j (fun i ↦ x i j)
          = ∑ i, (c i j - lam i) * bool_entry (x i j) := by
              simp [generalized_assignment_column_reduced_profit]
        _ ≤ ∑ i, (μ j * a i) * bool_entry (x i j) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hij : c i j - lam i ≤ μ j * a i := by
                linarith [hchoice_ge i j]
              exact mul_le_mul_of_nonneg_right hij (bool_entry_nonneg (x i j))
        _ = μ j * ∑ i, a i * bool_entry (x i j) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ ≤ μ j * b j := by
              have hμj : 0 ≤ μ j := hμ j
              exact mul_le_mul_of_nonneg_left
                ((mem_generalized_assignment_capacity_base_set_iff.mp hx) j) hμj
    -- Compare the assignment-relaxed objective to the sum of the column-wise capacity penalties.
    calc
      generalized_assignment_objective c x +
          ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))
        = (∑ i, lam i) +
            ∑ j, generalized_assignment_column_reduced_profit c lam j (fun i ↦ x i j) := by
              rw [assignmentRelaxedObjective_eq_constant_add_columns]
      _ ≤ (∑ i, lam i) + ∑ j, μ j * b j := by
            gcongr with j
            exact hcolumnBound j
      _ = generalized_assignment_capacity_relaxed_value a b c μ := by
            rw [capacityRelaxedValue_eq_constant_add_singleChoiceSup]
            simp [lam, add_comm]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened LP rows are
capacity rows, assignment rows, and nonnegativity rows. -/
private abbrev generalizedAssignmentFlatRow (m n : ℕ) :=
  Fin n ⊕ (Fin m ⊕ (Fin m × Fin n))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the semantic row blocks are
reindexed by the `Fin` owner required by the Chapter 3 LP API. -/
private abbrev generalizedAssignmentFlatRowEquiv (m n : ℕ) :
    generalizedAssignmentFlatRow m n ≃ Fin (n + (m + m * n)) :=
  (Equiv.sumCongr (Equiv.refl _)
      ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans
    finSumFinEquiv

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the raw flattened constraint
matrix encodes capacities, assignment row sums, and coordinate nonnegativity. -/
private def generalizedAssignmentFlatMatrixRaw {m n : ℕ}
    (a : Fin m → ℝ) : Matrix (generalizedAssignmentFlatRow m n) (Fin m × Fin n) ℝ :=
  fun row ij ↦
    match row with
    | Sum.inl j => if j = ij.2 then a ij.1 else 0
    | Sum.inr (Sum.inl i) => if i = ij.1 then 1 else 0
    | Sum.inr (Sum.inr kl) => if kl = ij then -1 else 0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the raw flattened right-hand
side is `(b, 1, 0)` on the three row blocks. -/
private def generalizedAssignmentFlatRhsRaw {m n : ℕ}
    (b : Fin n → ℝ) : generalizedAssignmentFlatRow m n → ℝ :=
  fun row ↦
    match row with
    | Sum.inl j => b j
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened constraint
matrix on explicit `Fin` row and column owners. -/
private def generalizedAssignmentFlatMatrix {m n : ℕ}
    (a : Fin m → ℝ) : Matrix (Fin (n + (m + m * n))) (Fin (m * n)) ℝ :=
  (generalizedAssignmentFlatMatrixRaw a).submatrix
    (generalizedAssignmentFlatRowEquiv m n).symm finProdFinEquiv.symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened right-hand side
on its explicit `Fin` row owner. -/
private def generalizedAssignmentFlatRhs {m n : ℕ}
    (b : Fin n → ℝ) : Fin (n + (m + m * n)) → ℝ :=
  generalizedAssignmentFlatRhsRaw b ∘ (generalizedAssignmentFlatRowEquiv m n).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened objective reads
the original coefficient at the corresponding item-machine pair. -/
private def generalizedAssignmentFlatObjective {m n : ℕ}
    (c : Fin m → Fin n → ℝ) : Fin (m * n) → ℝ :=
  fun k ↦ c (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: unflattening restores the
two-index assignment variable. -/
private def generalizedAssignmentUnflatten {m n : ℕ}
    (x : Fin (m * n) → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ x (finProdFinEquiv (i, j))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: flattening packages a
two-index assignment vector into the Chapter 3 LP column owner. -/
private def generalizedAssignmentFlatten {m n : ℕ}
    (x : Fin m → Fin n → ℝ) : Fin (m * n) → ℝ :=
  fun k ↦ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: unflattening a flattened
two-index vector recovers the original vector. -/
private lemma generalizedAssignmentUnflatten_flatten {m n : ℕ}
    (x : Fin m → Fin n → ℝ) :
    generalizedAssignmentUnflatten (generalizedAssignmentFlatten x) = x := by
  -- Evaluate at a pair and cancel the product equivalence.
  funext i j
  simp [generalizedAssignmentUnflatten, generalizedAssignmentFlatten]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: flattening an unflattened
Chapter 3 vector recovers that vector. -/
private lemma generalizedAssignmentFlatten_unflatten {m n : ℕ}
    (x : Fin (m * n) → ℝ) :
    generalizedAssignmentFlatten (generalizedAssignmentUnflatten x) = x := by
  -- Evaluate at a flat index and cancel the product equivalence.
  funext k
  simpa [generalizedAssignmentUnflatten, generalizedAssignmentFlatten] using
    congrArg x (finProdFinEquiv.apply_symm_apply k)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: a capacity row of the
flattened system evaluates to its machine load. -/
private lemma generalizedAssignmentFlatMatrix_mulVec_capacity {m n : ℕ}
    (a : Fin m → ℝ) (x : Fin (m * n) → ℝ) (j : Fin n) :
    Matrix.mulVec (generalizedAssignmentFlatMatrix a) x
        (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) =
      ∑ i, a i * generalizedAssignmentUnflatten x i j := by
  let Araw : Matrix (generalizedAssignmentFlatRow m n) (Fin m × Fin n) ℝ :=
    generalizedAssignmentFlatMatrixRaw a
  have hmul := Matrix.submatrix_mulVec_equiv Araw x
    (generalizedAssignmentFlatRowEquiv m n).symm finProdFinEquiv.symm
  calc
    Matrix.mulVec (generalizedAssignmentFlatMatrix a) x
        (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) =
        Matrix.mulVec Araw (x ∘ finProdFinEquiv) (Sum.inl j) := by
          simpa [generalizedAssignmentFlatMatrix, Araw] using
            congrFun hmul (generalizedAssignmentFlatRowEquiv m n (Sum.inl j))
    _ = ∑ i, a i * generalizedAssignmentUnflatten x i j := by
      -- Split the product-indexed sum and collapse the selector in the machine coordinate.
      simp [Araw, generalizedAssignmentFlatMatrixRaw, generalizedAssignmentUnflatten,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: an assignment row of the
flattened system evaluates to its item row sum. -/
private lemma generalizedAssignmentFlatMatrix_mulVec_assignment {m n : ℕ}
    (a : Fin m → ℝ) (x : Fin (m * n) → ℝ) (i : Fin m) :
    Matrix.mulVec (generalizedAssignmentFlatMatrix a) x
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) =
      ∑ j, generalizedAssignmentUnflatten x i j := by
  let Araw : Matrix (generalizedAssignmentFlatRow m n) (Fin m × Fin n) ℝ :=
    generalizedAssignmentFlatMatrixRaw a
  have hmul := Matrix.submatrix_mulVec_equiv Araw x
    (generalizedAssignmentFlatRowEquiv m n).symm finProdFinEquiv.symm
  calc
    Matrix.mulVec (generalizedAssignmentFlatMatrix a) x
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) =
        Matrix.mulVec Araw (x ∘ finProdFinEquiv) (Sum.inr (Sum.inl i)) := by
          simpa [generalizedAssignmentFlatMatrix, Araw] using
            congrFun hmul (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i)))
    _ = ∑ j, generalizedAssignmentUnflatten x i j := by
      -- Only columns whose item coordinate is `i` survive this selector row.
      rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i]
      · simp [Araw, generalizedAssignmentFlatMatrixRaw, generalizedAssignmentUnflatten]
      · intro k hk hki
        have hik : i ≠ k := Ne.symm hki
        simp [Araw, generalizedAssignmentFlatMatrixRaw, hik]
      · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: a nonnegativity row of the
flattened system evaluates to the negative of its selected coordinate. -/
private lemma generalizedAssignmentFlatMatrix_mulVec_nonneg {m n : ℕ}
    (a : Fin m → ℝ) (x : Fin (m * n) → ℝ) (i : Fin m) (j : Fin n) :
    Matrix.mulVec (generalizedAssignmentFlatMatrix a) x
        (generalizedAssignmentFlatRowEquiv m n
          (Sum.inr (Sum.inr (i, j)))) =
      -generalizedAssignmentUnflatten x i j := by
  let Araw : Matrix (generalizedAssignmentFlatRow m n) (Fin m × Fin n) ℝ :=
    generalizedAssignmentFlatMatrixRaw a
  have hmul := Matrix.submatrix_mulVec_equiv Araw x
    (generalizedAssignmentFlatRowEquiv m n).symm finProdFinEquiv.symm
  calc
    Matrix.mulVec (generalizedAssignmentFlatMatrix a) x
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j)))) =
        Matrix.mulVec Araw (x ∘ finProdFinEquiv) (Sum.inr (Sum.inr (i, j))) := by
          simpa [generalizedAssignmentFlatMatrix, Araw] using
            congrFun hmul
              (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j))))
    _ = -generalizedAssignmentUnflatten x i j := by
      -- The negative identity block selects exactly the coordinate `(i,j)`.
      simp [Araw, generalizedAssignmentFlatMatrixRaw, generalizedAssignmentUnflatten,
        Matrix.mulVec, dotProduct]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened right-hand
side at a capacity row is the corresponding capacity. -/
private lemma generalizedAssignmentFlatRhs_capacity {m n : ℕ}
    (b : Fin n → ℝ) (j : Fin n) :
    generalizedAssignmentFlatRhs b
        (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) = b j := by
  -- Cancel the row equivalence and expose the capacity block.
  simp [generalizedAssignmentFlatRhs, generalizedAssignmentFlatRhsRaw]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened right-hand
side at an assignment row is one. -/
private lemma generalizedAssignmentFlatRhs_assignment {m n : ℕ}
    (b : Fin n → ℝ) (i : Fin m) :
    generalizedAssignmentFlatRhs b
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) = 1 := by
  -- Cancel the row equivalence and expose the assignment block.
  simp [generalizedAssignmentFlatRhs, generalizedAssignmentFlatRhsRaw]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened right-hand
side at a nonnegativity row is zero. -/
private lemma generalizedAssignmentFlatRhs_nonneg {m n : ℕ}
    (b : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    generalizedAssignmentFlatRhs b
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j)))) = 0 := by
  -- Cancel the row equivalence and expose the homogeneous block.
  simp [generalizedAssignmentFlatRhs, generalizedAssignmentFlatRhsRaw]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened dot product is
the original double-sum objective. -/
private lemma generalizedAssignmentFlatObjective_dotProduct {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (x : Fin (m * n) → ℝ) :
    generalizedAssignmentFlatObjective c ⬝ᵥ x =
      ∑ i, ∑ j, c i j * generalizedAssignmentUnflatten x i j := by
  rw [dotProduct]
  calc
    ∑ k : Fin (m * n), generalizedAssignmentFlatObjective c k * x k =
        ∑ ij : Fin m × Fin n,
          generalizedAssignmentFlatObjective c (finProdFinEquiv ij) *
            x (finProdFinEquiv ij) := by
              symm
              exact Fintype.sum_equiv finProdFinEquiv _ _ fun _ ↦ rfl
    _ = ∑ i, ∑ j, c i j * generalizedAssignmentUnflatten x i j := by
      -- Reindex by item-machine pairs and cancel the flattening equivalence.
      rw [Fintype.sum_prod_type]
      simp [generalizedAssignmentFlatObjective, generalizedAssignmentUnflatten]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: flattened primal
feasibility is exactly generalized-assignment LP feasibility after unflattening. -/
private lemma mem_generalizedAssignmentFlatPrimal_iff {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (x : Fin (m * n) → ℝ) :
    x ∈ primal_feasible_region
        (generalizedAssignmentFlatMatrix a) (generalizedAssignmentFlatRhs b) ↔
      generalized_assignment_lp_feasible
        (generalized_assignment_capacity_coeffs a) b
        (generalizedAssignmentUnflatten x) := by
  rw [mem_primal_feasible_region_iff, generalized_assignment_lp_feasible_iff]
  constructor
  · intro hx
    have hnonneg : ∀ i j, 0 ≤ generalizedAssignmentUnflatten x i j := by
      intro i j
      have hrow := hx
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j))))
      rw [generalizedAssignmentFlatMatrix_mulVec_nonneg,
        generalizedAssignmentFlatRhs_nonneg] at hrow
      linarith
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      refine ⟨hnonneg i j, ?_⟩
      have hsingle :
          generalizedAssignmentUnflatten x i j ≤
            ∑ k, generalizedAssignmentUnflatten x i k := by
        exact Finset.single_le_sum (fun k _ ↦ hnonneg i k) (Finset.mem_univ j)
      have hrow := hx
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i)))
      rw [generalizedAssignmentFlatMatrix_mulVec_assignment,
        generalizedAssignmentFlatRhs_assignment] at hrow
      exact hsingle.trans hrow
    · intro j
      have hrow := hx (generalizedAssignmentFlatRowEquiv m n (Sum.inl j))
      rw [generalizedAssignmentFlatMatrix_mulVec_capacity,
        generalizedAssignmentFlatRhs_capacity] at hrow
      simpa [generalized_assignment_capacity_coeffs] using hrow
    · intro i
      have hrow := hx
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i)))
      rwa [generalizedAssignmentFlatMatrix_mulVec_assignment,
        generalizedAssignmentFlatRhs_assignment] at hrow
  · rintro ⟨hbox, hcapacity, hassignment⟩ row
    cases hsplit : (generalizedAssignmentFlatRowEquiv m n).symm row with
    | inl j =>
        have hrow : row = generalizedAssignmentFlatRowEquiv m n (Sum.inl j) := by
          simpa [hsplit] using
            (generalizedAssignmentFlatRowEquiv m n).apply_symm_apply row |>.symm
        rw [hrow, generalizedAssignmentFlatMatrix_mulVec_capacity,
          generalizedAssignmentFlatRhs_capacity]
        simpa [generalized_assignment_capacity_coeffs] using hcapacity j
    | inr rest =>
        cases rest with
        | inl i =>
            have hrow :
                row = generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i)) := by
              simpa [hsplit] using
                (generalizedAssignmentFlatRowEquiv m n).apply_symm_apply row |>.symm
            rw [hrow, generalizedAssignmentFlatMatrix_mulVec_assignment,
              generalizedAssignmentFlatRhs_assignment]
            exact hassignment i
        | inr ij =>
            rcases ij with ⟨i, j⟩
            have hrow :
                row = generalizedAssignmentFlatRowEquiv m n
                  (Sum.inr (Sum.inr (i, j))) := by
              simpa [hsplit] using
                (generalizedAssignmentFlatRowEquiv m n).apply_symm_apply row |>.symm
            rw [hrow, generalizedAssignmentFlatMatrix_mulVec_nonneg,
              generalizedAssignmentFlatRhs_nonneg]
            linarith [hbox i j |>.1]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the source LP value is the
supremum of objective values of the flattened Chapter 3 primal. -/
private lemma generalizedAssignmentLpValue_eq_flatPrimalSup {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_lp_value a b c =
      sSup (primal_objective_values
        (generalizedAssignmentFlatMatrix a)
        (generalizedAssignmentFlatRhs b)
        (generalizedAssignmentFlatObjective c)) := by
  have hvalues :
      primal_objective_values
          (generalizedAssignmentFlatMatrix a)
          (generalizedAssignmentFlatRhs b)
          (generalizedAssignmentFlatObjective c) =
        (fun x : Fin m → Fin n → ℝ ↦ ∑ i, ∑ j, c i j * x i j) ''
          {x |
            generalized_assignment_lp_feasible
              (generalized_assignment_capacity_coeffs a) b x} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨generalizedAssignmentUnflatten x,
        (mem_generalizedAssignmentFlatPrimal_iff a b x).mp hx, ?_⟩
      -- The objective component lemma identifies the two displayed values.
      exact (generalizedAssignmentFlatObjective_dotProduct c x).symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨generalizedAssignmentFlatten x, ?_, ?_⟩
      · rw [mem_generalizedAssignmentFlatPrimal_iff,
          generalizedAssignmentUnflatten_flatten]
        exact hx
      · calc
          (fun y ↦ generalizedAssignmentFlatObjective c ⬝ᵥ y)
                (generalizedAssignmentFlatten x) =
              generalizedAssignmentFlatObjective c ⬝ᵥ generalizedAssignmentFlatten x := rfl
          _ = ∑ i, ∑ j, c i j *
                generalizedAssignmentUnflatten (generalizedAssignmentFlatten x) i j :=
            generalizedAssignmentFlatObjective_dotProduct c (generalizedAssignmentFlatten x)
          _ = (fun y : Fin m → Fin n → ℝ ↦ ∑ i, ∑ j, c i j * y i j) x := by
            rw [generalizedAssignmentUnflatten_flatten]
  -- Rewrite the two value owners through the proved equality of objective-value sets.
  rw [generalized_assignment_lp_value, hvalues]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: evaluating the flattened
dual row equation at `(i,j)` gives its capacity, assignment, and slack components. -/
private lemma generalizedAssignmentFlatMatrix_vecMul_component {m n : ℕ}
    (a : Fin m → ℝ) (u : Fin (n + (m + m * n)) → ℝ) (i : Fin m) (j : Fin n) :
    Matrix.vecMul u (generalizedAssignmentFlatMatrix a) (finProdFinEquiv (i, j)) =
      u (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) * a i +
        u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) -
          u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j)))) := by
  let Araw : Matrix (generalizedAssignmentFlatRow m n) (Fin m × Fin n) ℝ :=
    generalizedAssignmentFlatMatrixRaw a
  have hvec := Matrix.submatrix_vecMul_equiv Araw u
    (generalizedAssignmentFlatRowEquiv m n).symm finProdFinEquiv.symm
  have hcomponent :
      Matrix.vecMul u (generalizedAssignmentFlatMatrix a) (finProdFinEquiv (i, j)) =
        Matrix.vecMul (u ∘ generalizedAssignmentFlatRowEquiv m n) Araw (i, j) := by
    simpa [generalizedAssignmentFlatMatrix, Araw] using
      congrFun hvec (finProdFinEquiv (i, j))
  rw [hcomponent, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  -- Each of the three selector blocks contributes its named coordinate.
  simp [Araw, generalizedAssignmentFlatMatrixRaw]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: a vector is feasible for
the flattened dual exactly when its semantic coordinates are nonnegative and obey the reduced
cost equations. -/
private lemma mem_generalizedAssignmentFlatDual_iff {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ)
    (u : Fin (n + (m + m * n)) → ℝ) :
    u ∈ dual_feasible_region
        (generalizedAssignmentFlatMatrix a) (generalizedAssignmentFlatObjective c) ↔
      (∀ row, 0 ≤ u row) ∧
        ∀ i j,
          u (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) * a i +
              u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) -
                u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j)))) =
            c i j := by
  rw [mem_dual_feasible_region_iff]
  constructor
  · rintro ⟨heq, hnonneg⟩
    refine ⟨hnonneg, ?_⟩
    intro i j
    have hcomponent := congrFun heq (finProdFinEquiv (i, j))
    rw [generalizedAssignmentFlatMatrix_vecMul_component] at hcomponent
    simpa [generalizedAssignmentFlatObjective] using hcomponent
  · rintro ⟨hnonneg, heq⟩
    refine ⟨?_, hnonneg⟩
    ext k
    let ij : Fin m × Fin n := finProdFinEquiv.symm k
    have hk : finProdFinEquiv ij = k := finProdFinEquiv.apply_symm_apply k
    rw [← hk, generalizedAssignmentFlatMatrix_vecMul_component]
    simpa [ij, generalizedAssignmentFlatObjective] using heq ij.1 ij.2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the flattened dual
objective is the capacity contribution plus the assignment contribution; slack rows vanish. -/
private lemma generalizedAssignmentFlatDualObjective_eq {m n : ℕ}
    (b : Fin n → ℝ) (u : Fin (n + (m + m * n)) → ℝ) :
    u ⬝ᵥ generalizedAssignmentFlatRhs b =
      (∑ j, u (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) * b j) +
        ∑ i, u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) := by
  rw [dotProduct]
  calc
    ∑ row : Fin (n + (m + m * n)), u row * generalizedAssignmentFlatRhs b row =
        ∑ row : generalizedAssignmentFlatRow m n,
          u (generalizedAssignmentFlatRowEquiv m n row) *
            generalizedAssignmentFlatRhs b (generalizedAssignmentFlatRowEquiv m n row) := by
              symm
              exact Fintype.sum_equiv (generalizedAssignmentFlatRowEquiv m n) _ _
                fun _ ↦ rfl
    _ = (∑ j, u (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) * b j) +
        ∑ i, u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) := by
      -- Split the three semantic row blocks; the homogeneous slack block contributes zero.
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [generalizedAssignmentFlatRhs, generalizedAssignmentFlatRhsRaw]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: every concrete machine
choice is bounded by the corresponding finite single-choice supremum. -/
private lemma itemChoiceValue_some_le_sup {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (mu : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    c i j - mu j * a i ≤
      sSup
        ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c mu i o) ''
          Set.univ) := by
  let hs : (Set.univ : Set (Option (Fin n))).Finite := Set.toFinite _
  -- Insert `some j` into the finite image that defines the item multiplier.
  exact le_csSup (hs.image _).bddAbove
    ⟨some j, Set.mem_univ _, generalized_assignment_item_choice_value_some a c mu i j⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the canonical flattened
dual lift stores capacity multipliers, item-choice suprema, and their nonnegative slacks. -/
private def generalizedAssignmentFlatDualLift {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (mu : Fin n → ℝ) :
    Fin (n + (m + m * n)) → ℝ :=
  fun row ↦
    match (generalizedAssignmentFlatRowEquiv m n).symm row with
    | Sum.inl j => mu j
    | Sum.inr (Sum.inl i) =>
        sSup
          ((fun o : Option (Fin n) ↦
              generalized_assignment_item_choice_value a c mu i o) '' Set.univ)
    | Sum.inr (Sum.inr (i, j)) =>
        sSup
            ((fun o : Option (Fin n) ↦
                generalized_assignment_item_choice_value a c mu i o) '' Set.univ) +
          mu j * a i - c i j

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the capacity coordinates
of the canonical flattened dual lift are the original multipliers. -/
private lemma generalizedAssignmentFlatDualLift_capacity {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (mu : Fin n → ℝ) (j : Fin n) :
    generalizedAssignmentFlatDualLift a c mu
        (generalizedAssignmentFlatRowEquiv m n (Sum.inl j)) = mu j := by
  -- Cancel the row equivalence and expose the capacity branch.
  simp [generalizedAssignmentFlatDualLift]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the assignment coordinates
of the canonical flattened dual lift are the item-choice suprema. -/
private lemma generalizedAssignmentFlatDualLift_assignment {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (mu : Fin n → ℝ) (i : Fin m) :
    generalizedAssignmentFlatDualLift a c mu
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) =
      sSup
        ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c mu i o) ''
          Set.univ) := by
  -- Cancel the row equivalence and expose the assignment branch.
  simp [generalizedAssignmentFlatDualLift]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the slack coordinates of
the canonical flattened dual lift are the assignment suprema minus the reduced profits. -/
private lemma generalizedAssignmentFlatDualLift_slack {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (mu : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    generalizedAssignmentFlatDualLift a c mu
        (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j)))) =
      sSup
          ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c mu i o) ''
            Set.univ) +
        mu j * a i - c i j := by
  -- Cancel the row equivalence and expose the slack branch.
  simp [generalizedAssignmentFlatDualLift]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: nonnegative capacity
multipliers lift to a feasible point of the flattened LP dual. -/
private lemma generalizedAssignmentFlatDualLift_mem {m n : ℕ}
    (a : Fin m → ℝ) (c : Fin m → Fin n → ℝ) (mu : Fin n → ℝ)
    (hmu : 0 ≤ mu) :
    generalizedAssignmentFlatDualLift a c mu ∈
      dual_feasible_region
        (generalizedAssignmentFlatMatrix a) (generalizedAssignmentFlatObjective c) := by
  rw [mem_generalizedAssignmentFlatDual_iff]
  refine ⟨?_, ?_⟩
  · intro row
    cases hsplit : (generalizedAssignmentFlatRowEquiv m n).symm row with
    | inl j =>
        have hrow : row = generalizedAssignmentFlatRowEquiv m n (Sum.inl j) := by
          simpa [hsplit] using
            (generalizedAssignmentFlatRowEquiv m n).apply_symm_apply row |>.symm
        rw [hrow, generalizedAssignmentFlatDualLift_capacity]
        exact hmu j
    | inr rest =>
        cases rest with
        | inl i =>
            have hrow :
                row = generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i)) := by
              simpa [hsplit] using
                (generalizedAssignmentFlatRowEquiv m n).apply_symm_apply row |>.symm
            rw [hrow, generalizedAssignmentFlatDualLift_assignment]
            exact itemChoiceSup_nonneg a c mu i
        | inr ij =>
            rcases ij with ⟨i, j⟩
            have hrow :
                row = generalizedAssignmentFlatRowEquiv m n
                  (Sum.inr (Sum.inr (i, j))) := by
              simpa [hsplit] using
                (generalizedAssignmentFlatRowEquiv m n).apply_symm_apply row |>.symm
            rw [hrow, generalizedAssignmentFlatDualLift_slack]
            linarith [itemChoiceValue_some_le_sup a c mu i j]
  · intro i j
    rw [generalizedAssignmentFlatDualLift_capacity,
      generalizedAssignmentFlatDualLift_assignment, generalizedAssignmentFlatDualLift_slack]
    ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: every nonnegative capacity
multiplier has a flattened dual lift with exactly the same objective value. -/
private lemma exists_flatDualWithObjective_eq_capacityRelaxedValue {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ)
    (mu : Fin n → ℝ) (hmu : 0 ≤ mu) :
    ∃ u ∈ dual_feasible_region
        (generalizedAssignmentFlatMatrix a) (generalizedAssignmentFlatObjective c),
      u ⬝ᵥ generalizedAssignmentFlatRhs b =
        generalized_assignment_capacity_relaxed_value a b c mu := by
  refine ⟨generalizedAssignmentFlatDualLift a c mu,
    generalizedAssignmentFlatDualLift_mem a c mu hmu, ?_⟩
  -- Project the lifted objective and use the established item-wise value formula.
  rw [generalizedAssignmentFlatDualObjective_eq,
    capacityRelaxedValue_eq_constant_add_singleChoiceSup]
  simp only [generalizedAssignmentFlatDualLift_capacity,
    generalizedAssignmentFlatDualLift_assignment]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: projecting the capacity
coordinates of a flattened dual vector produces a capacity multiplier. -/
private def generalizedAssignmentCapacityProjection {m n : ℕ}
    (u : Fin (n + (m + m * n)) → ℝ) : Fin n → ℝ :=
  fun j ↦ u (generalizedAssignmentFlatRowEquiv m n (Sum.inl j))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: the capacity-relaxed value
at the capacity projection of a feasible flattened dual is at most its flattened objective. -/
private lemma capacityRelaxedValue_le_flatDualObjective {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ)
    (u : Fin (n + (m + m * n)) → ℝ)
    (hu : u ∈ dual_feasible_region
      (generalizedAssignmentFlatMatrix a) (generalizedAssignmentFlatObjective c)) :
    0 ≤ generalizedAssignmentCapacityProjection u ∧
      generalized_assignment_capacity_relaxed_value a b c
          (generalizedAssignmentCapacityProjection u) ≤
        u ⬝ᵥ generalizedAssignmentFlatRhs b := by
  classical
  rcases (mem_generalizedAssignmentFlatDual_iff a c u).mp hu with ⟨hnonneg, heq⟩
  refine ⟨?_, ?_⟩
  · intro j
    exact hnonneg (generalizedAssignmentFlatRowEquiv m n (Sum.inl j))
  · have hchoice :
        ∀ i o,
          generalized_assignment_item_choice_value a c
              (generalizedAssignmentCapacityProjection u) i o ≤
            u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) := by
      intro i o
      cases o with
      | none =>
          simpa using hnonneg
            (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i)))
      | some j =>
          have hslack := hnonneg
            (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inr (i, j))))
          have hij := heq i j
          simp only [generalized_assignment_item_choice_value_some,
            generalizedAssignmentCapacityProjection]
          linarith
    have hitemBound :
        ∀ i,
          sSup
              ((fun o : Option (Fin n) ↦
                  generalized_assignment_item_choice_value a c
                    (generalizedAssignmentCapacityProjection u) i o) '' Set.univ) ≤
            u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) := by
      intro i
      refine csSup_le ?_ ?_
      · exact ⟨_, ⟨none, Set.mem_univ _, rfl⟩⟩
      · rintro _ ⟨o, ho, rfl⟩
        exact hchoice i o
    calc
      generalized_assignment_capacity_relaxed_value a b c
          (generalizedAssignmentCapacityProjection u) =
          (∑ j, generalizedAssignmentCapacityProjection u j * b j) +
            ∑ i,
              sSup
                ((fun o : Option (Fin n) ↦
                    generalized_assignment_item_choice_value a c
                      (generalizedAssignmentCapacityProjection u) i o) '' Set.univ) := by
            rw [capacityRelaxedValue_eq_constant_add_singleChoiceSup]
      _ ≤ (∑ j, generalizedAssignmentCapacityProjection u j * b j) +
          ∑ i, u (generalizedAssignmentFlatRowEquiv m n (Sum.inr (Sum.inl i))) := by
            exact add_le_add (le_refl _) (Finset.sum_le_sum fun i _ ↦ hitemBound i)
      _ = u ⬝ᵥ generalizedAssignmentFlatRhs b := by
            rw [generalizedAssignmentFlatDualObjective_eq]
            rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean`: a generic finite real LP with
a nonempty dual has equal real primal supremum and dual infimum, including an empty primal. -/
private lemma realLinearProgramSup_eq_dualInf_of_dualNonempty
    {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℝ)
    (rhs : Fin r → ℝ)
    (obj : Fin d → ℝ)
    (hDual : (dual_feasible_region A obj).Nonempty) :
    sSup (primal_objective_values A rhs obj) =
      sInf (dual_objective_values A rhs obj) := by
  by_cases hPrimal : (primal_feasible_region A rhs).Nonempty
  · have hPrimalValues : (primal_objective_values A rhs obj).Nonempty := by
      rcases hPrimal with ⟨x, hx⟩
      exact ⟨obj ⬝ᵥ x, ⟨x, hx, rfl⟩⟩
    have hDualValues : (dual_objective_values A rhs obj).Nonempty := by
      rcases hDual with ⟨u, hu⟩
      exact ⟨u ⬝ᵥ rhs, ⟨u, hu, rfl⟩⟩
    have hPrimalBdd := primal_objective_values_bddAbove_of_dual_nonempty A rhs obj hDual
    have hDualBdd : BddBelow (dual_objective_values A rhs obj) := by
      rcases hPrimal with ⟨x, hx⟩
      refine ⟨obj ⬝ᵥ x, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      exact weak_duality_feasible_pair A rhs obj hx hu
    apply le_antisymm
    · -- Weak duality bounds the primal supremum by every feasible dual objective.
      refine le_csInf hDualValues ?_
      rintro _ ⟨u, hu, rfl⟩
      refine csSup_le hPrimalValues ?_
      rintro _ ⟨x, hx, rfl⟩
      exact weak_duality_feasible_pair A rhs obj hx hu
    · -- A strict gap would produce a dual objective strictly inside that gap.
      by_contra hnot
      have hgap :
          sSup (primal_objective_values A rhs obj) <
            sInf (dual_objective_values A rhs obj) := lt_of_not_ge hnot
      obtain ⟨z, hPrimalLt, hzDual⟩ := exists_between hgap
      have hExtendedLe :
          sSup
              ((fun x : Fin d → ℝ ↦ ((obj ⬝ᵥ x : ℝ) : EReal)) ''
                primal_feasible_region A rhs) ≤
            ((sSup (primal_objective_values A rhs obj) : ℝ) : EReal) := by
        refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact EReal.coe_le_coe_iff.mpr
          (le_csSup hPrimalBdd (show obj ⬝ᵥ x ∈ primal_objective_values A rhs obj from
            ⟨x, hx, rfl⟩))
      have hExtendedLt :
          sSup
              ((fun x : Fin d → ℝ ↦ ((obj ⬝ᵥ x : ℝ) : EReal)) ''
                primal_feasible_region A rhs) <
            (z : EReal) := by
        exact hExtendedLe.trans_lt (by exact_mod_cast hPrimalLt)
      obtain ⟨u, hu, huLt⟩ :=
        exists_dual_feasible_below_of_lt_primal_sup A rhs obj hPrimal hExtendedLt
      have hInfLe : sInf (dual_objective_values A rhs obj) ≤ u ⬝ᵥ rhs :=
        csInf_le hDualBdd ⟨u, hu, rfl⟩
      linarith
  · have hPrimalEmpty : primal_feasible_region A rhs = (∅ : Set (Fin d → ℝ)) := by
      rwa [Set.not_nonempty_iff_eq_empty] at hPrimal
    have hDualUnbounded : ¬ BddBelow (dual_objective_values A rhs obj) :=
      dual_objective_values_not_bddBelow_of_primal_empty A rhs obj hPrimal hDual
    -- Both real-valued conventions are `0`: the primal image is empty and the dual is unbounded.
    rw [primal_objective_values, hPrimalEmpty, Set.image_empty, Real.sSup_empty,
      Real.sInf_of_not_bddBelow hDualUnbounded]

/-- Exercise 8.6 (1). If one dualizes the capacity constraints of the generalized assignment
problem, then the resulting Lagrangian dual gives no better bound than the usual
linear-programming relaxation. -/
theorem exercise_8_6_capacity_relaxed_dual_eq_lp_value {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_dual_value a b c =
      generalized_assignment_lp_value a b c := by
  -- Route correction: the earlier dependency-object failure was transient; the validated route
  -- compares the reduced dual with the explicit flattened LP dual in both directions.
  have hInf :
      sInf
          ((fun mu : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c mu) ''
            Set.Ici (0 : Fin n → ℝ)) =
        sInf
          (dual_objective_values
            (generalizedAssignmentFlatMatrix a)
            (generalizedAssignmentFlatRhs b)
            (generalizedAssignmentFlatObjective c)) := by
    apply csInf_eq_csInf_of_forall_exists_le
    · rintro _ ⟨mu, hmu, rfl⟩
      obtain ⟨u, hu, huObjective⟩ :=
        exists_flatDualWithObjective_eq_capacityRelaxedValue a b c mu hmu
      refine ⟨u ⬝ᵥ generalizedAssignmentFlatRhs b, ⟨u, hu, rfl⟩, ?_⟩
      exact le_of_eq huObjective
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨hmu, hObjective⟩ := capacityRelaxedValue_le_flatDualObjective a b c u hu
      refine ⟨generalized_assignment_capacity_relaxed_value a b c
          (generalizedAssignmentCapacityProjection u), ?_, hObjective⟩
      exact ⟨generalizedAssignmentCapacityProjection u, hmu, rfl⟩
  have hDual :
      (dual_feasible_region
        (generalizedAssignmentFlatMatrix a) (generalizedAssignmentFlatObjective c)).Nonempty := by
    have hzero : 0 ≤ (0 : Fin n → ℝ) := le_rfl
    obtain ⟨u, hu, huObjective⟩ :=
      exists_flatDualWithObjective_eq_capacityRelaxedValue a b c 0 hzero
    -- The objective identity is not needed here; the lifted zero multiplier supplies feasibility.
    exact ⟨u, hu⟩
  have hStrong :=
    realLinearProgramSup_eq_dualInf_of_dualNonempty
      (generalizedAssignmentFlatMatrix a)
      (generalizedAssignmentFlatRhs b)
      (generalizedAssignmentFlatObjective c)
      hDual
  -- Cofinality identifies the reduced and full duals, and finite LP duality closes the chain.
  calc
    generalized_assignment_capacity_relaxed_dual_value a b c =
        sInf
          ((fun mu : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c mu) ''
            Set.Ici (0 : Fin n → ℝ)) := rfl
    _ = sInf
        (dual_objective_values
          (generalizedAssignmentFlatMatrix a)
          (generalizedAssignmentFlatRhs b)
          (generalizedAssignmentFlatObjective c)) := hInf
    _ = sSup
        (primal_objective_values
          (generalizedAssignmentFlatMatrix a)
          (generalizedAssignmentFlatRhs b)
          (generalizedAssignmentFlatObjective c)) := hStrong.symm
    _ = generalized_assignment_lp_value a b c :=
      (generalizedAssignmentLpValue_eq_flatPrimalSup a b c).symm

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_6.lean
Exercise 8.6 (2). Assuming the machine capacities are nonnegative, the dual obtained by
dualizing the assignment constraints is at least as strong as the dual obtained by dualizing the
capacity constraints; as an upper bound for the maximization problem, it is therefore smaller. -/
theorem exercise_8_6_assignment_relaxed_dual_le_capacity_relaxed_dual {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ)
    (hb_nonneg : ∀ j, 0 ≤ b j) :
    generalized_assignment_assignment_relaxed_dual_value a b c ≤
      generalized_assignment_capacity_relaxed_dual_value a b c := by
  classical
  let xZero : Fin m → Fin n → Bool := fun _ _ ↦ false
  have hxZero : xZero ∈ generalized_assignment_capacity_base_set a b := by
    -- Nonnegative capacities make the all-zero pattern feasible for every machine.
    rw [mem_generalized_assignment_capacity_base_set_iff]
    intro j
    simpa [xZero] using hb_nonneg j
  have hbase : (generalized_assignment_capacity_base_set a b).Nonempty :=
    ⟨xZero, hxZero⟩
  have hAssignmentBdd :
      BddBelow
        ((fun lam : Fin m → ℝ ↦ generalized_assignment_assignment_relaxed_value a b c lam) ''
          Set.Ici (0 : Fin m → ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨lam, hlam, rfl⟩
    have hImageBdd :
        BddAbove
          ((fun x : Fin m → Fin n → Bool ↦
              generalized_assignment_objective c x +
                ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
            generalized_assignment_capacity_base_set a b) := by
      let hs : (generalized_assignment_capacity_base_set a b).Finite := Set.toFinite _
      simpa [hs] using
        (hs.image
          (fun x : Fin m → Fin n → Bool ↦
            generalized_assignment_objective c x +
              ∑ i, lam i * (1 - ∑ j, bool_entry (x i j)))).bddAbove
    -- Evaluating at the zero pattern bounds every nonnegative-multiplier relaxation below by zero.
    dsimp only
    rw [generalized_assignment_assignment_relaxed_value_eq_sSup]
    calc
      0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ ↦ hlam i
      _ = generalized_assignment_objective c xZero +
          ∑ i, lam i * (1 - ∑ j, bool_entry (xZero i j)) := by
            simp [generalized_assignment_objective, xZero]
      _ ≤ sSup
          ((fun x : Fin m → Fin n → Bool ↦
              generalized_assignment_objective c x +
                ∑ i, lam i * (1 - ∑ j, bool_entry (x i j))) ''
            generalized_assignment_capacity_base_set a b) :=
        le_csSup hImageBdd ⟨xZero, hxZero, rfl⟩
  rw [generalized_assignment_assignment_relaxed_dual_value_eq_sInf,
    generalized_assignment_capacity_relaxed_dual_value_eq_sInf]
  have hCapacityNonempty :
      ((fun μ : Fin n → ℝ ↦ generalized_assignment_capacity_relaxed_value a b c μ) ''
        Set.Ici (0 : Fin n → ℝ)).Nonempty := by
    exact ⟨generalized_assignment_capacity_relaxed_value a b c 0, ⟨0, by simp, rfl⟩⟩
  refine le_csInf hCapacityNonempty ?_
  rintro _ ⟨μ, hμ, rfl⟩
  let lam : Fin m → ℝ := fun i ↦
    sSup
      ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
        Set.univ)
  have hlam : lam ∈ Set.Ici (0 : Fin m → ℝ) := by
    intro i
    exact itemChoiceSup_nonneg a c μ i
  -- The item-wise best reduced profits give an admissible assignment multiplier vector.
  calc
    sInf
        ((fun lam : Fin m → ℝ ↦ generalized_assignment_assignment_relaxed_value a b c lam) ''
          Set.Ici (0 : Fin m → ℝ)) ≤
        generalized_assignment_assignment_relaxed_value a b c lam :=
      csInf_le hAssignmentBdd ⟨lam, hlam, rfl⟩
    _ ≤ generalized_assignment_capacity_relaxed_value a b c μ := by
      exact assignmentRelaxedValue_le_capacityRelaxedValue_of_nonempty a b c μ hμ hbase

/-- Exercise 8.6 (3). For fixed multipliers `λ`, assuming the machine capacities are
nonnegative so that each machine knapsack family contains the zero pattern, dualizing the
assignment constraints decomposes the relaxation into `n` independent `0`-`1` knapsack
subproblems, one for each machine `j`. -/
theorem exercise_8_6_assignment_relaxed_subproblems_are_knapsack {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ)
    (hb_nonneg : ∀ j, 0 ≤ b j) :
    generalized_assignment_assignment_relaxed_value a b c lam =
      (∑ i, lam i) +
        ∑ j,
          sSup
            ((fun z : Fin m → Bool ↦ generalized_assignment_column_reduced_profit c lam j z) ''
              generalized_assignment_block_patterns
                (generalized_assignment_capacity_coeffs a) b j) := by
  -- The helper lemma already packages the finite maximizer construction for each machine block.
  exact assignmentRelaxedValue_eq_constant_add_knapsackSup a b c lam hb_nonneg

/-- Exercise 8.6 (4). For fixed multipliers `μ`, dualizing the capacity constraints decomposes
the relaxation into `m` independent single-item choice problems: each item is either left
unassigned or sent to one machine with reduced profit `c_ij - μ_j a_i`. -/
theorem exercise_8_6_capacity_relaxed_subproblems_are_single_choice {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin m → Fin n → ℝ) (μ : Fin n → ℝ) :
    generalized_assignment_capacity_relaxed_value a b c μ =
      (∑ j, μ j * b j) +
        ∑ i,
          sSup
            ((fun o : Option (Fin n) ↦ generalized_assignment_item_choice_value a c μ i o) ''
              Set.univ) :=
  by
  -- The helper lemma already packages the row-wise maximizer construction.
  exact capacityRelaxedValue_eq_constant_add_singleChoiceSup a b c μ

end Exercise86
