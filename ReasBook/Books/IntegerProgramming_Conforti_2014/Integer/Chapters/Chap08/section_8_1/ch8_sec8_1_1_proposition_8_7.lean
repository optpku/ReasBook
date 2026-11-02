import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

section Proposition87

variable {m n : ℕ}

/-- The feasible pairs `(x,y)` in the Lagrangian relaxation obtained by keeping the linking
constraints `y_{ij} ≤ x_j` together with the binary restrictions on `x_j` and `y_{ij}`. -/
def facility_location_lagrangian_relaxation_feasible
    (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, y i j ≤ x j) ∧
    (∀ i j, y i j = 0 ∨ y i j = 1) ∧
      (∀ j, x j = 0 ∨ x j = 1)

/-- The objective value of the Lagrangian relaxation `(8.6)` for profits `c`, opening costs `f`,
and multipliers `lam`. -/
def facility_location_lagrangian_relaxation_value
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ) : ℝ :=
  (∑ i, lam i) + ∑ j, ((∑ i, (c i j - lam i) * y i j) - f j * x j)

/-- The feasible set of the Proposition 8.7 Lagrangian relaxation, written on pairs `(y, x)` so it
matches the later chapter convention for facility-location points. -/
def facility_location_lagrangian_relaxation_feasible_set :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy | facility_location_lagrangian_relaxation_feasible xy.2 xy.1}

/-- Membership in `facility_location_lagrangian_relaxation_feasible_set` means exactly that the
pair `(y, x)` satisfies the linking inequalities and binary restrictions from `(8.6)`. -/
theorem mem_facility_location_lagrangian_relaxation_feasible_set_iff
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    xy ∈ facility_location_lagrangian_relaxation_feasible_set ↔
      facility_location_lagrangian_relaxation_feasible xy.2 xy.1 :=
  Iff.rfl

/-- The Lagrangian-relaxation objective as a function on pairs `(y, x)`. -/
def facility_location_lagrangian_relaxation_pair_value
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
  fun xy ↦ facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1

/-- Evaluating `facility_location_lagrangian_relaxation_pair_value c f lam` on `(y, x)` recovers
the original objective formula. -/
theorem facility_location_lagrangian_relaxation_pair_value_mk
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (y : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    facility_location_lagrangian_relaxation_pair_value c f lam (y, x) =
      facility_location_lagrangian_relaxation_value c f lam x y :=
  rfl

/-- The reduced profit `∑_ℓ (c_{ℓj} - λ_ℓ)^+ - f_j` attached to facility `j`. -/
def facility_location_reduced_profit
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (j : Fin n) : ℝ :=
  (∑ i, max (c i j - lam i) 0) - f j

/-- The opening decision `x_j(λ)` from the source formula. -/
noncomputable def lagrangian_relaxation_open_decision
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    Fin n → ℝ :=
  fun j ↦ if 0 < facility_location_reduced_profit c f lam j then (1 : ℝ) else 0

/-- Evaluating `lagrangian_relaxation_open_decision c f lam` at `j` returns the source formula for
`x_j(λ)`. -/
theorem lagrangian_relaxation_open_decision_apply
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (j : Fin n) :
    lagrangian_relaxation_open_decision c f lam j =
      if 0 < facility_location_reduced_profit c f lam j then (1 : ℝ) else 0 := rfl

/-- The assignment decision `y_{ij}(λ)` from the source formula. -/
noncomputable def lagrangian_relaxation_assignment_decision
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦
    if 0 < c i j - lam i ∧ 0 < facility_location_reduced_profit c f lam j then (1 : ℝ) else 0

/-- Evaluating `lagrangian_relaxation_assignment_decision c f lam` at `(i,j)` returns the source
formula for `y_{ij}(λ)`. -/
theorem lagrangian_relaxation_assignment_decision_apply
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (i : Fin m) (j : Fin n) :
    lagrangian_relaxation_assignment_decision c f lam i j =
      if 0 < c i j - lam i ∧ 0 < facility_location_reduced_profit c f lam j then
        (1 : ℝ)
      else
        0 := rfl

/-- The explicit Proposition 8.7 solution pair `(y(λ), x(λ))`. -/
noncomputable def lagrangian_relaxation_solution
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    : (Fin m → Fin n → ℝ) × (Fin n → ℝ) :=
  (lagrangian_relaxation_assignment_decision c f lam,
    lagrangian_relaxation_open_decision c f lam)

/-- The assignment component of `lagrangian_relaxation_solution c f lam` is the source formula
`y(λ)`. -/
theorem lagrangian_relaxation_solution_assignment
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    (lagrangian_relaxation_solution c f lam).1 =
      lagrangian_relaxation_assignment_decision c f lam :=
  rfl

/-- The opening component of `lagrangian_relaxation_solution c f lam` is the source formula
`x(λ)`. -/
theorem lagrangian_relaxation_solution_open
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    (lagrangian_relaxation_solution c f lam).2 =
      lagrangian_relaxation_open_decision c f lam :=
  rfl

/-- Helper for Proposition 8.7: the explicit solution pair satisfies the linking and binary
constraints of the Lagrangian relaxation. -/
lemma lagrangian_relaxation_solution_mem_feasible_set
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    lagrangian_relaxation_solution c f lam ∈
      facility_location_lagrangian_relaxation_feasible_set := by
  rw [mem_facility_location_lagrangian_relaxation_feasible_set_iff]
  constructor
  · intro i j
    -- The linking inequality is decided by the reduced-profit and coefficient branches.
    by_cases hj : 0 < facility_location_reduced_profit c f lam j
    · by_cases hij : 0 < c i j - lam i
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          lagrangian_relaxation_open_decision_apply, hj, hij]
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          lagrangian_relaxation_open_decision_apply, hj, hij]
    · by_cases hij : 0 < c i j - lam i
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          lagrangian_relaxation_open_decision_apply, hj, hij]
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          lagrangian_relaxation_open_decision_apply, hj, hij]
  constructor
  · intro i j
    -- Each assignment decision is explicitly `0` or `1`.
    by_cases hij : 0 < c i j - lam i
    · by_cases hj : 0 < facility_location_reduced_profit c f lam j
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          hij, hj]
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          hij, hj]
    · by_cases hj : 0 < facility_location_reduced_profit c f lam j
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          hij, hj]
      · simp [lagrangian_relaxation_solution, lagrangian_relaxation_assignment_decision_apply,
          hij, hj]
  · intro j
    -- Each opening decision is explicitly `0` or `1`.
    by_cases h : 0 < facility_location_reduced_profit c f lam j
    · simp [lagrangian_relaxation_solution, lagrangian_relaxation_open_decision_apply, h]
    · simp [lagrangian_relaxation_solution, lagrangian_relaxation_open_decision_apply, h]

/-- Helper for Proposition 8.7: each feasible column contribution is bounded by the positive part
of the reduced profit attached to that facility. -/
lemma column_objective_le_positive_part_reduced_profit
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    {x : Fin n → ℝ} {y : Fin m → Fin n → ℝ}
    (hfeas : facility_location_lagrangian_relaxation_feasible x y) (j : Fin n) :
    ((∑ i, (c i j - lam i) * y i j) - f j * x j) ≤
      max (facility_location_reduced_profit c f lam j) 0 := by
  rcases hfeas with ⟨hlink, hybin, hxbin⟩
  rcases hxbin j with hx0 | hx1
  · -- If `x_j = 0`, the linking inequalities force every assignment in the column to vanish.
    have hy_nonneg : ∀ i, 0 ≤ y i j := by
      intro i
      rcases hybin i j with hy0 | hy1
      · simp [hy0]
      · simp [hy1]
    have hy_zero : ∀ i, y i j = 0 := by
      intro i
      have hy_le : y i j ≤ 0 := by simpa [hx0] using hlink i j
      exact le_antisymm hy_le (hy_nonneg i)
    have hsum_zero : ∑ i, (c i j - lam i) * y i j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hy_zero i]
    calc
      ((∑ i, (c i j - lam i) * y i j) - f j * x j) = 0 := by
        simp [hsum_zero, hx0]
      _ ≤ max (facility_location_reduced_profit c f lam j) 0 := by
        exact le_max_right _ _
  · -- If `x_j = 1`, each assignment contributes at most the positive part of its coefficient.
    have hterm :
        ∀ i, (c i j - lam i) * y i j ≤ max (c i j - lam i) 0 := by
      intro i
      rcases hybin i j with hy0 | hy1
      · calc
          (c i j - lam i) * y i j = 0 := by simp [hy0]
          _ ≤ max (c i j - lam i) 0 := by
            exact le_max_right _ _
      · by_cases hij : 0 < c i j - lam i
        · have hmax : max (c i j - lam i) 0 = c i j - lam i := max_eq_left (le_of_lt hij)
          have hEq : (c i j - lam i) * y i j = max (c i j - lam i) 0 := by
            calc
              (c i j - lam i) * y i j = c i j - lam i := by simp [hy1]
              _ = max (c i j - lam i) 0 := by rw [hmax]
          rw [hEq]
        · have hle : c i j - lam i ≤ 0 := le_of_not_gt hij
          have hmax : max (c i j - lam i) 0 = 0 := max_eq_right hle
          calc
            (c i j - lam i) * y i j = c i j - lam i := by simp [hy1]
            _ ≤ 0 := hle
            _ = max (c i j - lam i) 0 := by rw [hmax]
    have hsum_le :
        ∑ i, (c i j - lam i) * y i j ≤ ∑ i, max (c i j - lam i) 0 := by
      exact Finset.sum_le_sum fun i _ ↦ hterm i
    calc
      ((∑ i, (c i j - lam i) * y i j) - f j * x j)
          = ((∑ i, (c i j - lam i) * y i j) - f j) := by
            simp [hx1]
      _ ≤ ((∑ i, max (c i j - lam i) 0) - f j) := by
        exact sub_le_sub_right hsum_le _
      _ = facility_location_reduced_profit c f lam j := by
        rw [facility_location_reduced_profit]
      _ ≤ max (facility_location_reduced_profit c f lam j) 0 := by
        exact le_max_left _ _

/-- Helper for Proposition 8.7: the explicit column rule attains exactly the positive part of the
reduced profit for that facility. -/
lemma solution_column_objective_eq_positive_part_reduced_profit
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) (j : Fin n) :
    ((∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j) -
        f j * lagrangian_relaxation_open_decision c f lam j) =
      max (facility_location_reduced_profit c f lam j) 0 := by
  by_cases hj : 0 < facility_location_reduced_profit c f lam j
  · -- In the profitable branch, the explicit assignments keep exactly the positive coefficients.
    have hsum :
        ∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j =
          ∑ i, max (c i j - lam i) 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hij : 0 < c i j - lam i
      · have hmax : max (c i j - lam i) 0 = c i j - lam i := max_eq_left (le_of_lt hij)
        simp [lagrangian_relaxation_assignment_decision_apply, hj, hij, hmax]
      · have hle : c i j - lam i ≤ 0 := le_of_not_gt hij
        have hmax : max (c i j - lam i) 0 = 0 := max_eq_right hle
        simp [lagrangian_relaxation_assignment_decision_apply, hj, hij, hmax]
    have hmax :
        max (facility_location_reduced_profit c f lam j) 0 =
          facility_location_reduced_profit c f lam j := max_eq_left (le_of_lt hj)
    calc
      ((∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j) -
          f j * lagrangian_relaxation_open_decision c f lam j)
          = (∑ i, max (c i j - lam i) 0) - f j := by
            simp [lagrangian_relaxation_open_decision_apply, hj, hsum]
      _ = facility_location_reduced_profit c f lam j := by
        rw [facility_location_reduced_profit]
      _ = max (facility_location_reduced_profit c f lam j) 0 := by
        rw [hmax]
  · -- In the nonprofitable branch, both the opening and the assignments are zero.
    have hsum_zero :
        ∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [lagrangian_relaxation_assignment_decision_apply, hj]
    have hmax :
        max (facility_location_reduced_profit c f lam j) 0 = 0 := by
      exact max_eq_right (le_of_not_gt hj)
    calc
      ((∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j) -
          f j * lagrangian_relaxation_open_decision c f lam j)
          = 0 := by
            simp [lagrangian_relaxation_open_decision_apply, hj, hsum_zero]
      _ = max (facility_location_reduced_profit c f lam j) 0 := by
        rw [hmax]

/-- Helper for Proposition 8.7: the explicit solution is a maximizer of the pair-valued
Lagrangian-relaxation objective over the feasible set. -/
lemma lagrangian_relaxation_solution_isMaxOn
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    IsMaxOn
      (facility_location_lagrangian_relaxation_pair_value c f lam)
      facility_location_lagrangian_relaxation_feasible_set
      (lagrangian_relaxation_solution c f lam) := by
  rw [isMaxOn_iff]
  intro xy hxy
  rcases xy with ⟨y, x⟩
  rw [mem_facility_location_lagrangian_relaxation_feasible_set_iff] at hxy
  have hcolumn :
      ∑ j, ((∑ i, (c i j - lam i) * y i j) - f j * x j) ≤
        ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
    -- Sum the columnwise upper bounds over all facilities.
    exact Finset.sum_le_sum fun j _ ↦
      column_objective_le_positive_part_reduced_profit c f lam hxy j
  have hsolution :
      ∑ j, ((∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j) -
        f j * lagrangian_relaxation_open_decision c f lam j) =
        ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
    -- The explicit solution realizes the positive part in every column.
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact solution_column_objective_eq_positive_part_reduced_profit c f lam j
  -- Assemble the constant term and the column bounds into the `IsMaxOn` inequality.
  calc
    facility_location_lagrangian_relaxation_pair_value c f lam (y, x) =
        (∑ i, lam i) + ∑ j, ((∑ i, (c i j - lam i) * y i j) - f j * x j) := by
          rfl
    _ ≤ (∑ i, lam i) + ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
      simpa using add_le_add_left hcolumn (∑ i, lam i)
    _ = (∑ i, lam i) + ∑ j,
          ((∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_decision c f lam i j) -
            f j * lagrangian_relaxation_open_decision c f lam j) := by
              rw [← hsolution]
    _ = facility_location_lagrangian_relaxation_pair_value c f lam
          (lagrangian_relaxation_solution c f lam) := by
            rfl

/-- Proposition 8.7. An optimal solution of the Lagrangian relaxation `(8.6)` is given by the
coordinatewise rules `y_{ij}(λ) = 1` iff `c_{ij} - λ_i > 0` and
`∑_ℓ (c_{ℓj} - λ_ℓ)^+ - f_j > 0`, and `x_j(λ) = 1` iff
`∑_ℓ (c_{ℓj} - λ_ℓ)^+ - f_j > 0`; otherwise the corresponding coordinate is `0`. -/
theorem proposition_8_7_optimal_lagrangian_relaxation_solution
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    lagrangian_relaxation_solution c f lam ∈
        facility_location_lagrangian_relaxation_feasible_set ∧
      IsMaxOn
        (facility_location_lagrangian_relaxation_pair_value c f lam)
        facility_location_lagrangian_relaxation_feasible_set
        (lagrangian_relaxation_solution c f lam) := by
  constructor
  · -- The explicit formulas satisfy the constraints of the relaxation.
    exact lagrangian_relaxation_solution_mem_feasible_set c f lam
  · -- The columnwise decomposition proves the explicit pair is optimal.
    exact lagrangian_relaxation_solution_isMaxOn c f lam

end Proposition87
