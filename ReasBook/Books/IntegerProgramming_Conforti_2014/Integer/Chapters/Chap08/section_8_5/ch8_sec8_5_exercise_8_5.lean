import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_7

-- Semantic recall note: the domain-sampling pass for this exercise identified the
-- uncapacitated-facility-location Lagrangian layer from Section 8.1 as the owner domain.
-- Primitive data here is only the fixed-`x` best-response assignment rule from Exercise 8.5 (1).
-- The fixed-`x` optimization problem depends only on the `y`-varying part of the Proposition 8.7
-- objective, so its main optimality theorem should use mathlib's canonical `IsMaxOn` owner on
-- that primitive layer; the full Lagrangian objective with opening costs is then a constant-shift
-- `bridge/view`. Exercise 8.5 (2) is an exact recall of Proposition 8.7 rather than a second
-- theorem.

section Exercise85

variable {m n : ℕ}

/-- The assignment rule from Exercise 8.5(i) after fixing the open-decision vector `x`. -/
noncomputable def lagrangian_relaxation_assignment_best_response_given_x
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦ if 0 < c i j - lam i then x j else 0

/-- Evaluating `lagrangian_relaxation_assignment_best_response_given_x c lam x` at `(i,j)` returns
the source formula `y_ij = x_j` when `c_ij - λ_i > 0`, and `0` otherwise. -/
theorem lagrangian_relaxation_assignment_best_response_given_x_apply
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (x : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    lagrangian_relaxation_assignment_best_response_given_x c lam x i j =
      if 0 < c i j - lam i then x j else 0 := rfl

/-- A fixed opening vector `x` admits a feasible assignment for the Proposition 8.7 Lagrangian
relaxation exactly when the opening decisions themselves satisfy the binary condition from `(8.6)`.
-/
theorem facility_location_lagrangian_relaxation_feasible_exists_iff
    (x : Fin n → ℝ) :
    (∃ y : Fin m → Fin n → ℝ, facility_location_lagrangian_relaxation_feasible x y) ↔
      ∀ j, x j = 0 ∨ x j = 1 := by
  constructor
  · rintro ⟨y, hy⟩
    exact hy.2.2
  · intro hx
    refine ⟨fun _ _ ↦ 0, ?_⟩
    refine ⟨?_, ?_, hx⟩
    · intro i j
      rcases hx j with h0 | h1
      · simp [h0]
      · simp [h1]
    · intro i j
      left
      rfl

/-- Helper for Exercise 8.5: the fixed-`x` best-response rule satisfies the linking and binary
constraints whenever the opening vector `x` is binary. -/
lemma bestResponseGivenXFeasible
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    facility_location_lagrangian_relaxation_feasible x
      (lagrangian_relaxation_assignment_best_response_given_x c lam x) := by
  constructor
  · intro i j
    -- The best response in each entry is either `x_j` or `0`, both of which stay below `x_j`.
    by_cases hij : 0 < c i j - lam i
    · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij]
    · rcases hx j with h0 | h1
      · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, h0]
      · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, h1]
  constructor
  · intro i j
    -- Each assignment coordinate is explicitly one of the binary opening values or `0`.
    by_cases hij : 0 < c i j - lam i
    · rcases hx j with h0 | h1
      · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, h0]
      · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, h1]
    · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij]
  · exact hx

/-- Helper for Exercise 8.5: every feasible assignment column is bounded by the positive-part
column value scaled by the fixed opening decision `x_j`. -/
lemma fixedOpeningColumnObjectiveLe
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ)
    {x : Fin n → ℝ} {y : Fin m → Fin n → ℝ}
    (hfeas : facility_location_lagrangian_relaxation_feasible x y) (j : Fin n) :
    ∑ i, (c i j - lam i) * y i j ≤ x j * ∑ i, max (c i j - lam i) 0 := by
  rcases hfeas with ⟨hlink, hybin, hxbin⟩
  rcases hxbin j with hx0 | hx1
  · -- Closed facilities force every assignment in the column to vanish.
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
    simp [hx0, hsum_zero]
  · -- Open facilities reduce to the same positive-part bound as Proposition 8.7.
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
          simp [hy1, hmax]
        · have hle : c i j - lam i ≤ 0 := le_of_not_gt hij
          have hmax : max (c i j - lam i) 0 = 0 := max_eq_right hle
          calc
            (c i j - lam i) * y i j = c i j - lam i := by simp [hy1]
            _ ≤ 0 := hle
            _ = max (c i j - lam i) 0 := by rw [hmax]
    have hsum_le :
        ∑ i, (c i j - lam i) * y i j ≤ ∑ i, max (c i j - lam i) 0 := by
      exact Finset.sum_le_sum fun i _ ↦ hterm i
    simpa [hx1] using hsum_le

/-- Helper for Exercise 8.5: the fixed-`x` best-response rule attains the scaled positive-part
column value in every facility column. -/
lemma bestResponseGivenXColumnObjectiveEq
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) (j : Fin n) :
    ∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_best_response_given_x c lam x i j =
      x j * ∑ i, max (c i j - lam i) 0 := by
  rcases hx j with hx0 | hx1
  · -- If `x_j = 0`, the best-response column is identically zero.
    have hsum_zero :
        ∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_best_response_given_x c lam x i j =
          0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      by_cases hij : 0 < c i j - lam i
      · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, hx0]
      · simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij]
    simp [hx0, hsum_zero]
  · -- If `x_j = 1`, the best response keeps exactly the positive coefficients.
    have hsum_eq :
        ∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_best_response_given_x c lam x i j =
          ∑ i, max (c i j - lam i) 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hij : 0 < c i j - lam i
      · have hmax : max (c i j - lam i) 0 = c i j - lam i := max_eq_left (le_of_lt hij)
        simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, hx1, hmax]
      · have hle : c i j - lam i ≤ 0 := le_of_not_gt hij
        have hmax : max (c i j - lam i) 0 = 0 := max_eq_right hle
        simp [lagrangian_relaxation_assignment_best_response_given_x_apply, hij, hmax]
    calc
      ∑ i, (c i j - lam i) * lagrangian_relaxation_assignment_best_response_given_x c lam x i j =
          ∑ i, max (c i j - lam i) 0 := hsum_eq
      _ = x j * ∑ i, max (c i j - lam i) 0 := by simp [hx1]

/-- Helper for Exercise 8.5: the full Lagrangian objective differs from the `f = 0` objective by
the penalty term `∑_j f_j x_j`, which is constant in the assignment vector `y`. -/
lemma fullValueEqZeroCostValueSubPenalty
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ) :
    facility_location_lagrangian_relaxation_value c f lam x y =
      facility_location_lagrangian_relaxation_value c 0 lam x y - ∑ j, f j * x j := by
  -- Expand the objective once, separate the penalty sum, and normalize the arithmetic.
  calc
    facility_location_lagrangian_relaxation_value c f lam x y =
        (∑ i, lam i) +
          ((∑ j, ∑ i, (c i j - lam i) * y i j) - ∑ j, f j * x j) := by
            simp [facility_location_lagrangian_relaxation_value, Finset.sum_sub_distrib]
    _ = facility_location_lagrangian_relaxation_value c 0 lam x y - ∑ j, f j * x j := by
      simp [facility_location_lagrangian_relaxation_value, sub_eq_add_neg, add_assoc]

/-- Exercise 8.5 (1). If the fixed opening vector `x` satisfies the primitive binary condition from
`(8.6)`, then the feasible assignment vector maximizing the fixed-`x` assignment subproblem is
given coordinatewise by `y_ij = x_j` when `c_ij - λ_i > 0`, and `0` otherwise. The opening costs
play no role in this fixed-`x` maximization, so the main statement uses the `f = 0` specialization
of the Proposition 8.7 objective. -/
theorem lagrangian_relaxation_assignment_best_response_given_x_is_optimal
    (c : Fin m → Fin n → ℝ) (lam : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    facility_location_lagrangian_relaxation_feasible x
        (lagrangian_relaxation_assignment_best_response_given_x c lam x) ∧
      IsMaxOn
        (facility_location_lagrangian_relaxation_value c 0 lam x)
        {y | facility_location_lagrangian_relaxation_feasible x y}
        (lagrangian_relaxation_assignment_best_response_given_x c lam x) := by
  constructor
  · -- First establish that the candidate assignment is feasible for the fixed opening vector.
    exact bestResponseGivenXFeasible c lam x hx
  · -- Then maximize the `f = 0` objective by summing the sharp column bounds.
    rw [isMaxOn_iff]
    intro y hy
    have hcolumn :
        ∑ j, ∑ i, (c i j - lam i) * y i j ≤
          ∑ j, x j * ∑ i, max (c i j - lam i) 0 := by
      exact Finset.sum_le_sum fun j _ ↦ fixedOpeningColumnObjectiveLe c lam hy j
    have hbest :
        ∑ j, ∑ i,
            (c i j - lam i) *
              lagrangian_relaxation_assignment_best_response_given_x c lam x i j =
          ∑ j, x j * ∑ i, max (c i j - lam i) 0 := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact bestResponseGivenXColumnObjectiveEq c lam x hx j
    calc
      facility_location_lagrangian_relaxation_value c 0 lam x y =
          (∑ i, lam i) + ∑ j, ∑ i, (c i j - lam i) * y i j := by
            simp [facility_location_lagrangian_relaxation_value]
      _ ≤ (∑ i, lam i) + ∑ j, x j * ∑ i, max (c i j - lam i) 0 := by
        simpa using add_le_add_left hcolumn (∑ i, lam i)
      _ = (∑ i, lam i) + ∑ j, ∑ i,
            (c i j - lam i) *
              lagrangian_relaxation_assignment_best_response_given_x c lam x i j := by
                rw [← hbest]
      _ = facility_location_lagrangian_relaxation_value c 0 lam x
            (lagrangian_relaxation_assignment_best_response_given_x c lam x) := by
              simp [facility_location_lagrangian_relaxation_value]

/-- The full Proposition 8.7 objective differs from the fixed-`x` assignment subproblem only by
the constant term `-∑_j f_j x_j`, so Exercise 8.5 (1)'s best response also maximizes the full
Lagrangian objective over the feasible assignments for the chosen binary opening vector `x`. -/
theorem lagrangian_relaxation_assignment_best_response_given_x_is_optimal_for_relaxation_value
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ)
    (x : Fin n → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    facility_location_lagrangian_relaxation_feasible x
        (lagrangian_relaxation_assignment_best_response_given_x c lam x) ∧
      IsMaxOn
        (facility_location_lagrangian_relaxation_value c f lam x)
        {y | facility_location_lagrangian_relaxation_feasible x y}
        (lagrangian_relaxation_assignment_best_response_given_x c lam x) := by
  rcases lagrangian_relaxation_assignment_best_response_given_x_is_optimal c lam x hx with
    ⟨hfeas, hmaxZero⟩
  constructor
  · -- Feasibility is identical for the full objective because the constraints do not involve `f`.
    exact hfeas
  · -- Transport the zero-opening-cost optimum across the constant penalty shift.
    rw [isMaxOn_iff] at hmaxZero ⊢
    intro y hy
    have hzero :
        facility_location_lagrangian_relaxation_value c 0 lam x y ≤
          facility_location_lagrangian_relaxation_value c 0 lam x
            (lagrangian_relaxation_assignment_best_response_given_x c lam x) :=
      hmaxZero y hy
    calc
      facility_location_lagrangian_relaxation_value c f lam x y =
          facility_location_lagrangian_relaxation_value c 0 lam x y - ∑ j, f j * x j :=
            fullValueEqZeroCostValueSubPenalty c f lam x y
      _ ≤ facility_location_lagrangian_relaxation_value c 0 lam x
            (lagrangian_relaxation_assignment_best_response_given_x c lam x) -
          ∑ j, f j * x j := by
            exact sub_le_sub_right hzero (∑ j, f j * x j)
      _ = facility_location_lagrangian_relaxation_value c f lam x
            (lagrangian_relaxation_assignment_best_response_given_x c lam x) := by
              symm
              exact fullValueEqZeroCostValueSubPenalty c f lam x
                (lagrangian_relaxation_assignment_best_response_given_x c lam x)

/-- For the opening rule used in Proposition 8.7, the fixed-`x` best response from Exercise 8.5(i)
coincides with the proposition's explicit assignment rule. -/
theorem lagrangian_relaxation_best_response_given_open_decision_eq_assignment_decision
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    lagrangian_relaxation_assignment_best_response_given_x c lam
        (lagrangian_relaxation_open_decision c f lam) =
      lagrangian_relaxation_assignment_decision c f lam := by
  funext i j
  by_cases hij : 0 < c i j - lam i <;>
    by_cases hj : 0 < facility_location_reduced_profit c f lam j <;>
      simp [lagrangian_relaxation_assignment_best_response_given_x,
        lagrangian_relaxation_open_decision, lagrangian_relaxation_assignment_decision, hij, hj]

end Exercise85

/-- Exercise 8.5 (2). After specializing the fixed-`x` best response from part (1) to the
opening rule `lagrangian_relaxation_open_decision c f lam`, the resulting optimal-solution
statement is exactly Proposition 8.7. -/
theorem exercise_8_5_proposition_8_7
    (c : Fin m → Fin n → ℝ) (f : Fin n → ℝ) (lam : Fin m → ℝ) :
    lagrangian_relaxation_solution c f lam ∈
        facility_location_lagrangian_relaxation_feasible_set ∧
      IsMaxOn
        (facility_location_lagrangian_relaxation_pair_value c f lam)
        facility_location_lagrangian_relaxation_feasible_set
        (lagrangian_relaxation_solution c f lam) :=
  proposition_8_7_optimal_lagrangian_relaxation_solution c f lam
