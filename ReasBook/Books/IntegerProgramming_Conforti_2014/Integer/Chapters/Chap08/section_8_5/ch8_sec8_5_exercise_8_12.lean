import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_8
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section Exercise812

variable {m n : ℕ}

/-- The integral feasible set of the uncapacitated facility-location formulation `(8.5)`,
with assignment equations, linking inequalities, and binary restrictions on both assignment and
opening variables. Assignment nonnegativity is recovered canonically from the binary constraints.
-/
def uncapacitated_facility_location_integer_feasible_set :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy |
    (∀ i, ∑ j, xy.1 i j = 1) ∧
      (∀ i j, xy.1 i j ≤ xy.2 j) ∧
        (∀ i j, xy.1 i j = 0 ∨ xy.1 i j = 1) ∧
          ∀ j, xy.2 j = 0 ∨ xy.2 j = 1}

/-- Membership in `uncapacitated_facility_location_integer_feasible_set` is exactly the canonical
binary-and-linking formulation of `(8.5)`. -/
theorem mem_uncapacitated_facility_location_integer_feasible_set_iff
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    xy ∈ uncapacitated_facility_location_integer_feasible_set ↔
      (∀ i, ∑ j, xy.1 i j = 1) ∧
        (∀ i j, xy.1 i j ≤ xy.2 j) ∧
          (∀ i j, xy.1 i j = 0 ∨ xy.1 i j = 1) ∧
            ∀ j, xy.2 j = 0 ∨ xy.2 j = 1 :=
  Iff.rfl

/-- Any assignment variable in the integral feasible set of `(8.5)` is nonnegative, because it is
binary. This recovers the redundant source-side nonnegativity inequality from the canonical owner.
-/
theorem nonneg_of_mem_uncapacitated_facility_location_integer_feasible_set
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ uncapacitated_facility_location_integer_feasible_set)
    (i : Fin m)
    (j : Fin n) :
    0 ≤ xy.1 i j := by
  rcases (mem_uncapacitated_facility_location_integer_feasible_set_iff.mp hxy).2.2.1 i j with
    hxyij | hxyij
  · simp [hxyij]
  · simp [hxyij]

/-- The optimal value of the integral uncapacitated facility-location formulation `(8.5)`,
represented as a `WithBot ℝ` supremum so that infeasible fixed-opening subproblems can still be
compared to it. -/
noncomputable def uncapacitated_facility_location_integer_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : WithBot ℝ :=
  sSup
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
      uncapacitated_facility_location_integer_feasible_set)

/-- Unfolding `uncapacitated_facility_location_integer_value c f` recovers the supremum of the
integral facility-location objective over `uncapacitated_facility_location_integer_feasible_set`.
-/
theorem uncapacitated_facility_location_integer_value_eq_sSup
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_integer_value c f =
      sSup
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
          uncapacitated_facility_location_integer_feasible_set) :=
  rfl

/-- The assignment matrices feasible for `(8.5)` after fixing the opening variables to `x`. -/
def uncapacitated_facility_location_assignments_for_openings
    (x : Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {y | (y, x) ∈ uncapacitated_facility_location_integer_feasible_set}

/-- Membership in `uncapacitated_facility_location_assignments_for_openings x` is exactly
feasibility of `(y, x)` for `(8.5)`. -/
theorem mem_uncapacitated_facility_location_assignments_for_openings_iff
    (x : Fin n → ℝ)
    {y : Fin m → Fin n → ℝ} :
    y ∈ uncapacitated_facility_location_assignments_for_openings x ↔
      (y, x) ∈ uncapacitated_facility_location_integer_feasible_set :=
  Iff.rfl

/-- In any feasible fixed-opening assignment, a customer assigned to facility `j` certifies that
`j` is open. This is the canonical consequence of the linking inequalities together with the
binary restriction on the opening variables. -/
theorem opening_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : y ∈ uncapacitated_facility_location_assignments_for_openings x)
    {i : Fin m}
    {j : Fin n}
    (hij : y i j = 1) :
    x j = 1 := by
  rcases (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mp hy with
    ⟨_, hlink, _, hx_binary⟩
  have hle : (1 : ℝ) ≤ x j := by
    simpa [hij] using hlink i j
  rcases hx_binary j with hxj | hxj
  · have hxj' : x j = 0 := by
      simpa using hxj
    rw [hxj'] at hle
    exact False.elim ((not_le_of_gt zero_lt_one) hle)
  · simpa using hxj

/-- The specialized subgradient vector `g(λ)` for the assignment equations
`∑_j y_ij = 1`, evaluated at the Proposition 8.7 optimal solution of `(8.6)`. -/
noncomputable def facility_location_subgradient
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) : Fin m → ℝ :=
  fun i ↦ 1 - ∑ j, lagrangian_relaxation_assignment_decision c f lam i j

/-- Evaluating `facility_location_subgradient c f lam` at `i` gives
`1 - ∑_j y_ij(λ)`. -/
theorem facility_location_subgradient_apply
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (i : Fin m) :
    facility_location_subgradient c f lam i =
      1 - ∑ j, lagrangian_relaxation_assignment_decision c f lam i j :=
  rfl

/-- `IsGreedyFacilityLocationAssignmentForOpenings c x y` means that `y` is feasible with the
fixed opening vector `x`, and each assigned customer is sent to an open facility maximizing
`c_ij` among the open facilities. The Proposition 8.7 choice `x = x(λ)` is a bridge/view
specialization used in the exercise statements below. -/
@[mk_iff isGreedyFacilityLocationAssignmentForOpenings_iff]
class IsGreedyFacilityLocationAssignmentForOpenings
    (c : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (y : Fin m → Fin n → ℝ) : Prop where
  feasible :
    y ∈ uncapacitated_facility_location_assignments_for_openings x
  maximizing (i : Fin m) (j k : Fin n)
      (hij : y i j = 1) (hk : x k = 1) :
      c i k ≤ c i j

/-- In a greedy feasible assignment, any facility actually used by a customer is open. -/
theorem IsGreedyFacilityLocationAssignmentForOpenings.opening_eq_one
    {c : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : IsGreedyFacilityLocationAssignmentForOpenings c x y)
    {i : Fin m}
    {j : Fin n}
    (hij : y i j = 1) :
    x j = 1 :=
  opening_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings hy.feasible hij

/-- Helper for Exercise 8.12: every integral feasible point of `(8.5)` is also feasible for the
LP relaxation from Proposition 8.8, since binary variables automatically satisfy the LP bounds.
-/
lemma mem_uncapacitated_facility_location_lp_feasible_set_of_mem_integer_feasible_set
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ uncapacitated_facility_location_integer_feasible_set) :
    xy ∈ uncapacitated_facility_location_lp_feasible_set := by
  rcases (mem_uncapacitated_facility_location_integer_feasible_set_iff.mp hxy) with
    ⟨hrow, hlink, _, hxBinary⟩
  -- Repackage the integer constraints into the LP owner from Proposition 8.8.
  rw [mem_uncapacitated_facility_location_lp_feasible_set_iff]
  refine ⟨hrow, ?_, hlink, ?_, ?_⟩
  · intro i j
    exact nonneg_of_mem_uncapacitated_facility_location_integer_feasible_set hxy i j
  · intro j
    rcases hxBinary j with hxj | hxj <;> simp [hxj]
  · intro j
    rcases hxBinary j with hxj | hxj <;> simp [hxj]

/-- Helper for Exercise 8.12: in every feasible fixed-opening assignment, each customer row picks
some facility with value `1`. -/
lemma exists_assignment_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : y ∈ uncapacitated_facility_location_assignments_for_openings x)
    (i : Fin m) :
    ∃ j, y i j = 1 := by
  rcases (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mp hy with
    ⟨hrow, _, hbinary, _⟩
  by_contra hnone
  have hallZero : ∀ j, y i j = 0 := by
    intro j
    rcases hbinary i j with hij | hij
    · exact hij
    · exact False.elim (hnone ⟨j, hij⟩)
  have hsumZero : ∑ j, y i j = 0 := by
    simp [hallZero]
  have hrowi := hrow i
  rw [hsumZero] at hrowi
  norm_num at hrowi

/-- Helper for Exercise 8.12: once row `i` assigns customer `i` to facility `j`, the whole row
objective collapses to the single coefficient `c i j`. -/
lemma rowObjective_eq_of_mem_uncapacitated_facility_location_assignments_for_openings
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : y ∈ uncapacitated_facility_location_assignments_for_openings x)
    {i : Fin m}
    {j : Fin n}
    (hij : y i j = 1) :
    ∑ k, c i k * y i k = c i j := by
  rcases (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mp hy with
    ⟨hrow, _, hbinary, _⟩
  have hrowY : ∀ i, ∑ k, y i k = 1 := by
    intro i
    simpa using hrow i
  have hbinaryY : ∀ i j, y i j = 0 ∨ y i j = 1 := by
    intro i j
    simpa using hbinary i j
  have hrestZero : Finset.sum (Finset.univ.erase j) (fun k ↦ y i k) = 0 := by
    have hrowi := hrowY i
    have hjMem : j ∈ Finset.univ := by
      simp
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
      (s := Finset.univ) (f := fun k ↦ y i k) hjMem] at hrowi
    rw [Finset.sdiff_singleton_eq_erase, hij] at hrowi
    linarith
  have hzeroOfNe : ∀ ⦃k : Fin n⦄, k ≠ j → y i k = 0 := by
    intro k hkj
    have hkNonneg : 0 ≤ y i k := by
      rcases hbinaryY i k with hik | hik <;> linarith
    have hkLeRest : y i k ≤ Finset.sum (Finset.univ.erase j) (fun l ↦ y i l) := by
      have hkMem : k ∈ Finset.univ.erase j := by
        simp [hkj]
      exact
        Finset.single_le_sum
          (fun l hl ↦ by
            rcases hbinaryY i l with hil | hil <;> linarith)
          hkMem
    have hkLeZero : y i k ≤ 0 := by
      simpa [hrestZero] using hkLeRest
    linarith
  -- Remove every off-diagonal term in the row sum, leaving only the chosen facility.
  calc
    ∑ k, c i k * y i k = c i j * y i j := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro k hk hkj
        simp [hzeroOfNe hkj]
      · simp
    _ = c i j := by simp [hij]

/-- Helper for Exercise 8.12: a greedy feasible assignment maximizes the original objective among
all assignments feasible for the same fixed opening vector `x`. -/
theorem IsGreedyFacilityLocationAssignmentForOpenings.isMaxOnObjective
    {c : Fin m → Fin n → ℝ}
    {f : Fin n → ℝ}
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : IsGreedyFacilityLocationAssignmentForOpenings c x y) :
    IsMaxOn
      (fun y' ↦ uncapacitated_facility_location_objective c f (y', x))
      (uncapacitated_facility_location_assignments_for_openings x)
      y := by
  rw [isMaxOn_iff]
  intro y' hy'
  have hrowLe :
      ∀ i, ∑ j, c i j * y' i j ≤ ∑ j, c i j * y i j := by
    intro i
    obtain ⟨j, hij⟩ :=
      exists_assignment_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings
        hy.feasible i
    obtain ⟨k, hik⟩ :=
      exists_assignment_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings
        hy' i
    have hkOpen : x k = 1 :=
      opening_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings hy' hik
    -- Compare the unique chosen facilities in the two feasible rows using the greedy rule.
    calc
      ∑ l, c i l * y' i l = c i k :=
        rowObjective_eq_of_mem_uncapacitated_facility_location_assignments_for_openings
          c hy' hik
      _ ≤ c i j := hy.maximizing i j k hij hkOpen
      _ = ∑ l, c i l * y i l := by
        symm
        exact
          rowObjective_eq_of_mem_uncapacitated_facility_location_assignments_for_openings
            c hy.feasible hij
  have hassignmentLe :
      ∑ i, ∑ j, c i j * y' i j ≤ ∑ i, ∑ j, c i j * y i j := by
    -- Summing the rowwise inequalities gives the global assignment-profit inequality.
    exact Finset.sum_le_sum fun i _ ↦ hrowLe i
  -- The opening-cost term is constant because the opening vector `x` is fixed.
  calc
    uncapacitated_facility_location_objective c f (y', x) =
        (∑ i, ∑ j, c i j * y' i j) - ∑ j, f j * x j := by
          rw [uncapacitated_facility_location_objective_mk]
    _ ≤ (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j := by
      exact sub_le_sub_right hassignmentLe (∑ j, f j * x j)
    _ = uncapacitated_facility_location_objective c f (y, x) := by
      rw [uncapacitated_facility_location_objective_mk]

/-- Helper for Exercise 8.12: specializing the subgradient method to the uncapacitated
facility-location
Lagrangian dual uses the Proposition 8.7 decisions `x(λ)` and `y(λ)`, the subgradient
`g_i(λ) = 1 - ∑_j y_ij(λ)`, and the update
`λ_i^+ = λ_i - step * (1 - ∑_j y_ij(λ))`, which is the Chapter 8 `subgradient_step`
specialized to `facility_location_subgradient c f lam`. -/
theorem exercise_8_12_subgradient_specialization
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (step : ℝ) :
    facility_location_subgradient c f lam =
      (fun i ↦ 1 - ∑ j, lagrangian_relaxation_assignment_decision c f lam i j) ∧
      subgradient_step lam (facility_location_subgradient c f lam) step =
        (fun i ↦
          lam i - step * (1 - ∑ j, lagrangian_relaxation_assignment_decision c f lam i j)) :=
  by
  constructor <;> ext i <;> rfl

/-- Exercise 8.12 (2). If, after fixing the opening variables to the Proposition 8.7 values
`x_j(λ)`, an assignment `y` sends each customer to an open facility maximizing `c_ij` among the
 open facilities, then `(y, x(λ))` is feasible for `(8.5)` and `y` maximizes the original
 objective among all assignments feasible with those opening variables fixed. -/
theorem exercise_8_12_fixed_opening_best_solution
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (y : Fin m → Fin n → ℝ)
    (hy :
      IsGreedyFacilityLocationAssignmentForOpenings
        c
        (lagrangian_relaxation_open_decision c f lam)
        y) :
    y ∈
        uncapacitated_facility_location_assignments_for_openings
          (lagrangian_relaxation_open_decision c f lam) ∧
      IsMaxOn
        (fun y' ↦
          uncapacitated_facility_location_objective c f
            (y', lagrangian_relaxation_open_decision c f lam))
        (uncapacitated_facility_location_assignments_for_openings
          (lagrangian_relaxation_open_decision c f lam))
        y := by
  constructor
  · -- The greedy assignment hypothesis already carries feasibility for the fixed openings.
    exact hy.feasible
  · -- Reuse the generic fixed-opening optimality statement at `x = x(λ)`.
    simpa using hy.isMaxOnObjective (f := f)

/-- Helper for Exercise 8.12: under the fixed-opening assignment hypothesis from part (2), the
objective value of `(y, x(λ))` is a lower bound on the optimal value of `(8.5)`. -/
theorem exercise_8_12_fixed_opening_lower_bound
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (y : Fin m → Fin n → ℝ)
    (hy :
      IsGreedyFacilityLocationAssignmentForOpenings
        c
        (lagrangian_relaxation_open_decision c f lam)
        y) :
    ((uncapacitated_facility_location_objective c f
        (y, lagrangian_relaxation_open_decision c f lam) : ℝ) : WithBot ℝ) ≤
      uncapacitated_facility_location_integer_value c f := by
  let x := lagrangian_relaxation_open_decision c f lam
  have hxyMem : (y, x) ∈ uncapacitated_facility_location_integer_feasible_set := by
    exact (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mp hy.feasible
  have hIntegerBdd :
      BddAbove
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
          uncapacitated_facility_location_integer_feasible_set) := by
    rcases facilityLocationLpImage_bddAbove (m := m) (n := n) c f with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rintro _ ⟨xy, hxy, rfl⟩
    -- Restrict the LP upper bound from Proposition 8.8 to the integer-feasible subset.
    exact
      hu
        ⟨xy,
          mem_uncapacitated_facility_location_lp_feasible_set_of_mem_integer_feasible_set hxy,
          rfl⟩
  -- Insert the current feasible integer point into the supremum defining the integer optimum.
  rw [uncapacitated_facility_location_integer_value_eq_sSup]
  exact le_csSup hIntegerBdd ⟨(y, x), hxyMem, rfl⟩

/-- Helper for Exercise 8.12: the lower bound from part (3) gives an additional stopping
criterion for
the subgradient method: if it reaches the current Lagrangian upper bound `z_LR(λ)`, then the
current fixed-opening solution is already optimal for `(8.5)`. -/
theorem exercise_8_12_stopping_criterion
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (y : Fin m → Fin n → ℝ)
    (hlower :
      ((uncapacitated_facility_location_objective c f
          (y, lagrangian_relaxation_open_decision c f lam) : ℝ) : WithBot ℝ) ≤
        uncapacitated_facility_location_integer_value c f)
    (hupper :
      uncapacitated_facility_location_integer_value c f ≤
        ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) : WithBot ℝ))
    (hstop :
      ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) : WithBot ℝ) ≤
        ((uncapacitated_facility_location_objective c f
            (y, lagrangian_relaxation_open_decision c f lam) : ℝ) : WithBot ℝ)) :
    ((uncapacitated_facility_location_objective c f
        (y, lagrangian_relaxation_open_decision c f lam) : ℝ) : WithBot ℝ) =
      uncapacitated_facility_location_integer_value c f := by
  apply le_antisymm
  · exact hlower
  · exact le_trans hupper hstop

end Exercise812
