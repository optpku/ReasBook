/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_8
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_12

open scoped BigOperators

-- Domain sampling note:
-- * core/canonical convex-geometry owner for extreme points: `Set.extremePoints ℝ`
-- * core/canonical polyhedral-ray owner: `IsExtremeRayOfPolyhedron`
-- * chapter-local facility-location owners reused here:
--   `uncapacitated_facility_location_integer_feasible_set` and
--   `uncapacitated_facility_location_objective`
-- This file keeps the source-facing Exercise 8.20 Benders objects and rewrites only the exact
-- duplicate owner layer to those canonical declarations.
-- Semantic recall note: LeanSearch confirms `SameRay` and
-- `exists_nonneg_right_iff_sameRay` as the canonical ray API used below.

section Exercise820

variable {m n : ℕ}

/-- The common feasible set of the customer-specific Benders subproblems after fixing the opening
vector `x`. Each customer shares the same assignment simplex cut by the site-opening bounds
`y_j ≤ x_j`. -/
def uncapacitated_facility_location_customer_subproblem_feasible_set
    (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {yi |
    (∑ j, yi j = 1) ∧
      (∀ j, yi j ≤ x j) ∧
      ∀ j, 0 ≤ yi j}

/-- Membership in `uncapacitated_facility_location_customer_subproblem_feasible_set x` means
precisely that the row vector sums to `1`, respects the opening bounds `x`, and is nonnegative.
-/
theorem mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff
    {x : Fin n → ℝ}
    {yi : Fin n → ℝ} :
    yi ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x ↔
      (∑ j, yi j = 1) ∧
        (∀ j, yi j ≤ x j) ∧
        ∀ j, 0 ≤ yi j :=
  Iff.rfl

/-- The value `z_LP(x)` of the Benders subproblem for the uncapacitated facility-location problem,
represented as an infimum in `WithTop ℝ` so that infeasible subproblems have value `⊤`. -/
noncomputable def uncapacitated_facility_location_benders_subproblem_value
    (c : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) : WithTop ℝ :=
  sInf
    ((fun y : Fin m → Fin n → ℝ ↦
        (((∑ i, ∑ j, c i j * y i j) : ℝ) : WithTop ℝ)) ''
      {y | ∀ i, y i ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x})

/-- The value `z_LP^i(x)` of the customer-specific subproblem for customer `i`, again recorded in
`WithTop ℝ` so that infeasibility is represented by `⊤`. -/
noncomputable def uncapacitated_facility_location_customer_subproblem_value
    (c : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (i : Fin m) : WithTop ℝ :=
  sInf
    ((fun yi : Fin n → ℝ ↦
        (((∑ j, c i j * yi j) : ℝ) : WithTop ℝ)) ''
      uncapacitated_facility_location_customer_subproblem_feasible_set x)

/-- The dual polyhedron
`Q_i = {(u_i,w_i) ∈ ℝ × ℝ_+^n | u_i - w_{ij} ≤ c_{ij} for all j}` attached to the `i`th customer.
-/
def uncapacitated_facility_location_dual_polyhedron
    (ci : Fin n → ℝ) : Set (ℝ × (Fin n → ℝ)) :=
  {uw |
    (∀ j, 0 ≤ uw.2 j) ∧
      ∀ j, uw.1 - uw.2 j ≤ ci j}

/-- Membership in `uncapacitated_facility_location_dual_polyhedron ci` is exactly nonnegativity of
the `w`-coordinates together with the inequalities `u - w_j ≤ c_j`. -/
theorem mem_uncapacitated_facility_location_dual_polyhedron_iff
    {ci : Fin n → ℝ}
    {uw : ℝ × (Fin n → ℝ)} :
    uw ∈ uncapacitated_facility_location_dual_polyhedron ci ↔
      (∀ j, 0 ≤ uw.2 j) ∧
        ∀ j, uw.1 - uw.2 j ≤ ci j :=
  Iff.rfl

/-- The candidate extreme point of `Q_i` indexed by facility `k`. -/
def uncapacitated_facility_location_dual_extreme_point_candidate
    (ci : Fin n → ℝ)
    (k : Fin n) : ℝ × (Fin n → ℝ) :=
  (ci k, fun j ↦ max (ci k - ci j) 0)

/-- The common covering ray `(1, 1, ..., 1)` of the recession cone of `Q_i`. -/
def uncapacitated_facility_location_dual_covering_ray_candidate :
    ℝ × (Fin n → ℝ) :=
  (1, fun _ ↦ (1 : ℝ))

/-- The negative-`u` ray `(-1, 0, ..., 0)` of the recession cone of `Q_i`. -/
def uncapacitated_facility_location_dual_negative_u_ray_candidate :
    ℝ × (Fin n → ℝ) :=
  (-1, fun _ ↦ (0 : ℝ))

/-- The coordinate ray `(0, e^k)` of the recession cone of `Q_i`. -/
def uncapacitated_facility_location_dual_coordinate_ray_candidate
    (k : Fin n) : ℝ × (Fin n → ℝ) :=
  (0, fun j ↦ if j = k then (1 : ℝ) else 0)

/-- The source-feasible set of Exercise 8.20: assignment equations, linking inequalities,
nonnegative assignment variables, and binary opening variables. -/
def uncapacitated_facility_location_problem_feasible_set :
    Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy |
    (∀ i, ∑ j, xy.1 i j = 1) ∧
      (∀ i j, xy.1 i j ≤ xy.2 j) ∧
      (∀ i j, 0 ≤ xy.1 i j) ∧
        ∀ j, xy.2 j = 0 ∨ xy.2 j = 1}

/-- Membership in `uncapacitated_facility_location_problem_feasible_set` is exactly the
source-facing formulation from Exercise 8.20, with continuous assignment variables `y` and binary
opening variables `x`. -/
theorem mem_uncapacitated_facility_location_problem_feasible_set_iff
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    xy ∈ uncapacitated_facility_location_problem_feasible_set ↔
      (∀ i, ∑ j, xy.1 i j = 1) ∧
        (∀ i j, xy.1 i j ≤ xy.2 j) ∧
        (∀ i j, 0 ≤ xy.1 i j) ∧
          ∀ j, xy.2 j = 0 ∨ xy.2 j = 1 :=
  Iff.rfl

/-- The optimal value of the source-facing uncapacitated facility-location problem from
Exercise 8.20, recorded in `WithTop ℝ` so that infeasibility is represented by `⊤`. -/
noncomputable def uncapacitated_facility_location_problem_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : WithTop ℝ :=
  sInf
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((-uncapacitated_facility_location_objective
            (fun i j ↦ -c i j)
            f
            xy : ℝ) : WithTop ℝ)) ''
      uncapacitated_facility_location_problem_feasible_set)

/-- Unfolding `uncapacitated_facility_location_problem_value c f` recovers the infimum of the
cost objective over the source-facing feasible set from Exercise 8.20. -/
theorem uncapacitated_facility_location_problem_value_eq_sInf
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_problem_value c f =
      sInf
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            ((-uncapacitated_facility_location_objective
                (fun i j ↦ -c i j)
                f
                xy : ℝ) : WithTop ℝ)) ''
          uncapacitated_facility_location_problem_feasible_set) :=
  rfl

/-- The feasible set of the Benders reformulation from Exercise 8.20, with first component `η`
and second component `x`. -/
def uncapacitated_facility_location_benders_reformulation_feasible_set
    (c : Fin m → Fin n → ℝ) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {etax |
    (∀ j, etax.2 j = 0 ∨ etax.2 j = 1) ∧
      (∀ i k, c i k - ∑ j, max (c i k - c i j) 0 * etax.2 j ≤ etax.1 i) ∧
      1 ≤ ∑ j, etax.2 j}

/-- Membership in `uncapacitated_facility_location_benders_reformulation_feasible_set c`
expands to the binary opening condition, the Benders optimality cuts, and the feasibility cut
`∑ j, x_j ≥ 1`. -/
theorem mem_uncapacitated_facility_location_benders_reformulation_feasible_set_iff
    {c : Fin m → Fin n → ℝ}
    {etax : (Fin m → ℝ) × (Fin n → ℝ)} :
    etax ∈ uncapacitated_facility_location_benders_reformulation_feasible_set c ↔
      (∀ j, etax.2 j = 0 ∨ etax.2 j = 1) ∧
        (∀ i k, c i k - ∑ j, max (c i k - c i j) 0 * etax.2 j ≤ etax.1 i) ∧
        1 ≤ ∑ j, etax.2 j :=
  Iff.rfl

/-- The objective `∑_i η_i + ∑_j f_j x_j` of the Benders reformulation from Exercise 8.20. -/
def uncapacitated_facility_location_benders_reformulation_objective
    (f : Fin n → ℝ)
    (etax : (Fin m → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ i, etax.1 i) + ∑ j, f j * etax.2 j

/-- The optimal value of the explicit Benders reformulation from Exercise 8.20, again recorded in
`WithTop ℝ`. -/
noncomputable def uncapacitated_facility_location_benders_reformulation_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : WithTop ℝ :=
  sInf
    ((fun etax : (Fin m → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_benders_reformulation_objective f etax : ℝ) :
          WithTop ℝ)) ''
      uncapacitated_facility_location_benders_reformulation_feasible_set c)

/-- Helper for Exercise 8.20: the basis assignment sending one customer entirely to facility `k`.
-/
def openFacilityIndicator
    (k : Fin n) : Fin n → ℝ :=
  fun j ↦ if j = k then 1 else 0

/-- Helper for Exercise 8.20: the indicator row for facility `k` has unit sum. -/
theorem sum_openFacilityIndicator
    (k : Fin n) :
    ∑ j, openFacilityIndicator k j = 1 := by
  -- The indicator row has exactly one nonzero entry, namely the chosen facility.
  simp [openFacilityIndicator]

/-- Helper for Exercise 8.20: the assignment cost of the indicator row at facility `k` is the
single coefficient `c i k`. -/
theorem rowCost_openFacilityIndicator
    (c : Fin m → Fin n → ℝ)
    (i : Fin m)
    (k : Fin n) :
    ∑ j, c i j * openFacilityIndicator k j = c i k := by
  -- The indicator row removes every term except the one at `k`.
  simp [openFacilityIndicator]

/-- Helper for Exercise 8.20: if facility `k` is open, then the indicator row at `k` is feasible
for the one-customer subproblem with opening vector `x`. -/
theorem openFacilityIndicator_mem_customer_subproblem_feasible_set
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    {k : Fin n}
    (hk : x k = 1) :
    openFacilityIndicator k ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x :=
  by
  -- The indicator row has unit sum, stays below `x` because `k` is open, and is nonnegative.
  rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff]
  refine ⟨sum_openFacilityIndicator k, ?_, ?_⟩
  · intro j
    by_cases hj : j = k
    · simp [openFacilityIndicator, hj, hk]
    · rcases hx j with hxj | hxj <;> simp [openFacilityIndicator, hj, hxj]
  · intro j
    by_cases hj : j = k
    · simp [openFacilityIndicator, hj]
    · simp [openFacilityIndicator, hj]

/-- Helper for Exercise 8.20: if every facility is closed, then the one-customer feasible set is
empty. -/
theorem customerSubproblemFeasibleSet_eq_empty_of_all_facilities_closed
    {x : Fin n → ℝ}
    (hxClosed : ∀ j, x j = 0) :
    uncapacitated_facility_location_customer_subproblem_feasible_set x = ∅ := by
  -- With all openings zero, nonnegativity and the upper bounds force every row entry to vanish,
  -- contradicting the unit-sum equation.
  ext yi
  constructor
  · intro hyi
    rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff] at hyi
    rcases hyi with ⟨hsum, hle, hnonneg⟩
    have hallZero : ∀ j, yi j = 0 := by
      intro j
      have hyLeZero : yi j ≤ 0 := by
        simpa [hxClosed j] using hle j
      linarith [hnonneg j, hyLeZero]
    have hsumZero : ∑ j, yi j = 0 := by
      simp [hallZero]
    exact False.elim (by linarith)
  · intro hyi
    cases hyi

/-- Helper for Exercise 8.20: a binary opening vector with `∑_j x_j ≥ 1` has at least one open
facility. -/
theorem exists_openFacility_of_binary_and_sum_ge_one
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    (hsum : 1 ≤ ∑ j, x j) :
    ∃ j, x j = 1 := by
  by_contra hnone
  have hallZero : ∀ j, x j = 0 := by
    intro j
    rcases hx j with hxj | hxj
    · exact hxj
    · exact False.elim (hnone ⟨j, hxj⟩)
  have hsumZero : ∑ j, x j = 0 := by
    simp [hallZero]
  linarith

/-- Helper for Exercise 8.20: for each customer, a binary opening vector with
`∑_j x_j ≥ 1` contains an open facility minimizing the customer cost among all open facilities.
-/
theorem existsOpenFacilityArgmin
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    (hsum : 1 ≤ ∑ j, x j)
    (i : Fin m) :
    ∃ k : Fin n, x k = 1 ∧ ∀ j, x j = 1 → c i k ≤ c i j := by
  classical
  obtain ⟨j0, hj0⟩ := exists_openFacility_of_binary_and_sum_ge_one hx hsum
  let openFacilities := {j : Fin n // x j = 1}
  have hopenFacilities : Nonempty openFacilities := ⟨⟨j0, hj0⟩⟩
  obtain ⟨k, hkMin⟩ := Finite.exists_min (fun j : openFacilities ↦ c i j)
  refine ⟨k, k.property, ?_⟩
  intro j hj
  exact hkMin ⟨j, hj⟩

/-- Helper for Exercise 8.20: an open minimizing facility gives a lower bound on every feasible
one-customer assignment cost. -/
theorem openArgmin_le_customerRowCost
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    {i : Fin m}
    {k : Fin n}
    (hkOpen : x k = 1)
    (hkMin : ∀ j, x j = 1 → c i k ≤ c i j)
    {yi : Fin n → ℝ}
    (hyi : yi ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x) :
    c i k ≤ ∑ j, c i j * yi j := by
  let _ := hkOpen
  rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff] at hyi
  rcases hyi with ⟨hsum, hle, hnonneg⟩
  have htermLe : ∀ j, c i k * yi j ≤ c i j * yi j := by
    intro j
    rcases hx j with hxj | hxj
    · have hyjLeZero : yi j ≤ 0 := by
        simpa [hxj] using hle j
      have hyjZero : yi j = 0 := by
        linarith [hnonneg j, hyjLeZero]
      simp [hyjZero]
    · exact mul_le_mul_of_nonneg_right (hkMin j hxj) (hnonneg j)
  -- Rewrite the minimizing cost as a weighted sum over the feasible row and compare termwise.
  calc
    c i k = c i k * ∑ j, yi j := by rw [hsum, mul_one]
    _ = ∑ j, c i k * yi j := by
          simpa using (Finset.mul_sum Finset.univ (fun j ↦ yi j) (c i k))
    _ ≤ ∑ j, c i j * yi j := Finset.sum_le_sum fun j _ ↦ htermLe j

/-- Helper for Exercise 8.20: the one-customer subproblem value equals the open-facility minimum
cost once an open minimizing facility `k` is fixed. -/
theorem customerSubproblemValue_eq_of_openArgmin
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    {i : Fin m}
    {k : Fin n}
    (hkOpen : x k = 1)
    (hkMin : ∀ j, x j = 1 → c i k ≤ c i j) :
    uncapacitated_facility_location_customer_subproblem_value c x i =
      ((c i k : ℝ) : WithTop ℝ) := by
  -- The indicator row attains the minimizing open cost, and every feasible row costs at least
  -- that much, so the infimum is squeezed to `c i k`.
  rw [uncapacitated_facility_location_customer_subproblem_value]
  let S : Set (WithTop ℝ) :=
    ((fun yi : Fin n → ℝ ↦ (((∑ j, c i j * yi j) : ℝ) : WithTop ℝ)) ''
      uncapacitated_facility_location_customer_subproblem_feasible_set x)
  change sInf S = ((c i k : ℝ) : WithTop ℝ)
  have hmem : ((c i k : ℝ) : WithTop ℝ) ∈ S := by
    refine ⟨openFacilityIndicator k,
      openFacilityIndicator_mem_customer_subproblem_feasible_set hx hkOpen, ?_⟩
    simp [rowCost_openFacilityIndicator]
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_ ?_
  · exact ⟨((c i k : ℝ) : WithTop ℝ), hmem⟩
  · intro a ha
    rcases ha with ⟨yi, hyi, rfl⟩
    have hle : (c i k : ℝ) ≤ ∑ j, c i j * yi j :=
      openArgmin_le_customerRowCost c hx hkOpen hkMin hyi
    have hle' : ((c i k : ℝ) : WithTop ℝ) ≤ (((∑ j, c i j * yi j : ℝ)) : WithTop ℝ) := by
      exact (WithTop.coe_le_coe).2 hle
    simpa [WithTop.coe_sum] using hle'
  · intro w hw
    refine ⟨((c i k : ℝ) : WithTop ℝ), hmem, hw⟩

/-- Helper for Exercise 8.20: if every facility is closed, then the one-customer subproblem value
is infeasible and therefore equals `⊤`. -/
theorem customerSubproblemValue_eq_top_of_all_facilities_closed
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hxClosed : ∀ j, x j = 0)
    (i : Fin m) :
    uncapacitated_facility_location_customer_subproblem_value c x i = ⊤ := by
  -- The customer feasible set is empty, so the image in `WithTop` is empty as well.
  rw [uncapacitated_facility_location_customer_subproblem_value,
    customerSubproblemFeasibleSet_eq_empty_of_all_facilities_closed hxClosed]
  simp

/-- Helper for Exercise 8.20: every Benders cut for customer `i` collapses to the single open
minimum bound `c i k ≤ η` once `k` is an open minimizing facility. -/
theorem customerCuts_iff_geOpenArgminCost
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    {i : Fin m}
    {k : Fin n}
    (hkOpen : x k = 1)
    (hkMin : ∀ j, x j = 1 → c i k ≤ c i j)
    {η : ℝ} :
    (∀ k', c i k' - ∑ j, max (c i k' - c i j) 0 * x j ≤ η) ↔ c i k ≤ η := by
  constructor
  · intro hcuts
    have hkCut := hcuts k
    have hsumZero :
        ∑ j, max (c i k - c i j) 0 * x j = 0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rcases hx j with hxj | hxj
      · simp [hxj]
      · have hdiff : c i k - c i j ≤ 0 := by
          linarith [hkMin j hxj]
        simp [hxj, max_eq_right hdiff]
    simpa [hsumZero] using hkCut
  · intro hkEta k'
    have hcoord :
        max (c i k' - c i k) 0 ≤
          ∑ j, max (c i k' - c i j) 0 * x j := by
      have htermNonneg :
          ∀ j, 0 ≤ max (c i k' - c i j) 0 * x j := by
        intro j
        rcases hx j with hxj | hxj <;> simp [hxj]
      have hsingle :
          max (c i k' - c i k) 0 * x k ≤
            ∑ j, max (c i k' - c i j) 0 * x j := by
        exact Finset.single_le_sum (fun j _ ↦ htermNonneg j) (by simp)
      simpa [hkOpen] using hsingle
    have hcutToK :
        c i k' - ∑ j, max (c i k' - c i j) 0 * x j ≤ c i k := by
      refine le_trans (sub_le_sub_left hcoord _) ?_
      by_cases hcase : c i k' - c i k ≤ 0
      · have hmax : max (c i k' - c i k) 0 = 0 := max_eq_right hcase
        rw [hmax]
        linarith
      · have hnonneg : 0 ≤ c i k' - c i k := le_of_not_ge hcase
        have hmax : max (c i k' - c i k) 0 = c i k' - c i k := max_eq_left hnonneg
        rw [hmax]
        ring_nf
        exact le_rfl
    exact le_trans hcutToK hkEta

/-- Helper for Exercise 8.20: a feasible customer row bounds every Benders cut from above by its
assignment cost. -/
theorem customerCut_le_customerRowCost
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    {i : Fin m}
    {yi : Fin n → ℝ}
    (hyi : yi ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x)
    (k : Fin n) :
    c i k - ∑ j, max (c i k - c i j) 0 * x j ≤ ∑ j, c i j * yi j := by
  rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff] at hyi
  rcases hyi with ⟨hsum, hle, hnonneg⟩
  have htermLe :
      ∀ j, (c i k - c i j) * yi j ≤ max (c i k - c i j) 0 * x j := by
    intro j
    by_cases hcase : c i k - c i j ≤ 0
    · have hleftLeZero : (c i k - c i j) * yi j ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hcase (hnonneg j)
      have hrightNonneg : 0 ≤ max (c i k - c i j) 0 * x j := by
        rcases hx j with hxj | hxj <;> simp [hxj]
      linarith
    · have hnonneg : 0 ≤ c i k - c i j := le_of_not_ge hcase
      have hmax : max (c i k - c i j) 0 = c i k - c i j := max_eq_left hnonneg
      rw [hmax]
      exact mul_le_mul_of_nonneg_left (hle j) hnonneg
  have hsumLe :
      ∑ j, (c i k - c i j) * yi j ≤
        ∑ j, max (c i k - c i j) 0 * x j := by
    exact Finset.sum_le_sum fun j _ ↦ htermLe j
  have hrewrite :
      c i k - ∑ j, (c i k - c i j) * yi j =
        ∑ j, c i j * yi j := by
    have hmul :
        c i k * ∑ j, yi j = ∑ j, c i k * yi j := by
      simpa using (Finset.mul_sum Finset.univ (fun j ↦ yi j) (c i k))
    calc
      c i k - ∑ j, (c i k - c i j) * yi j =
          c i k * ∑ j, yi j - ∑ j, (c i k - c i j) * yi j := by
            rw [hsum, mul_one]
      _ = ∑ j, c i k * yi j - ∑ j, (c i k - c i j) * yi j := by
            rw [hmul]
      _ = ∑ j, (c i k * yi j - (c i k - c i j) * yi j) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ j, c i j * yi j := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            ring
  -- Compare the cut coefficients termwise, then simplify the remaining algebra with the row sum.
  calc
    c i k - ∑ j, max (c i k - c i j) 0 * x j ≤
        c i k - ∑ j, (c i k - c i j) * yi j := by
          exact sub_le_sub_left hsumLe _
    _ = ∑ j, c i j * yi j := hrewrite

/-- Helper for Exercise 8.20: a globally minimizing facility for customer `i` bounds every
feasible one-customer assignment cost from below. -/
theorem globalMin_le_customerRowCost
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    {i : Fin m}
    {k : Fin n}
    (hkMin : ∀ j, c i k ≤ c i j)
    {yi : Fin n → ℝ}
    (hyi : yi ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x) :
    c i k ≤ ∑ j, c i j * yi j := by
  rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff] at hyi
  rcases hyi with ⟨hsum, _, hnonneg⟩
  have htermLe : ∀ j, c i k * yi j ≤ c i j * yi j := by
    intro j
    exact mul_le_mul_of_nonneg_right (hkMin j) (hnonneg j)
  -- Rewrite the minimizing cost as a weighted sum over the feasible row and compare termwise.
  calc
    c i k = c i k * ∑ j, yi j := by rw [hsum, mul_one]
    _ = ∑ j, c i k * yi j := by
          simpa using (Finset.mul_sum Finset.univ (fun j ↦ yi j) (c i k))
    _ ≤ ∑ j, c i j * yi j := Finset.sum_le_sum fun j _ ↦ htermLe j

/-- Helper for Exercise 8.20: every feasible integer solution opens at least one facility when the
customer set is nonempty. -/
theorem exists_openFacility_of_mem_integer_feasible_set
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hm : 0 < m)
    (hxy : (y, x) ∈ uncapacitated_facility_location_integer_feasible_set) :
    ∃ j, x j = 1 := by
  let i0 : Fin m := ⟨0, hm⟩
  have hyMem : y ∈ uncapacitated_facility_location_assignments_for_openings x := by
    exact (mem_uncapacitated_facility_location_assignments_for_openings_iff x).2 hxy
  obtain ⟨j, hij⟩ :=
    exists_assignment_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings
      hyMem i0
  exact ⟨j,
    opening_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings hyMem hij⟩

/-- Helper for Exercise 8.20: once a binary opening vector contains an open facility `k`, the sum
of the opening variables is at least `1`. -/
theorem one_le_sum_of_binary_of_openFacility
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    {k : Fin n}
    (hk : x k = 1) :
    1 ≤ ∑ j, x j := by
  -- The open coordinate contributes `1`, and every binary coordinate is nonnegative.
  have hnonneg : ∀ j, 0 ≤ x j := by
    intro j
    rcases hx j with hxj | hxj <;> simp [hxj]
  have hsingle : x k ≤ ∑ j, x j := by
    exact Finset.single_le_sum (fun j _ ↦ hnonneg j) (by simp)
  simpa [hk] using hsingle

/-- Helper for Exercise 8.20: each row of an integer-feasible assignment is feasible for the
corresponding customer subproblem with the same opening vector. -/
theorem row_mem_customer_subproblem_feasible_set_of_mem_integer_feasible_set
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hxy : (y, x) ∈ uncapacitated_facility_location_integer_feasible_set)
    (i : Fin m) :
    y i ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x := by
  -- Repackage the `i`th assignment row into the customer-subproblem owner.
  rcases (mem_uncapacitated_facility_location_integer_feasible_set_iff.mp hxy) with
    ⟨hrow, hlink, hbinary, _⟩
  rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff]
  refine ⟨hrow i, ?_, ?_⟩
  · intro j
    exact hlink i j
  · intro j
    change 0 ≤ (y, x).1 i j
    exact nonneg_of_mem_uncapacitated_facility_location_integer_feasible_set hxy i j

/-- Helper for Exercise 8.20: fixing an open minimizing facility for every customer determines the
global Benders subproblem value. -/
theorem globalSubproblemValue_eq_of_openArgminFamily
    (c : Fin m → Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    (k : Fin m → Fin n)
    (hkOpen : ∀ i, x (k i) = 1)
    (hkMin : ∀ i j, x j = 1 → c i (k i) ≤ c i j) :
    uncapacitated_facility_location_benders_subproblem_value c x =
      (((∑ i, c i (k i)) : ℝ) : WithTop ℝ) := by
  -- The rowwise indicator assignment attains the claimed value, and every feasible matrix has
  -- row costs bounded below by the same chosen open minima.
  rw [uncapacitated_facility_location_benders_subproblem_value]
  let S : Set (WithTop ℝ) :=
    ((fun y : Fin m → Fin n → ℝ ↦
        (((∑ i, ∑ j, c i j * y i j) : ℝ) : WithTop ℝ)) ''
      {y | ∀ i, y i ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x})
  change sInf S = (((∑ i, c i (k i)) : ℝ) : WithTop ℝ)
  have hmem : ((((∑ i, c i (k i)) : ℝ) : WithTop ℝ)) ∈ S := by
    refine ⟨fun i ↦ openFacilityIndicator (k i), ?_, ?_⟩
    · intro i
      exact openFacilityIndicator_mem_customer_subproblem_feasible_set hx (hkOpen i)
    · simp [rowCost_openFacilityIndicator]
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_ ?_
  · exact ⟨(((∑ i, c i (k i)) : ℝ) : WithTop ℝ), hmem⟩
  · intro a ha
    rcases ha with ⟨y, hy, rfl⟩
    have hrow :
        ∀ i, c i (k i) ≤ ∑ j, c i j * y i j := by
      intro i
      exact openArgmin_le_customerRowCost c hx (hkOpen i) (hkMin i) (hy i)
    have hsum :
        ∑ i, c i (k i) ≤ ∑ i, ∑ j, c i j * y i j := by
      exact Finset.sum_le_sum fun i _ ↦ hrow i
    exact (WithTop.coe_le_coe).2 hsum
  · intro w hw
    exact ⟨(((∑ i, c i (k i)) : ℝ) : WithTop ℝ), hmem, hw⟩

/-- Helper for Exercise 8.20: if every facility is closed and there is at least one customer, then
the global Benders subproblem is infeasible and its value is `⊤`. -/
theorem globalSubproblemValue_eq_top_of_allFacilitiesClosed
    (c : Fin m → Fin n → ℝ)
    (hm : 0 < m)
    {x : Fin n → ℝ}
    (hxClosed : ∀ j, x j = 0) :
    uncapacitated_facility_location_benders_subproblem_value c x = ⊤ := by
  -- The first customer already has an empty feasible row set, so no global assignment survives.
  let i0 : Fin m := ⟨0, hm⟩
  rw [uncapacitated_facility_location_benders_subproblem_value]
  have hempty :
      {y : Fin m → Fin n → ℝ |
          ∀ i, y i ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x} = ∅ := by
    ext y
    constructor
    · intro hy
      have hy0 := hy i0
      rw [customerSubproblemFeasibleSet_eq_empty_of_all_facilities_closed hxClosed] at hy0
      exact False.elim hy0
    · intro hy
      cases hy
  rw [hempty]
  simp

/-- Helper for Exercise 8.20: choosing one open facility for each customer and assigning that
customer entirely to it yields an integer-feasible solution of the original formulation. -/
theorem openArgminIndicatorAssignment_mem_integer_feasible_set
    {x : Fin n → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1)
    (k : Fin m → Fin n)
    (hkOpen : ∀ i, x (k i) = 1) :
    ((fun i ↦ openFacilityIndicator (k i)), x) ∈
      uncapacitated_facility_location_integer_feasible_set := by
  -- Each row is an indicator assignment with unit sum, it respects the opening bounds, and both
  -- assignment and opening variables remain binary.
  rw [mem_uncapacitated_facility_location_integer_feasible_set_iff]
  refine ⟨?_, ?_, ?_, hx⟩
  · intro i
    exact sum_openFacilityIndicator (k i)
  · intro i j
    by_cases hj : j = k i
    · simp [openFacilityIndicator, hj, hkOpen i]
    · rcases hx j with hxj | hxj <;> simp [openFacilityIndicator, hj, hxj]
  · intro i j
    by_cases hj : j = k i
    · right
      simp [openFacilityIndicator, hj]
    · left
      simp [openFacilityIndicator, hj]

/-- Helper for Exercise 8.20: a positive weighted sum of two nonnegative reals vanishes only when
both summands vanish. -/
lemma positive_weighted_sum_eq_zero_of_nonneg
    {μ₁ μ₂ a b : ℝ}
    (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hsum : μ₁ * a + μ₂ * b = 0) :
    a = 0 ∧ b = 0 := by
  -- Nonnegative summands can add up to zero only if both are already zero.
  have hμ₁a_nonneg : 0 ≤ μ₁ * a :=
    mul_nonneg (le_of_lt hμ₁) ha
  have hμ₂b_nonneg : 0 ≤ μ₂ * b :=
    mul_nonneg (le_of_lt hμ₂) hb
  have hμ₁a_zero : μ₁ * a = 0 := by
    linarith
  have hμ₂b_zero : μ₂ * b = 0 := by
    linarith
  constructor
  · exact (mul_eq_zero.mp hμ₁a_zero).resolve_left hμ₁.ne'
  · exact (mul_eq_zero.mp hμ₂b_zero).resolve_left hμ₂.ne'

/-- Helper for Exercise 8.20: every point is the midpoint of its symmetric perturbation pair. -/
lemma mem_openSegment_of_symmetric_perturbation
    (x d : ℝ × (Fin n → ℝ)) :
    x ∈ openSegment ℝ (x + d) (x - d) := by
  -- The midpoint parameter `1 / 2` recovers the original point from symmetric endpoints.
  rw [openSegment_eq_image_lineMap]
  refine ⟨(1 / 2 : ℝ), by constructor <;> norm_num, ?_⟩
  ext i <;> simp [AffineMap.lineMap_apply_module] <;> ring

/-- Helper for Exercise 8.20: each candidate point indexed by `k` belongs to the dual polyhedron.
-/
lemma dualExtremePointCandidate_mem_dualPolyhedron
    (ci : Fin n → ℝ)
    (k : Fin n) :
    uncapacitated_facility_location_dual_extreme_point_candidate ci k ∈
      uncapacitated_facility_location_dual_polyhedron ci := by
  -- The candidate has nonnegative `w`-coordinates and satisfies `u - w_j ≤ c_j` coordinatewise.
  rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
  constructor
  · intro j
    simp [uncapacitated_facility_location_dual_extreme_point_candidate]
  · intro j
    by_cases hkj : ci k - ci j ≤ 0
    · have hmax : max (ci k - ci j) 0 = 0 := max_eq_right hkj
      simp [uncapacitated_facility_location_dual_extreme_point_candidate, hmax]
      linarith
    · have hnonneg : 0 ≤ ci k - ci j := le_of_not_ge hkj
      have hmax : max (ci k - ci j) 0 = ci k - ci j := max_eq_left hnonneg
      simp [uncapacitated_facility_location_dual_extreme_point_candidate, hmax]

/-- Helper for Exercise 8.20: the recession cone of the dual polyhedron is exactly the homogeneous
system `w_j ≥ 0` and `u ≤ w_j` for every `j`. -/
lemma memRecessionCone_dualPolyhedron_iff
    (ci : Fin n → ℝ)
    {r : ℝ × (Fin n → ℝ)} :
    r ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) ↔
      (∀ j, 0 ≤ r.2 j) ∧ ∀ j, r.1 ≤ r.2 j := by
  constructor
  · intro hr
    rw [mem_recessionCone_iff] at hr
    constructor
    · intro j
      -- Translate the active candidate point at `j` and read off the `w_j` nonnegativity.
      have htranslate :=
        hr (dualExtremePointCandidate_mem_dualPolyhedron ci j) 1 zero_le_one
      rw [mem_uncapacitated_facility_location_dual_polyhedron_iff] at htranslate
      simpa [uncapacitated_facility_location_dual_extreme_point_candidate] using (htranslate.1 j)
    · intro j
      -- The same active candidate point makes the `j`th inequality tight, so translation yields
      -- the homogeneous inequality `r.1 ≤ r.2 j`.
      have htranslate :=
        hr (dualExtremePointCandidate_mem_dualPolyhedron ci j) 1 zero_le_one
      rw [mem_uncapacitated_facility_location_dual_polyhedron_iff] at htranslate
      have hj := htranslate.2 j
      simpa [uncapacitated_facility_location_dual_extreme_point_candidate] using hj
  · rintro ⟨hrNonneg, hrBound⟩
    rw [mem_recessionCone_iff]
    intro q hq a ha
    rw [mem_uncapacitated_facility_location_dual_polyhedron_iff] at hq ⊢
    constructor
    · intro j
      -- Nonnegative translations preserve the nonnegative `w`-coordinates.
      simpa [Pi.add_apply, Pi.smul_apply, mul_comm] using
        add_nonneg (hq.1 j) (mul_nonneg ha (hrNonneg j))
    · intro j
      -- The defining inequalities gain the nonpositive increment `a * (r.1 - r.2 j)`.
      have hdir : a * (r.1 - r.2 j) ≤ 0 := by
        have hdiff : r.1 - r.2 j ≤ 0 := sub_nonpos.mpr (hrBound j)
        exact mul_nonpos_of_nonneg_of_nonpos ha hdiff
      have htranslated :
          q.1 + a * r.1 - (q.2 j + a * r.2 j) ≤ ci j := by
        linarith [hq.2 j, hdir]
      simpa [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_comm, mul_left_comm, mul_assoc] using htranslated

/-- Part (1) of Exercise 8.20. The Benders subproblem value decomposes as the sum of the `m`
customer-specific subproblem values
`z_LP(x) = ∑_i z_LP^i(x)` for every binary opening vector `x ∈ {0,1}^n`. -/
theorem exercise_8_20_benders_subproblem_decomposes_by_customer
    (c : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ)
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    uncapacitated_facility_location_benders_subproblem_value c x =
      ∑ i, uncapacitated_facility_location_customer_subproblem_value c x i := by
  by_cases hopen : ∃ j, x j = 1
  · classical
    -- Choose one open minimizing facility for each customer and compare both sides to the same
    -- fixed-opening cost formula.
    obtain ⟨j0, hj0⟩ := hopen
    have hsum : 1 ≤ ∑ j, x j :=
      one_le_sum_of_binary_of_openFacility hx hj0
    have hkExists :
        ∀ i : Fin m, ∃ k : Fin n, x k = 1 ∧ ∀ j, x j = 1 → c i k ≤ c i j := by
      intro i
      exact existsOpenFacilityArgmin c hx hsum i
    choose k hkOpen hkMin using hkExists
    have hglobal :
        uncapacitated_facility_location_benders_subproblem_value c x =
          (((∑ i, c i (k i)) : ℝ) : WithTop ℝ) :=
      globalSubproblemValue_eq_of_openArgminFamily c hx k hkOpen hkMin
    have hrow :
        ∀ i,
          uncapacitated_facility_location_customer_subproblem_value c x i =
            ((c i (k i) : ℝ) : WithTop ℝ) := by
      intro i
      exact customerSubproblemValue_eq_of_openArgmin c hx (hkOpen i) (hkMin i)
    -- Route correction: compare the global and rowwise infima through one shared sum of chosen
    -- open argmin costs instead of repeating `WithTop` normalization on each branch.
    calc
      uncapacitated_facility_location_benders_subproblem_value c x =
          (((∑ i, c i (k i)) : ℝ) : WithTop ℝ) := hglobal
      _ = ∑ i, uncapacitated_facility_location_customer_subproblem_value c x i := by
            simp [hrow]
  · have hxClosed : ∀ j, x j = 0 := by
      intro j
      rcases hx j with hxj | hxj
      · exact hxj
      · exact False.elim (hopen ⟨j, hxj⟩)
    by_cases hm : m = 0
    · -- With no customers, both the global subproblem and the sum of row values collapse to `0`.
      subst hm
      simp [uncapacitated_facility_location_benders_subproblem_value,
        uncapacitated_facility_location_customer_subproblem_value]
    · have hmPos : 0 < m := Nat.pos_of_ne_zero hm
      have hglobalTop :
          uncapacitated_facility_location_benders_subproblem_value c x = ⊤ :=
        globalSubproblemValue_eq_top_of_allFacilitiesClosed c hmPos hxClosed
      have hrowTop :
          ∀ i, uncapacitated_facility_location_customer_subproblem_value c x i = ⊤ := by
        intro i
        exact customerSubproblemValue_eq_top_of_all_facilities_closed c hxClosed i
      let i0 : Fin m := ⟨0, hmPos⟩
      have hsumTop :
          (∑ i, uncapacitated_facility_location_customer_subproblem_value c x i) = ⊤ := by
        -- One customer row already contributes `⊤`, so the whole sum is `⊤`.
        have hi0 : i0 ∈ Finset.univ := by
          simp [i0]
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hi0, hrowTop i0, top_add]
      exact hglobalTop.trans hsumTop.symm

/-- Helper for Exercise 8.20: an extreme point of the dual polyhedron has no slack above the
canonical profile `w_j = max (u - c_j) 0`. -/
lemma dualExtremePoint_w_eq_profile_of_mem_extremePoints
    (ci : Fin n → ℝ)
    {q : ℝ × (Fin n → ℝ)}
    (hq : q ∈ (uncapacitated_facility_location_dual_polyhedron ci).extremePoints ℝ) :
    ∀ j, q.2 j = max (q.1 - ci j) 0 := by
  rcases (mem_extremePoints_iff_left.mp hq) with ⟨hqPoly, hqExtreme⟩
  intro j
  have hprofile_le : max (q.1 - ci j) 0 ≤ q.2 j := by
    refine max_le_iff.mpr ⟨?_, hqPoly.1 j⟩
    linarith [hqPoly.2 j]
  by_contra hneq
  have hneq' : max (q.1 - ci j) 0 ≠ q.2 j := by
    intro hEq
    exact hneq hEq.symm
  have hstrict : max (q.1 - ci j) 0 < q.2 j := lt_of_le_of_ne hprofile_le hneq'
  let δ : ℝ := (q.2 j - max (q.1 - ci j) 0) / 2
  let d : ℝ × (Fin n → ℝ) := (0, fun l ↦ if l = j then δ else 0)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_le_coord : δ ≤ q.2 j := by
    have hmax_nonneg : 0 ≤ max (q.1 - ci j) 0 := le_max_right _ _
    dsimp [δ]
    linarith
  have hyMem : q + d ∈ uncapacitated_facility_location_dual_polyhedron ci := by
    rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
    constructor
    · intro l
      by_cases hlj : l = j
      · simpa [d, hlj] using add_nonneg (hqPoly.1 j) hδ_nonneg
      · simpa [d, hlj] using hqPoly.1 l
    · intro l
      by_cases hlj : l = j
      · have hbound : q.1 - (q.2 j + δ) ≤ q.1 - q.2 j := by
          linarith
        simpa [d, hlj] using le_trans hbound (hqPoly.2 j)
      · simpa [d, hlj] using hqPoly.2 l
  have hzMem : q - d ∈ uncapacitated_facility_location_dual_polyhedron ci := by
    rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
    constructor
    · intro l
      by_cases hlj : l = j
      · simpa [d, hlj] using sub_nonneg.mpr hδ_le_coord
      · simpa [d, hlj] using hqPoly.1 l
    · intro l
      by_cases hlj : l = j
      · have hδ_le_slack : δ ≤ q.2 j - max (q.1 - ci j) 0 := by
          dsimp [δ]
          linarith
        have hbound_to_max : q.1 - (q.2 j - δ) ≤ q.1 - max (q.1 - ci j) 0 := by
          linarith
        have hmax_bound : q.1 - max (q.1 - ci j) 0 ≤ ci j := by
          by_cases hcase : q.1 - ci j ≤ 0
          · have hmax : max (q.1 - ci j) 0 = 0 := max_eq_right hcase
            rw [hmax]
            linarith
          · have hnonneg : 0 ≤ q.1 - ci j := le_of_not_ge hcase
            have hmax : max (q.1 - ci j) 0 = q.1 - ci j := max_eq_left hnonneg
            rw [hmax]
            linarith
        simpa [d, hlj] using le_trans hbound_to_max hmax_bound
      · simpa [d, hlj] using hqPoly.2 l
  have hyEq : q + d = q :=
    hqExtreme (q + d) hyMem (q - d) hzMem (mem_openSegment_of_symmetric_perturbation q d)
  have hcoordEq : q.2 j + δ = q.2 j := by
    simpa [d] using congrArg (fun p ↦ p.2 j) hyEq
  linarith

/-- Helper for Exercise 8.20: once `n > 0`, the head coordinate of an extreme point of the dual
polyhedron must equal one of the finitely many costs `c_j`. -/
lemma dualExtremePoint_head_eq_cost_of_mem_extremePoints
    (ci : Fin n → ℝ)
    (hn : 0 < n)
    {q : ℝ × (Fin n → ℝ)}
    (hq : q ∈ (uncapacitated_facility_location_dual_polyhedron ci).extremePoints ℝ) :
    ∃ k : Fin n, q.1 = ci k := by
  classical
  rcases (mem_extremePoints_iff_left.mp hq) with ⟨hqPoly, hqExtreme⟩
  have hprofile := dualExtremePoint_w_eq_profile_of_mem_extremePoints ci hq
  by_contra hnone
  have hallNe : ∀ j : Fin n, q.1 ≠ ci j := by
    intro j hEq
    exact hnone ⟨j, hEq⟩
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k0, hk0Min⟩ := Finite.exists_min (fun j : Fin n ↦ |q.1 - ci j|)
  have hgap_pos : 0 < |q.1 - ci k0| := by
    exact abs_pos.mpr (sub_ne_zero.mpr (hallNe k0))
  let ε : ℝ := |q.1 - ci k0| / 2
  let d : ℝ × (Fin n → ℝ) := (ε, fun j ↦ if ci j < q.1 then ε else 0)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_abs : ∀ j : Fin n, ε < |q.1 - ci j| := by
    intro j
    dsimp [ε]
    linarith [hk0Min j, hgap_pos]
  have hyMem : q + d ∈ uncapacitated_facility_location_dual_polyhedron ci := by
    rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
    constructor
    · intro j
      by_cases hj : ci j < q.1
      · simpa [d, hj] using add_nonneg (hqPoly.1 j) (le_of_lt hε_pos)
      · have hqj_zero : q.2 j = 0 := by
          have hcase : q.1 - ci j ≤ 0 := by
            exact sub_nonpos.mpr (le_of_not_gt hj)
          simp [hprofile j, max_eq_right hcase]
        simp [d, hj, hqj_zero]
    · intro j
      by_cases hj : ci j < q.1
      · simpa [d, hj, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hqPoly.2 j
      · have hji : q.1 < ci j := by
          have hneq : q.1 ≠ ci j := hallNe j
          exact lt_of_le_of_ne (le_of_not_gt hj) hneq
        have hqj_zero : q.2 j = 0 := by
          have hcase : q.1 - ci j ≤ 0 := by linarith
          simp [hprofile j, max_eq_right hcase]
        have hε_lt_gap : ε < ci j - q.1 := by
          have habs : |q.1 - ci j| = ci j - q.1 := by
            have hneg : q.1 - ci j < 0 := by linarith
            calc
              |q.1 - ci j| = -(q.1 - ci j) := abs_of_neg hneg
              _ = ci j - q.1 := by ring
          have hεlt := hε_lt_abs j
          rw [habs] at hεlt
          exact hεlt
        have hsum_lt : q.1 + ε < ci j := by
          linarith
        have hsum_le : q.1 + ε ≤ ci j := le_of_lt hsum_lt
        simpa [d, hj, hqj_zero] using hsum_le
  have hzMem : q - d ∈ uncapacitated_facility_location_dual_polyhedron ci := by
    rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
    constructor
    · intro j
      by_cases hj : ci j < q.1
      · have hgap : ε < q.1 - ci j := by
          have hnonneg : 0 ≤ q.1 - ci j := by linarith
          have habs : |q.1 - ci j| = q.1 - ci j := by
            exact abs_of_nonneg hnonneg
          have hεlt := hε_lt_abs j
          rw [habs] at hεlt
          exact hεlt
        have hqj : q.2 j = q.1 - ci j := by
          have hnonneg : 0 ≤ q.1 - ci j := by linarith
          simp [hprofile j, max_eq_left hnonneg]
        have hnonneg : 0 ≤ q.2 j - ε := by
          rw [hqj]
          linarith
        simpa [d, hj] using hnonneg
      · simpa [d, hj] using hqPoly.1 j
    · intro j
      by_cases hj : ci j < q.1
      · simpa [d, hj, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hqPoly.2 j
      · have hji : q.1 < ci j := by
          have hneq : q.1 ≠ ci j := hallNe j
          exact lt_of_le_of_ne (le_of_not_gt hj) hneq
        have hqj_zero : q.2 j = 0 := by
          have hcase : q.1 - ci j ≤ 0 := by linarith
          simp [hprofile j, max_eq_right hcase]
        have hsum_lt : q.1 - ε < ci j := by
          linarith [hε_pos, hji]
        have hsum_le : q.1 - ε ≤ ci j := le_of_lt hsum_lt
        simpa [d, hj, hqj_zero] using hsum_le
  -- Route correction: instead of searching for an active zero coordinate, perturb the head
  -- coordinate by a half-minimum gap while preserving the sign pattern of the max-profile.
  have hyEq : q + d = q :=
    hqExtreme (q + d) hyMem (q - d) hzMem (mem_openSegment_of_symmetric_perturbation q d)
  have hheadEq : q.1 + ε = q.1 := by
    simpa [d] using congrArg Prod.fst hyEq
  linarith

/-- Part (2) of Exercise 8.20. The extreme points of
`Q_i = {(u_i,w_i) ∈ ℝ × ℝ_+^n | u_i - w_{ij} ≤ c_{ij}}` are exactly the `n` points indexed by
`k`, namely `(c_{ik}, ((c_{ik} - c_{ij})^+)_j)`. -/
theorem exercise_8_20_dual_polyhedron_extreme_points
    (ci : Fin n → ℝ)
    (q : ℝ × (Fin n → ℝ)) :
    q ∈ (uncapacitated_facility_location_dual_polyhedron ci).extremePoints ℝ ↔
      ∃ k : Fin n,
        q = uncapacitated_facility_location_dual_extreme_point_candidate ci k := by
  by_cases hn0 : n = 0
  · subst hn0
    constructor
    · intro hq
      rcases (mem_extremePoints_iff_left.mp hq) with ⟨hqPoly, hqExtreme⟩
      let d : ℝ × (Fin 0 → ℝ) := (1, 0)
      have hyMem : q + d ∈ uncapacitated_facility_location_dual_polyhedron ci := by
        rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
        constructor <;> intro j <;> exact Fin.elim0 j
      have hzMem : q - d ∈ uncapacitated_facility_location_dual_polyhedron ci := by
        rw [mem_uncapacitated_facility_location_dual_polyhedron_iff]
        constructor <;> intro j <;> exact Fin.elim0 j
      have hyEq : q + d = q :=
        hqExtreme (q + d) hyMem (q - d) hzMem (mem_openSegment_of_symmetric_perturbation q d)
      have hheadEq : q.1 + 1 = q.1 := by
        simpa [d] using congrArg Prod.fst hyEq
      linarith
    · rintro ⟨k, _⟩
      exact Fin.elim0 k
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    constructor
    · intro hq
      obtain ⟨k, hk⟩ := dualExtremePoint_head_eq_cost_of_mem_extremePoints ci hn hq
      have hprofile := dualExtremePoint_w_eq_profile_of_mem_extremePoints ci hq
      refine ⟨k, ?_⟩
      ext j <;> simp [uncapacitated_facility_location_dual_extreme_point_candidate, hk, hprofile]
    · rintro ⟨k, rfl⟩
      rw [mem_extremePoints_iff_left]
      constructor
      · exact dualExtremePointCandidate_mem_dualPolyhedron ci k
      · intro y hy z hz hseg
        rw [mem_uncapacitated_facility_location_dual_polyhedron_iff] at hy hz
        rw [openSegment_eq_image_lineMap] at hseg
        rcases hseg with ⟨a, ha, hline⟩
        have hleft_pos : 0 < 1 - a := by
          linarith [ha.2]
        have hkCoord :
            (1 - a) * y.2 k + a * z.2 k = 0 := by
          simpa [AffineMap.lineMap_apply_module,
            uncapacitated_facility_location_dual_extreme_point_candidate] using
            congrArg (fun p ↦ p.2 k) hline
        have hkZero := positive_weighted_sum_eq_zero_of_nonneg
          hleft_pos ha.1 (hy.1 k) (hz.1 k) hkCoord
        have hyk_zero : y.2 k = 0 := hkZero.1
        have hzk_zero : z.2 k = 0 := hkZero.2
        have hyHeadLe : y.1 ≤ ci k := by
          simpa [hyk_zero] using hy.2 k
        have hzHeadLe : z.1 ≤ ci k := by
          simpa [hzk_zero] using hz.2 k
        have hheadCoord :
            (1 - a) * (ci k - y.1) + a * (ci k - z.1) = 0 := by
          have hhead :
              (1 - a) * y.1 + a * z.1 = ci k := by
            simpa [AffineMap.lineMap_apply_module,
              uncapacitated_facility_location_dual_extreme_point_candidate] using
              congrArg Prod.fst hline
          linarith
        have hheadZero := positive_weighted_sum_eq_zero_of_nonneg
          hleft_pos ha.1 (sub_nonneg.mpr hyHeadLe) (sub_nonneg.mpr hzHeadLe) hheadCoord
        have hyHeadEq : y.1 = ci k := by linarith
        have hzHeadEq : z.1 = ci k := by linarith
        refine Prod.ext hyHeadEq ?_
        funext j
        by_cases hkj : ci k ≤ ci j
        · have hcoord :
              (1 - a) * y.2 j + a * z.2 j = 0 := by
            have hmax : max (ci k - ci j) 0 = 0 := max_eq_right (sub_nonpos.mpr hkj)
            simpa [AffineMap.lineMap_apply_module,
              uncapacitated_facility_location_dual_extreme_point_candidate, hmax] using
              congrArg (fun p ↦ p.2 j) hline
          have hzero := positive_weighted_sum_eq_zero_of_nonneg
            hleft_pos ha.1 (hy.1 j) (hz.1 j) hcoord
          simp [uncapacitated_facility_location_dual_extreme_point_candidate,
            max_eq_right (sub_nonpos.mpr hkj), hzero.1]
        · have hkj' : ci j < ci k := by
            linarith
          have hySlackNonneg : 0 ≤ y.2 j - (ci k - ci j) := by
            linarith [hy.2 j, hyHeadEq]
          have hzSlackNonneg : 0 ≤ z.2 j - (ci k - ci j) := by
            linarith [hz.2 j, hzHeadEq]
          have hcoord :
              (1 - a) * (y.2 j - (ci k - ci j)) +
                a * (z.2 j - (ci k - ci j)) = 0 := by
            have hmax : max (ci k - ci j) 0 = ci k - ci j := max_eq_left (sub_nonneg.mpr hkj'.le)
            have hcoord' :
                (1 - a) * y.2 j + a * z.2 j = ci k - ci j := by
              simpa [AffineMap.lineMap_apply_module,
                uncapacitated_facility_location_dual_extreme_point_candidate, hmax] using
                congrArg (fun p ↦ p.2 j) hline
            linarith
          have hzero := positive_weighted_sum_eq_zero_of_nonneg
            hleft_pos ha.1 hySlackNonneg hzSlackNonneg hcoord
          have hyj_eq : y.2 j = ci k - ci j := by linarith
          simp [uncapacitated_facility_location_dual_extreme_point_candidate,
            max_eq_left (sub_nonneg.mpr hkj'.le), hyj_eq]

/-- Helper for Exercise 8.20: an extreme ray of the dual polyhedron belongs to its recession cone.
-/
lemma dualExtremeRay_mem_recessionCone
    {ci : Fin n → ℝ}
    {r : ℝ × (Fin n → ℝ)}
    (hr : IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r) :
    r ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
  -- Unpack the extreme-subset predicate and evaluate it at the generating vector itself.
  rw [isExtremeRayOfPolyhedron_iff] at hr
  have hr_edge :
      IsEdgeOf
        (recessionCone (uncapacitated_facility_location_dual_polyhedron ci))
        (PointedCone.hull ℝ ({r} : Set (ℝ × (Fin n → ℝ))) : Set (ℝ × (Fin n → ℝ))) :=
    (isExtremeRayOfCone_iff).1 hr
  have hr_hull :
      r ∈ (PointedCone.hull ℝ ({r} : Set (ℝ × (Fin n → ℝ))) : Set (ℝ × (Fin n → ℝ))) := by
    exact PointedCone.subset_hull (by simp)
  exact hr_edge.isExtreme.1 hr_hull

/-- Helper for Exercise 8.20: an extreme ray of the dual recession cone cannot admit a proper
conic decomposition into two distinct cone rays. -/
lemma dualExtremeRay_not_properConicCombination
    {ci : Fin n → ℝ}
    {r : ℝ × (Fin n → ℝ)}
    (hr : r ≠ 0)
    (hExt : IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r) :
    ¬ ProperConicCombinationOfDistinctConeRays
      (recessionCone (uncapacitated_facility_location_dual_polyhedron ci)) r := by
  -- Route correction: use the Chapter 3 cone criterion once, after extracting recession
  -- membership, instead of repeatedly unfolding the extreme-ray owner in each branch.
  have hr_mem := dualExtremeRay_mem_recessionCone hExt
  rw [isExtremeRayOfPolyhedron_iff] at hExt
  exact
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      ⟨recessionPointedCone ℝ (uncapacitated_facility_location_dual_polyhedron ci), rfl⟩
      hr_mem hr).1 hExt

/-- Helper for Exercise 8.20: the covering candidate belongs to the recession cone of the dual
polyhedron. -/
lemma dualCoveringRayCandidate_mem_recessionCone
    (ci : Fin n → ℝ) :
    uncapacitated_facility_location_dual_covering_ray_candidate ∈
      recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
  -- The common covering ray satisfies `w_j = 1` and `u = 1`, so every homogeneous inequality is
  -- tight.
  rw [memRecessionCone_dualPolyhedron_iff]
  constructor <;> intro j <;>
    simp [uncapacitated_facility_location_dual_covering_ray_candidate]

/-- Helper for Exercise 8.20: the negative-`u` candidate belongs to the recession cone of the dual
polyhedron. -/
lemma dualNegativeURayCandidate_mem_recessionCone
    (ci : Fin n → ℝ) :
    uncapacitated_facility_location_dual_negative_u_ray_candidate ∈
      recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
  -- The negative-`u` ray has vanishing `w`-coordinates and negative head, so `u ≤ w_j` is
  -- automatic.
  rw [memRecessionCone_dualPolyhedron_iff]
  constructor <;> intro j <;>
    simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]

/-- Helper for Exercise 8.20: each coordinate candidate belongs to the recession cone of the dual
polyhedron. -/
lemma dualCoordinateRayCandidate_mem_recessionCone
    (ci : Fin n → ℝ)
    (k : Fin n) :
    uncapacitated_facility_location_dual_coordinate_ray_candidate k ∈
      recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
  -- A coordinate ray has head `0` and one nonnegative unit tail entry, so it stays in the
  -- homogeneous system.
  rw [memRecessionCone_dualPolyhedron_iff]
  constructor
  · intro j
    by_cases hj : j = k <;>
      simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hj]
  · intro j
    by_cases hj : j = k <;>
      simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hj]

/-- Helper for Exercise 8.20: a nonzero head-zero direction cannot lie on the covering ray. -/
lemma dualCoveringRay_not_sameRay_of_head_zero
    {q : ℝ × (Fin n → ℝ)}
    (hq_ne : q ≠ 0)
    (hq0 : q.1 = 0) :
    ¬ SameRay ℝ q
      (uncapacitated_facility_location_dual_covering_ray_candidate : ℝ × (Fin n → ℝ)) := by
  -- Any same-ray multiple of the covering ray has strictly matching first coordinate, so a
  -- head-zero vector would have to vanish.
  intro hsame
  have hcover_ne :
      (uncapacitated_facility_location_dual_covering_ray_candidate : ℝ × (Fin n → ℝ)) ≠ 0 := by
    simp [uncapacitated_facility_location_dual_covering_ray_candidate]
  rcases hsame.exists_nonneg_right hcover_ne with ⟨a, ha, hqeq⟩
  have hhead : q.1 = a := by
    simpa [uncapacitated_facility_location_dual_covering_ray_candidate] using
      congrArg Prod.fst hqeq
  have ha_zero : a = 0 := by
    linarith [hq0, hhead]
  apply hq_ne
  rw [hqeq, ha_zero]
  simp

/-- Helper for Exercise 8.20: a nonzero head-zero direction cannot lie on the negative-`u` ray.
-/
lemma dualNegativeURay_not_sameRay_of_head_zero
    {q : ℝ × (Fin n → ℝ)}
    (hq_ne : q ≠ 0)
    (hq0 : q.1 = 0) :
    ¬ SameRay ℝ q
      (uncapacitated_facility_location_dual_negative_u_ray_candidate : ℝ × (Fin n → ℝ)) := by
  -- Any same-ray multiple of the negative-`u` ray has negative first coordinate unless the scalar
  -- is zero, which would again force the whole vector to vanish.
  intro hsame
  have hneg_ne :
      (uncapacitated_facility_location_dual_negative_u_ray_candidate : ℝ × (Fin n → ℝ)) ≠ 0 := by
    simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
  rcases hsame.exists_nonneg_right hneg_ne with ⟨a, ha, hqeq⟩
  have hhead : q.1 = -a := by
    simpa [uncapacitated_facility_location_dual_negative_u_ray_candidate] using
      congrArg Prod.fst hqeq
  have ha_zero : a = 0 := by
    linarith [hq0, hhead]
  apply hq_ne
  rw [hqeq, ha_zero]
  simp

/-- Helper for Exercise 8.20: the covering and negative-`u` candidates generate different rays.
-/
lemma dualCoveringRay_not_sameRay_negativeU :
    ¬ SameRay ℝ
      (uncapacitated_facility_location_dual_covering_ray_candidate : ℝ × (Fin n → ℝ))
      (uncapacitated_facility_location_dual_negative_u_ray_candidate : ℝ × (Fin n → ℝ)) := by
  -- Their first coordinates have opposite signs, so no nonnegative scaling can identify them.
  intro hsame
  have hneg_ne :
      (uncapacitated_facility_location_dual_negative_u_ray_candidate : ℝ × (Fin n → ℝ)) ≠ 0 := by
    simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
  rcases hsame.exists_nonneg_right hneg_ne with ⟨a, ha, hEq⟩
  have hhead : (1 : ℝ) = -a := by
    simpa [uncapacitated_facility_location_dual_covering_ray_candidate,
      uncapacitated_facility_location_dual_negative_u_ray_candidate] using
      congrArg Prod.fst hEq
  linarith

/-- Helper for Exercise 8.20: the covering candidate is an extreme ray of the dual polyhedron.
-/
lemma dualCoveringRayCandidate_isExtremeRay
    (ci : Fin n → ℝ)
    (hn : 0 < n) :
    IsExtremeRayOfPolyhedron
      (uncapacitated_facility_location_dual_polyhedron ci)
      (uncapacitated_facility_location_dual_covering_ray_candidate : ℝ × (Fin n → ℝ)) := by
  rw [isExtremeRayOfPolyhedron_iff]
  have hmem := dualCoveringRayCandidate_mem_recessionCone ci
  have hne :
      (uncapacitated_facility_location_dual_covering_ray_candidate : ℝ × (Fin n → ℝ)) ≠ 0 := by
    simp [uncapacitated_facility_location_dual_covering_ray_candidate]
  refine
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      ⟨recessionPointedCone ℝ (uncapacitated_facility_location_dual_polyhedron ci), rfl⟩
      hmem hne).2 ?_
  rintro ⟨u, v, hu, hv, hu_ne, hv_ne, huv_not, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
  change u ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) at hu
  change v ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) at hv
  rw [memRecessionCone_dualPolyhedron_iff] at hu hv
  let j0 : Fin n := ⟨0, hn⟩
  have hhead : μ₁ * u.1 + μ₂ * v.1 = 1 := by
    simpa [uncapacitated_facility_location_dual_covering_ray_candidate] using
      (congrArg Prod.fst hdecomp).symm
  have htail :
      ∀ j : Fin n, μ₁ * u.2 j + μ₂ * v.2 j = 1 := by
    intro j
    simpa [uncapacitated_facility_location_dual_covering_ray_candidate,
      Pi.add_apply, Pi.smul_apply] using
      (congrArg (fun p ↦ p.2 j) hdecomp).symm
  have hu_eq : ∀ j : Fin n, u.2 j = u.1 := by
    intro j
    have hgap :
        μ₁ * (u.2 j - u.1) + μ₂ * (v.2 j - v.1) = 0 := by
      linarith [hhead, htail j]
    have hzero := positive_weighted_sum_eq_zero_of_nonneg
      hμ₁ hμ₂ (sub_nonneg.mpr (hu.2 j)) (sub_nonneg.mpr (hv.2 j)) hgap
    linarith [hzero.1]
  have hv_eq : ∀ j : Fin n, v.2 j = v.1 := by
    intro j
    have hgap :
        μ₁ * (u.2 j - u.1) + μ₂ * (v.2 j - v.1) = 0 := by
      linarith [hhead, htail j]
    have hzero := positive_weighted_sum_eq_zero_of_nonneg
      hμ₁ hμ₂ (sub_nonneg.mpr (hu.2 j)) (sub_nonneg.mpr (hv.2 j)) hgap
    linarith [hzero.2]
  have hu_head_nonneg : 0 ≤ u.1 := by
    simpa [hu_eq j0] using hu.1 j0
  have hv_head_nonneg : 0 ≤ v.1 := by
    simpa [hv_eq j0] using hv.1 j0
  have hu_head_ne : u.1 ≠ 0 := by
    intro hu0
    apply hu_ne
    refine Prod.ext hu0 ?_
    funext j
    simp [hu_eq j, hu0]
  have hv_head_ne : v.1 ≠ 0 := by
    intro hv0
    apply hv_ne
    refine Prod.ext hv0 ?_
    funext j
    simp [hv_eq j, hv0]
  have hu_head_pos : 0 < u.1 := lt_of_le_of_ne hu_head_nonneg hu_head_ne.symm
  have hv_head_pos : 0 < v.1 := lt_of_le_of_ne hv_head_nonneg hv_head_ne.symm
  have hu_same :
      SameRay ℝ u uncapacitated_facility_location_dual_covering_ray_candidate := by
    have hu_repr :
        u = u.1 • uncapacitated_facility_location_dual_covering_ray_candidate := by
      refine Prod.ext ?_ ?_
      · simp [uncapacitated_facility_location_dual_covering_ray_candidate]
      · funext j
        simp [uncapacitated_facility_location_dual_covering_ray_candidate, hu_eq j]
    rw [hu_repr]
    exact SameRay.sameRay_pos_smul_left
      uncapacitated_facility_location_dual_covering_ray_candidate hu_head_pos
  have hv_same :
      SameRay ℝ v uncapacitated_facility_location_dual_covering_ray_candidate := by
    have hv_repr :
        v = v.1 • uncapacitated_facility_location_dual_covering_ray_candidate := by
      refine Prod.ext ?_ ?_
      · simp [uncapacitated_facility_location_dual_covering_ray_candidate]
      · funext j
        simp [uncapacitated_facility_location_dual_covering_ray_candidate, hv_eq j]
    rw [hv_repr]
    exact SameRay.sameRay_pos_smul_left
      uncapacitated_facility_location_dual_covering_ray_candidate hv_head_pos
  have huv_same : SameRay ℝ u v :=
    SameRay.trans hu_same hv_same.symm (fun hzero ↦ False.elim (hne hzero))
  exact huv_not huv_same

/-- Helper for Exercise 8.20: the negative-`u` candidate is an extreme ray of the dual
polyhedron. -/
lemma dualNegativeURayCandidate_isExtremeRay
    (ci : Fin n → ℝ)
    (hn : 0 < n) :
    IsExtremeRayOfPolyhedron
      (uncapacitated_facility_location_dual_polyhedron ci)
      (uncapacitated_facility_location_dual_negative_u_ray_candidate : ℝ × (Fin n → ℝ)) := by
  rw [isExtremeRayOfPolyhedron_iff]
  have hmem := dualNegativeURayCandidate_mem_recessionCone ci
  have hne :
      (uncapacitated_facility_location_dual_negative_u_ray_candidate : ℝ × (Fin n → ℝ)) ≠ 0 := by
    simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
  refine
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      ⟨recessionPointedCone ℝ (uncapacitated_facility_location_dual_polyhedron ci), rfl⟩
      hmem hne).2 ?_
  rintro ⟨u, v, hu, hv, hu_ne, hv_ne, huv_not, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
  change u ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) at hu
  change v ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) at hv
  rw [memRecessionCone_dualPolyhedron_iff] at hu hv
  let j0 : Fin n := ⟨0, hn⟩
  have hhead : μ₁ * u.1 + μ₂ * v.1 = -1 := by
    simpa [uncapacitated_facility_location_dual_negative_u_ray_candidate] using
      (congrArg Prod.fst hdecomp).symm
  have htail_zero :
      ∀ j : Fin n, μ₁ * u.2 j + μ₂ * v.2 j = 0 := by
    intro j
    simpa [uncapacitated_facility_location_dual_negative_u_ray_candidate,
      Pi.add_apply, Pi.smul_apply] using
      (congrArg (fun p ↦ p.2 j) hdecomp).symm
  have hu_zero : ∀ j : Fin n, u.2 j = 0 := by
    intro j
    have hzero := positive_weighted_sum_eq_zero_of_nonneg
      hμ₁ hμ₂ (hu.1 j) (hv.1 j) (htail_zero j)
    exact hzero.1
  have hv_zero : ∀ j : Fin n, v.2 j = 0 := by
    intro j
    have hzero := positive_weighted_sum_eq_zero_of_nonneg
      hμ₁ hμ₂ (hu.1 j) (hv.1 j) (htail_zero j)
    exact hzero.2
  have hu_head_nonpos : u.1 ≤ 0 := by
    simpa [hu_zero j0] using hu.2 j0
  have hv_head_nonpos : v.1 ≤ 0 := by
    simpa [hv_zero j0] using hv.2 j0
  have hu_head_ne : u.1 ≠ 0 := by
    intro hu0
    apply hu_ne
    refine Prod.ext hu0 ?_
    funext j
    simp [hu_zero j]
  have hv_head_ne : v.1 ≠ 0 := by
    intro hv0
    apply hv_ne
    refine Prod.ext hv0 ?_
    funext j
    simp [hv_zero j]
  have hu_head_neg : u.1 < 0 := lt_of_le_of_ne hu_head_nonpos hu_head_ne
  have hv_head_neg : v.1 < 0 := lt_of_le_of_ne hv_head_nonpos hv_head_ne
  have hu_same :
      SameRay ℝ u uncapacitated_facility_location_dual_negative_u_ray_candidate := by
    have hu_repr :
        u = (-u.1) • uncapacitated_facility_location_dual_negative_u_ray_candidate := by
      refine Prod.ext ?_ ?_
      · simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
      · funext j
        simp [uncapacitated_facility_location_dual_negative_u_ray_candidate, hu_zero j]
    rw [hu_repr]
    exact SameRay.sameRay_pos_smul_left
      uncapacitated_facility_location_dual_negative_u_ray_candidate (by linarith)
  have hv_same :
      SameRay ℝ v uncapacitated_facility_location_dual_negative_u_ray_candidate := by
    have hv_repr :
        v = (-v.1) • uncapacitated_facility_location_dual_negative_u_ray_candidate := by
      refine Prod.ext ?_ ?_
      · simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
      · funext j
        simp [uncapacitated_facility_location_dual_negative_u_ray_candidate, hv_zero j]
    rw [hv_repr]
    exact SameRay.sameRay_pos_smul_left
      uncapacitated_facility_location_dual_negative_u_ray_candidate (by linarith)
  have huv_same : SameRay ℝ u v :=
    SameRay.trans hu_same hv_same.symm (fun hzero ↦ False.elim (hne hzero))
  exact huv_not huv_same

/-- Helper for Exercise 8.20: for `n > 1`, each coordinate candidate is an extreme ray of the dual
polyhedron. -/
lemma dualCoordinateRayCandidate_isExtremeRay
    (ci : Fin n → ℝ)
    {k : Fin n}
    (hn : 1 < n) :
    IsExtremeRayOfPolyhedron
      (uncapacitated_facility_location_dual_polyhedron ci)
      (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
  rw [isExtremeRayOfPolyhedron_iff]
  have hmem := dualCoordinateRayCandidate_mem_recessionCone ci k
  have hne : uncapacitated_facility_location_dual_coordinate_ray_candidate k ≠ 0 := by
    intro hzero
    have hcoord : ((uncapacitated_facility_location_dual_coordinate_ray_candidate k).2 k) = 0 := by
      simpa using congrArg (fun p ↦ p.2 k) hzero
    simp [uncapacitated_facility_location_dual_coordinate_ray_candidate] at hcoord
  refine
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      ⟨recessionPointedCone ℝ (uncapacitated_facility_location_dual_polyhedron ci), rfl⟩
      hmem hne).2 ?_
  rintro ⟨u, v, hu, hv, hu_ne, hv_ne, huv_not, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
  change u ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) at hu
  change v ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) at hv
  rw [memRecessionCone_dualPolyhedron_iff] at hu hv
  have hnontrivial : Nontrivial (Fin n) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    simpa using hn
  letI := hnontrivial
  obtain ⟨j0, hj0⟩ := exists_ne k
  have htail_zero :
      ∀ j : Fin n, j ≠ k → μ₁ * u.2 j + μ₂ * v.2 j = 0 := by
    intro j hj
    have hcoord :
        μ₁ * u.2 j + μ₂ * v.2 j =
          (uncapacitated_facility_location_dual_coordinate_ray_candidate k).2 j := by
      simpa [uncapacitated_facility_location_dual_coordinate_ray_candidate,
        Pi.add_apply, Pi.smul_apply] using
        (congrArg (fun p ↦ p.2 j) hdecomp).symm
    simpa [uncapacitated_facility_location_dual_coordinate_ray_candidate, hj] using hcoord
  have hu_zero_off : ∀ j : Fin n, j ≠ k → u.2 j = 0 := by
    intro j hj
    have hzero := positive_weighted_sum_eq_zero_of_nonneg
      hμ₁ hμ₂ (hu.1 j) (hv.1 j) (htail_zero j hj)
    exact hzero.1
  have hv_zero_off : ∀ j : Fin n, j ≠ k → v.2 j = 0 := by
    intro j hj
    have hzero := positive_weighted_sum_eq_zero_of_nonneg
      hμ₁ hμ₂ (hu.1 j) (hv.1 j) (htail_zero j hj)
    exact hzero.2
  have hu_head_nonpos : u.1 ≤ 0 := by
    simpa [hu_zero_off j0 hj0] using hu.2 j0
  have hv_head_nonpos : v.1 ≤ 0 := by
    simpa [hv_zero_off j0 hj0] using hv.2 j0
  have hhead_zero :
      μ₁ * (-u.1) + μ₂ * (-v.1) = 0 := by
    have hhead :
        μ₁ * u.1 + μ₂ * v.1 = 0 := by
      simpa [uncapacitated_facility_location_dual_coordinate_ray_candidate] using
        (congrArg Prod.fst hdecomp).symm
    linarith
  have hhead_terms := positive_weighted_sum_eq_zero_of_nonneg
    hμ₁ hμ₂ (by linarith) (by linarith) hhead_zero
  have hu_head_zero : u.1 = 0 := by linarith [hhead_terms.1]
  have hv_head_zero : v.1 = 0 := by linarith [hhead_terms.2]
  have hu_tail_ne : u.2 k ≠ 0 := by
    intro huk
    apply hu_ne
    refine Prod.ext hu_head_zero ?_
    funext j
    by_cases hj : j = k
    · subst hj
      simp [huk]
    · simp [hu_zero_off j hj]
  have hv_tail_ne : v.2 k ≠ 0 := by
    intro hvk
    apply hv_ne
    refine Prod.ext hv_head_zero ?_
    funext j
    by_cases hj : j = k
    · subst hj
      simp [hvk]
    · simp [hv_zero_off j hj]
  have hu_tail_pos : 0 < u.2 k := lt_of_le_of_ne (hu.1 k) hu_tail_ne.symm
  have hv_tail_pos : 0 < v.2 k := lt_of_le_of_ne (hv.1 k) hv_tail_ne.symm
  have hu_same :
      SameRay ℝ u (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
    have hu_repr :
        u = u.2 k • uncapacitated_facility_location_dual_coordinate_ray_candidate k := by
      refine Prod.ext ?_ ?_
      · simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hu_head_zero]
      · funext j
        by_cases hj : j = k
        · subst hj
          simp [uncapacitated_facility_location_dual_coordinate_ray_candidate]
        · simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hj, hu_zero_off j hj]
    rw [hu_repr]
    exact SameRay.sameRay_pos_smul_left
      (uncapacitated_facility_location_dual_coordinate_ray_candidate k) hu_tail_pos
  have hv_same :
      SameRay ℝ v (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
    have hv_repr :
        v = v.2 k • uncapacitated_facility_location_dual_coordinate_ray_candidate k := by
      refine Prod.ext ?_ ?_
      · simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hv_head_zero]
      · funext j
        by_cases hj : j = k
        · subst hj
          simp [uncapacitated_facility_location_dual_coordinate_ray_candidate]
        · simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hj, hv_zero_off j hj]
    rw [hv_repr]
    exact SameRay.sameRay_pos_smul_left
      (uncapacitated_facility_location_dual_coordinate_ray_candidate k) hv_tail_pos
  have huv_same : SameRay ℝ u v :=
    SameRay.trans hu_same hv_same.symm (fun hzero ↦ False.elim (hne hzero))
  exact huv_not huv_same

/-- Helper for Exercise 8.20: a positive-head extreme ray must lie on the covering ray. -/
lemma dualExtremeRay_sameRay_covering_of_head_pos
    (ci : Fin n → ℝ)
    {r : ℝ × (Fin n → ℝ)}
    (hr : r ≠ 0)
    (hExt : IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r)
    (hpos : 0 < r.1) :
    SameRay ℝ r uncapacitated_facility_location_dual_covering_ray_candidate := by
  have hr_mem := dualExtremeRay_mem_recessionCone hExt
  have hnotproper := dualExtremeRay_not_properConicCombination hr hExt
  rw [memRecessionCone_dualPolyhedron_iff] at hr_mem
  let q : ℝ × (Fin n → ℝ) := (0, fun j ↦ r.2 j - r.1)
  have hq_mem :
      q ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
    -- The positive-head remainder keeps head `0` and leaves only the nonnegative slacks.
    rw [memRecessionCone_dualPolyhedron_iff]
    constructor
    · intro j
      dsimp [q]
      linarith [hr_mem.2 j]
    · intro j
      dsimp [q]
      linarith [hr_mem.2 j]
  have hr_split :
      r = r.1 • uncapacitated_facility_location_dual_covering_ray_candidate + q := by
    refine Prod.ext ?_ ?_
    · simp [q, uncapacitated_facility_location_dual_covering_ray_candidate]
    · funext j
      simp [q, uncapacitated_facility_location_dual_covering_ray_candidate,
        Pi.add_apply, Pi.smul_apply]
  by_cases hq_zero : q = 0
  · -- Once the slack remainder vanishes, `r` is a positive multiple of the covering ray.
    have hr_repr : r = r.1 • uncapacitated_facility_location_dual_covering_ray_candidate := by
      simpa [hq_zero] using hr_split
    rw [hr_repr]
    exact SameRay.sameRay_pos_smul_left
      uncapacitated_facility_location_dual_covering_ray_candidate hpos
  · -- A nonzero remainder would give a forbidden proper conic decomposition.
    have hproper :
        ProperConicCombinationOfDistinctConeRays
          (recessionCone (uncapacitated_facility_location_dual_polyhedron ci)) r := by
      refine ⟨uncapacitated_facility_location_dual_covering_ray_candidate, q, ?_, ?_, ?_, ?_, ?_,
        r.1, 1, hpos, zero_lt_one, ?_⟩
      · exact dualCoveringRayCandidate_mem_recessionCone ci
      · exact hq_mem
      · simp [uncapacitated_facility_location_dual_covering_ray_candidate]
      · exact hq_zero
      · intro hsame
        exact dualCoveringRay_not_sameRay_of_head_zero hq_zero rfl hsame.symm
      · simpa using hr_split
    exact False.elim (hnotproper hproper)

/-- Helper for Exercise 8.20: a negative-head extreme ray must lie on the negative-`u` ray. -/
lemma dualExtremeRay_sameRay_negativeU_of_head_neg
    (ci : Fin n → ℝ)
    {r : ℝ × (Fin n → ℝ)}
    (hr : r ≠ 0)
    (hExt : IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r)
    (hneg : r.1 < 0) :
    SameRay ℝ r uncapacitated_facility_location_dual_negative_u_ray_candidate := by
  have hr_mem := dualExtremeRay_mem_recessionCone hExt
  have hnotproper := dualExtremeRay_not_properConicCombination hr hExt
  rw [memRecessionCone_dualPolyhedron_iff] at hr_mem
  let q : ℝ × (Fin n → ℝ) := (0, fun j ↦ r.2 j)
  have hq_mem :
      q ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
    -- The head-zero remainder is exactly the nonnegative tail of `r`.
    rw [memRecessionCone_dualPolyhedron_iff]
    constructor
    · intro j
      simpa [q] using hr_mem.1 j
    · intro j
      simpa [q] using hr_mem.1 j
  have hr_split :
      r = (-r.1) • uncapacitated_facility_location_dual_negative_u_ray_candidate + q := by
    refine Prod.ext ?_ ?_
    · simp [q, uncapacitated_facility_location_dual_negative_u_ray_candidate]
    · funext j
      simp [q, uncapacitated_facility_location_dual_negative_u_ray_candidate,
        Pi.add_apply, Pi.smul_apply]
  by_cases hq_zero : q = 0
  · -- If the head-zero remainder vanishes, only the negative-`u` component survives.
    have hr_repr : r = (-r.1) • uncapacitated_facility_location_dual_negative_u_ray_candidate := by
      simpa [hq_zero] using hr_split
    rw [hr_repr]
    exact SameRay.sameRay_pos_smul_left
      uncapacitated_facility_location_dual_negative_u_ray_candidate (by linarith)
  · -- Otherwise the decomposition violates extremality because the two rays have different heads.
    have hproper :
        ProperConicCombinationOfDistinctConeRays
          (recessionCone (uncapacitated_facility_location_dual_polyhedron ci)) r := by
      refine ⟨uncapacitated_facility_location_dual_negative_u_ray_candidate, q, ?_, ?_, ?_, ?_, ?_,
        -r.1, 1, by linarith, zero_lt_one, ?_⟩
      · exact dualNegativeURayCandidate_mem_recessionCone ci
      · exact hq_mem
      · simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
      · exact hq_zero
      · intro hsame
        exact dualNegativeURay_not_sameRay_of_head_zero hq_zero rfl hsame.symm
      · simpa using hr_split
    exact False.elim (hnotproper hproper)

/-- Helper for Exercise 8.20: a head-zero extreme ray has support on a single tail coordinate. -/
lemma dualExtremeRay_uniqueSupport_of_head_zero
    (ci : Fin n → ℝ)
    {r : ℝ × (Fin n → ℝ)}
    (hr : r ≠ 0)
    (hExt : IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r)
    (h0 : r.1 = 0) :
    ∃ k : Fin n, 0 < r.2 k ∧ ∀ j, j ≠ k → r.2 j = 0 := by
  classical
  have hr_mem := dualExtremeRay_mem_recessionCone hExt
  have hnotproper := dualExtremeRay_not_properConicCombination hr hExt
  rw [memRecessionCone_dualPolyhedron_iff] at hr_mem
  have htail_exists : ∃ k : Fin n, r.2 k ≠ 0 := by
    by_contra hnone
    apply hr
    refine Prod.ext h0 ?_
    funext j
    by_contra hj
    exact hnone ⟨j, hj⟩
  obtain ⟨k, hk_ne⟩ := htail_exists
  have hk_pos : 0 < r.2 k := lt_of_le_of_ne (hr_mem.1 k) hk_ne.symm
  refine ⟨k, hk_pos, ?_⟩
  intro t ht
  by_contra ht_ne
  have ht_pos : 0 < r.2 t := by
    refine lt_of_le_of_ne (hr_mem.1 t) ?_
    exact fun hzero ↦ ht_ne hzero.symm
  let q : ℝ × (Fin n → ℝ) := (0, fun j ↦ if j = k then 0 else r.2 j)
  have hq_mem :
      q ∈ recessionCone (uncapacitated_facility_location_dual_polyhedron ci) := by
    -- Deleting one positive support coordinate keeps the vector in the head-zero orthant slice.
    rw [memRecessionCone_dualPolyhedron_iff]
    constructor
    · intro j
      by_cases hj : j = k
      · simp [q, hj]
      · simp [q, hj, hr_mem.1 j]
    · intro j
      by_cases hj : j = k
      · simp [q, hj]
      · simp [q, hj, hr_mem.1 j]
  have hq_ne : q ≠ 0 := by
    intro hq_zero
    have hqt : q.2 t = 0 := by
      simpa using congrArg (fun p ↦ p.2 t) hq_zero
    have : r.2 t = 0 := by
      simpa [q, ht] using hqt
    exact ht_ne this
  have hcoord_ne :
      uncapacitated_facility_location_dual_coordinate_ray_candidate k ≠ 0 := by
    intro hcoord_zero
    have hkk :
        ((uncapacitated_facility_location_dual_coordinate_ray_candidate k).2 k) = 0 := by
      simpa using congrArg (fun p ↦ p.2 k) hcoord_zero
    simp [uncapacitated_facility_location_dual_coordinate_ray_candidate] at hkk
  have hdistinct :
      ¬ SameRay ℝ
        (uncapacitated_facility_location_dual_coordinate_ray_candidate k) q := by
    intro hsame
    rcases hsame.exists_nonneg_left hcoord_ne with ⟨a, ha, hEq⟩
    have hqt :
        q.2 t = 0 := by
      simpa [uncapacitated_facility_location_dual_coordinate_ray_candidate, ht, q] using
        (congrArg (fun p ↦ p.2 t) hEq).symm
    have : r.2 t = 0 := by
      simpa [q, ht] using hqt
    exact ht_ne this
  have hr_split :
      r = r.2 k • uncapacitated_facility_location_dual_coordinate_ray_candidate k + q := by
    refine Prod.ext ?_ ?_
    · simp [q, h0, uncapacitated_facility_location_dual_coordinate_ray_candidate]
    funext j
    by_cases hj : j = k
    · subst hj
      simp [q, uncapacitated_facility_location_dual_coordinate_ray_candidate,
        Pi.add_apply, Pi.smul_apply]
    · simp [q, uncapacitated_facility_location_dual_coordinate_ray_candidate, hj,
        Pi.add_apply, Pi.smul_apply]
  have hproper :
      ProperConicCombinationOfDistinctConeRays
        (recessionCone (uncapacitated_facility_location_dual_polyhedron ci)) r := by
    refine ⟨uncapacitated_facility_location_dual_coordinate_ray_candidate k, q, ?_, ?_, ?_, ?_, ?_,
      r.2 k, 1, hk_pos, zero_lt_one, ?_⟩
    · exact dualCoordinateRayCandidate_mem_recessionCone ci k
    · exact hq_mem
    · exact hcoord_ne
    · exact hq_ne
    · exact hdistinct
    · simpa using hr_split
  exact False.elim (hnotproper hproper)

/-- Helper for Exercise 8.20: a head-zero extreme ray is, for `n > 0`, a coordinate ray, and the
dimension restriction must in fact strengthen to `1 < n`. -/
lemma dualExtremeRay_sameRay_coordinate_of_head_zero
    (ci : Fin n → ℝ)
    (hn : 0 < n)
    {r : ℝ × (Fin n → ℝ)}
    (hr : r ≠ 0)
    (hExt : IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r)
    (h0 : r.1 = 0) :
    ∃ k : Fin n, 1 < n ∧
      SameRay ℝ r (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
  have hnotproper := dualExtremeRay_not_properConicCombination hr hExt
  obtain ⟨k, hk_pos, huniq⟩ :=
    dualExtremeRay_uniqueSupport_of_head_zero ci hr hExt h0
  have hr_repr :
      r = r.2 k • uncapacitated_facility_location_dual_coordinate_ray_candidate k := by
    refine Prod.ext ?_ ?_
    · simp [h0, uncapacitated_facility_location_dual_coordinate_ray_candidate]
    funext j
    by_cases hj : j = k
    · subst hj
      simp [uncapacitated_facility_location_dual_coordinate_ray_candidate]
    · simp [uncapacitated_facility_location_dual_coordinate_ray_candidate, hj, huniq j hj]
  have hsame :
      SameRay ℝ r (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
    rw [hr_repr]
    exact SameRay.sameRay_pos_smul_left
      (uncapacitated_facility_location_dual_coordinate_ray_candidate k) hk_pos
  have hn1 : 1 < n := by
    by_contra hnot
    have hEq : n = 1 := by
      apply le_antisymm (Nat.le_of_not_gt hnot)
      exact Nat.succ_le_of_lt hn
    subst hEq
    have hr_split :
        r = r.2 k • uncapacitated_facility_location_dual_covering_ray_candidate +
          r.2 k • uncapacitated_facility_location_dual_negative_u_ray_candidate := by
      refine Prod.ext ?_ ?_
      · simp [h0, uncapacitated_facility_location_dual_covering_ray_candidate,
          uncapacitated_facility_location_dual_negative_u_ray_candidate]
      · funext j
        have hjk : j = k := Subsingleton.elim _ _
        subst hjk
        simp [uncapacitated_facility_location_dual_covering_ray_candidate,
          uncapacitated_facility_location_dual_negative_u_ray_candidate]
    have hproper :
        ProperConicCombinationOfDistinctConeRays
          (recessionCone (uncapacitated_facility_location_dual_polyhedron ci)) r := by
      refine ⟨uncapacitated_facility_location_dual_covering_ray_candidate,
        uncapacitated_facility_location_dual_negative_u_ray_candidate, ?_, ?_, ?_, ?_, ?_,
        r.2 k, r.2 k, hk_pos, hk_pos, ?_⟩
      · exact dualCoveringRayCandidate_mem_recessionCone ci
      · exact dualNegativeURayCandidate_mem_recessionCone ci
      · simp [uncapacitated_facility_location_dual_covering_ray_candidate]
      · simp [uncapacitated_facility_location_dual_negative_u_ray_candidate]
      · exact dualCoveringRay_not_sameRay_negativeU
      · simpa using hr_split
    exact False.elim (hnotproper hproper)
  exact ⟨k, hn1, hsame⟩

/-- Part (3) of Exercise 8.20. The extreme rays of
`Q_i = {(u_i,w_i) ∈ ℝ × ℝ_+^n | u_i - w_{ij} ≤ c_{ij}}` are, up to positive scaling, the common
covering ray `(1, 1, ..., 1)`, the negative-`u` ray `(-1, 0, ..., 0)`, and for `n > 1` the
coordinate rays `(0, e^k)`. -/
theorem exercise_8_20_dual_polyhedron_extreme_rays
    (ci : Fin n → ℝ)
    (hn : 0 < n)
    {r : ℝ × (Fin n → ℝ)}
    (hr : r ≠ 0) :
    IsExtremeRayOfPolyhedron (uncapacitated_facility_location_dual_polyhedron ci) r ↔
      SameRay ℝ r uncapacitated_facility_location_dual_covering_ray_candidate ∨
        SameRay ℝ r uncapacitated_facility_location_dual_negative_u_ray_candidate ∨
          ∃ k : Fin n,
            1 < n ∧ SameRay ℝ r
              (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
  constructor
  · intro hExt
    have hr_mem := dualExtremeRay_mem_recessionCone hExt
    rw [memRecessionCone_dualPolyhedron_iff] at hr_mem
    by_cases hpos : 0 < r.1
    · -- A positive head leaves only the covering-ray component in the canonical decomposition.
      exact Or.inl (dualExtremeRay_sameRay_covering_of_head_pos ci hr hExt hpos)
    · by_cases hneg : r.1 < 0
      · -- A negative head leaves only the negative-`u` component.
        exact Or.inr (Or.inl (dualExtremeRay_sameRay_negativeU_of_head_neg ci hr hExt hneg))
      · -- With zero head, extremality forces support on a single tail coordinate.
        have h0 : r.1 = 0 := by
          linarith
        exact Or.inr (Or.inr
          (dualExtremeRay_sameRay_coordinate_of_head_zero ci hn hr hExt h0))
  · intro hclass
    rw [isExtremeRayOfPolyhedron_iff]
    rcases hclass with hcover | hneg | ⟨k, hn1, hcoord⟩
    · -- Extreme-rayhood is preserved along the same covering ray.
      have hcover_ext :
          IsExtremeRayOfCone
            (recessionCone (uncapacitated_facility_location_dual_polyhedron ci))
            uncapacitated_facility_location_dual_covering_ray_candidate := by
        simpa [isExtremeRayOfPolyhedron_iff] using dualCoveringRayCandidate_isExtremeRay ci hn
      exact isExtremeRayOfCone_of_sameRay hcover_ext hcover.symm hr
    · -- The negative-`u` candidate gives the second extreme-ray family.
      have hneg_ext :
          IsExtremeRayOfCone
            (recessionCone (uncapacitated_facility_location_dual_polyhedron ci))
            uncapacitated_facility_location_dual_negative_u_ray_candidate := by
        simpa [isExtremeRayOfPolyhedron_iff] using dualNegativeURayCandidate_isExtremeRay ci hn
      exact isExtremeRayOfCone_of_sameRay hneg_ext hneg.symm hr
    · -- For `n > 1`, the head-zero singleton-support rays are exactly the coordinate rays.
      have hcoord_ext :
          IsExtremeRayOfCone
            (recessionCone (uncapacitated_facility_location_dual_polyhedron ci))
            (uncapacitated_facility_location_dual_coordinate_ray_candidate k) := by
        simpa [isExtremeRayOfPolyhedron_iff] using
          dualCoordinateRayCandidate_isExtremeRay ci hn1
      exact isExtremeRayOfCone_of_sameRay hcoord_ext hcoord.symm hr

/-- Helper for Exercise 8.20: source-feasibility is equivalent to rowwise customer-subproblem
feasibility together with binary opening variables. -/
theorem mem_uncapacitated_facility_location_problem_feasible_set_iff_rows
    {y : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ} :
    (y, x) ∈ uncapacitated_facility_location_problem_feasible_set ↔
      (∀ i, y i ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x) ∧
        (∀ j, x j = 0 ∨ x j = 1) := by
  -- Repackage the source owner as rowwise customer-subproblem feasibility plus binary openings.
  rw [mem_uncapacitated_facility_location_problem_feasible_set_iff]
  constructor
  · rintro ⟨hrow, hlink, hnonneg, hx⟩
    refine ⟨?_, hx⟩
    intro i
    rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff]
    exact ⟨hrow i, fun j ↦ hlink i j, fun j ↦ hnonneg i j⟩
  · rintro ⟨hrow, hx⟩
    refine ⟨?_, ?_, ?_, hx⟩
    · intro i
      exact (mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff.mp
        (hrow i)).1
    · intro i j
      exact (mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff.mp
        (hrow i)).2.1 j
    · intro i j
      exact (mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff.mp
        (hrow i)).2.2 j

/-- Helper for Exercise 8.20: any feasible customer row already forces the opening sum
constraint `1 ≤ ∑ j, x j`. -/
theorem one_le_sum_openings_of_mem_customer_subproblem_feasible_set
    {x : Fin n → ℝ}
    {yi : Fin n → ℝ}
    (hyi : yi ∈ uncapacitated_facility_location_customer_subproblem_feasible_set x) :
    1 ≤ ∑ j, x j := by
  -- Sum the coordinatewise upper bounds `yi j ≤ x j` and use the row equation `∑ yi = 1`.
  rw [mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff] at hyi
  rcases hyi with ⟨hsum, hle, _⟩
  calc
    1 = ∑ j, yi j := by symm; exact hsum
    _ ≤ ∑ j, x j := Finset.sum_le_sum fun j _ ↦ hle j

/-- Helper for Exercise 8.20: every integer-feasible assignment is also feasible for the
source-facing continuous formulation. -/
theorem mem_uncapacitated_facility_location_problem_feasible_set_of_mem_integer_feasible_set
    {y : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ}
    (hxy : (y, x) ∈ uncapacitated_facility_location_integer_feasible_set) :
    (y, x) ∈ uncapacitated_facility_location_problem_feasible_set := by
  -- Keep the same assignment equations, linking inequalities, and binary openings, and recover
  -- nonnegativity from the binary assignment variables.
  rcases (mem_uncapacitated_facility_location_integer_feasible_set_iff.mp hxy) with
    ⟨hrow, hlink, _, hx⟩
  rw [mem_uncapacitated_facility_location_problem_feasible_set_iff]
  refine ⟨hrow, hlink, ?_, hx⟩
  intro i j
  exact nonneg_of_mem_uncapacitated_facility_location_integer_feasible_set hxy i j

/-- Helper for Exercise 8.20: replacing each customer row by its row cost produces a feasible
point of the explicit Benders reformulation. -/
theorem rowCosts_mem_bendersReformulationFeasibleSet_of_mem_problemFeasibleSet
    (c : Fin m → Fin n → ℝ)
    (hm : 0 < m)
    {y : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ}
    (hxy : (y, x) ∈ uncapacitated_facility_location_problem_feasible_set) :
    ((fun i ↦ ∑ j, c i j * y i j), x) ∈
      uncapacitated_facility_location_benders_reformulation_feasible_set c := by
  -- The row costs satisfy every optimality cut, and any one feasible row yields the cut
  -- `∑_j x_j ≥ 1` because the customer set is nonempty.
  rcases (mem_uncapacitated_facility_location_problem_feasible_set_iff_rows.mp hxy) with
    ⟨hrows, hx⟩
  rw [mem_uncapacitated_facility_location_benders_reformulation_feasible_set_iff]
  refine ⟨hx, ?_, ?_⟩
  · intro i k
    exact customerCut_le_customerRowCost c hx (hrows i) k
  · let i0 : Fin m := ⟨0, hm⟩
    exact one_le_sum_openings_of_mem_customer_subproblem_feasible_set (hrows i0)

/-- Helper for Exercise 8.20: the source objective equals the Benders objective evaluated at the
row-cost vector `η_i = ∑_j c_ij y_ij`. -/
theorem sourceObjective_eq_bendersObjective_of_rowCosts
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (y : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    (-uncapacitated_facility_location_objective (fun i j ↦ -c i j) f (y, x) : ℝ) =
      uncapacitated_facility_location_benders_reformulation_objective f
        ((fun i ↦ ∑ j, c i j * y i j), x) := by
  -- Expanding both objective owners leaves the same assignment-cost plus opening-cost formula.
  simp [uncapacitated_facility_location_objective_mk,
    uncapacitated_facility_location_benders_reformulation_objective, neg_sub, add_comm]

/-- Helper for Exercise 8.20: a family of global row minima together with the coordinatewise lower
bound `min (f j) 0` yields a uniform lower bound on the source objective. -/
theorem sourceObjective_lowerBound_of_mem_problemFeasibleSet
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (kmin : Fin m → Fin n)
    (hkMin : ∀ i j, c i (kmin i) ≤ c i j)
    {y : Fin m → Fin n → ℝ}
    {x : Fin n → ℝ}
    (hxy : (y, x) ∈ uncapacitated_facility_location_problem_feasible_set) :
    (∑ i, c i (kmin i)) + ∑ j, min (f j) 0 ≤
      (-uncapacitated_facility_location_objective (fun i j ↦ -c i j) f (y, x) : ℝ) := by
  -- Bound the assignment part rowwise by the chosen global minima and bound the opening part
  -- coordinatewise by `min (f j) 0`.
  rcases (mem_uncapacitated_facility_location_problem_feasible_set_iff_rows.mp hxy) with
    ⟨hrows, hx⟩
  have hrowLower : ∀ i, c i (kmin i) ≤ ∑ j, c i j * y i j := by
    intro i
    exact globalMin_le_customerRowCost c (hkMin i) (hrows i)
  have hopenLower : ∀ j, min (f j) 0 ≤ f j * x j := by
    intro j
    rcases hx j with hxj | hxj <;> simp [hxj]
  have hsumRows : ∑ i, c i (kmin i) ≤ ∑ i, ∑ j, c i j * y i j := by
    exact Finset.sum_le_sum fun i _ ↦ hrowLower i
  have hsumOpen : ∑ j, min (f j) 0 ≤ ∑ j, f j * x j := by
    exact Finset.sum_le_sum fun j _ ↦ hopenLower j
  calc
    (∑ i, c i (kmin i)) + ∑ j, min (f j) 0 ≤
        (∑ i, ∑ j, c i j * y i j) + ∑ j, f j * x j := by
          exact add_le_add hsumRows hsumOpen
    _ = (-uncapacitated_facility_location_objective (fun i j ↦ -c i j) f (y, x) : ℝ) := by
          symm
          exact sourceObjective_eq_bendersObjective_of_rowCosts c f y x

/-- Helper for Exercise 8.20: every feasible Benders point admits a source-feasible witness whose
source objective is bounded above by the Benders objective. -/
theorem exists_sourceWitness_le_of_mem_bendersReformulationFeasibleSet
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    {η : Fin m → ℝ}
    {x : Fin n → ℝ}
    (hetax : (η, x) ∈ uncapacitated_facility_location_benders_reformulation_feasible_set c) :
    ∃ y : Fin m → Fin n → ℝ,
      (y, x) ∈ uncapacitated_facility_location_problem_feasible_set ∧
      (((-uncapacitated_facility_location_objective (fun i j ↦ -c i j) f (y, x) : ℝ) :
          WithTop ℝ) ≤
        ((uncapacitated_facility_location_benders_reformulation_objective f (η, x) : ℝ) :
          WithTop ℝ)) := by
  classical
  -- Choose for each customer an open minimizing facility and use its indicator assignment as the
  -- source witness.
  rcases (mem_uncapacitated_facility_location_benders_reformulation_feasible_set_iff.mp hetax) with
    ⟨hx, hcuts, hsum⟩
  have hkExists :
      ∀ i : Fin m, ∃ k : Fin n, x k = 1 ∧ ∀ j, x j = 1 → c i k ≤ c i j := by
    intro i
    exact existsOpenFacilityArgmin c hx hsum i
  choose k hkOpen hkMin using hkExists
  let y : Fin m → Fin n → ℝ := fun i ↦ openFacilityIndicator (k i)
  have hyInteger :
      (y, x) ∈ uncapacitated_facility_location_integer_feasible_set :=
    openArgminIndicatorAssignment_mem_integer_feasible_set hx k hkOpen
  have hySource :
      (y, x) ∈ uncapacitated_facility_location_problem_feasible_set :=
    mem_uncapacitated_facility_location_problem_feasible_set_of_mem_integer_feasible_set hyInteger
  have hkEta : ∀ i, c i (k i) ≤ η i := by
    intro i
    exact
      (customerCuts_iff_geOpenArgminCost c hx (hkOpen i) (hkMin i) (η := η i)).mp
        (hcuts i)
  have hreal :
      uncapacitated_facility_location_benders_reformulation_objective f
          ((fun i ↦ c i (k i)), x) ≤
        uncapacitated_facility_location_benders_reformulation_objective f (η, x) := by
    rw [uncapacitated_facility_location_benders_reformulation_objective,
      uncapacitated_facility_location_benders_reformulation_objective]
    have hsumEta : ∑ i, c i (k i) ≤ ∑ i, η i := by
      exact Finset.sum_le_sum fun i _ ↦ hkEta i
    linarith
  refine ⟨y, hySource, ?_⟩
  -- Normalize the source objective to the chosen row costs and then compare with the Benders
  -- cuts `c_i(k_i) ≤ η_i`.
  calc
    (((-uncapacitated_facility_location_objective (fun i j ↦ -c i j) f (y, x) : ℝ) :
        WithTop ℝ)) =
        ((uncapacitated_facility_location_benders_reformulation_objective f
          ((fun i ↦ c i (k i)), x) : ℝ) : WithTop ℝ) := by
            rw [sourceObjective_eq_bendersObjective_of_rowCosts]
            simp [y, rowCost_openFacilityIndicator,
              uncapacitated_facility_location_benders_reformulation_objective]
    _ ≤ ((uncapacitated_facility_location_benders_reformulation_objective f (η, x) : ℝ) :
          WithTop ℝ) := by
            exact (WithTop.coe_le_coe).2 hreal

/-- Exercise 8.20. Part (iii): for a nonempty customer set, deducing from part (i) and the
preceding part (ii) extreme-point and extreme-ray characterizations, the uncapacitated
facility-location problem is equivalent to the explicit Benders reformulation with objective
`∑_i η_i + ∑_j f_j x_j`, optimality cuts
`η_i ≥ c_{ik} - ∑_j (c_{ik} - c_{ij})^+ x_j`, the nontrivial feasibility cut `∑_j x_j ≥ 1`, and
binary opening variables `x ∈ {0,1}^n`. -/
theorem exercise_8_20_benders_reformulation
    (c : Fin m → Fin n → ℝ)
    (hm : 0 < m)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_problem_value c f =
      uncapacitated_facility_location_benders_reformulation_value c f := by
  classical
  -- Route correction: compare the two formulations by explicit witness maps between their image
  -- sets, instead of reopening the dual polyhedron analysis from part (ii).
  let sourceSet : Set (WithTop ℝ) :=
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((-uncapacitated_facility_location_objective
            (fun i j ↦ -c i j)
            f
            xy : ℝ) : WithTop ℝ)) ''
      uncapacitated_facility_location_problem_feasible_set)
  let bendersSet : Set (WithTop ℝ) :=
    ((fun etax : (Fin m → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_benders_reformulation_objective f etax : ℝ) :
          WithTop ℝ)) ''
      uncapacitated_facility_location_benders_reformulation_feasible_set c)
  by_cases hne : Nonempty (Fin n)
  · have hkExists : ∀ i : Fin m, ∃ k : Fin n, ∀ j, c i k ≤ c i j := by
      intro i
      obtain ⟨k, hk⟩ := Finite.exists_min (fun j : Fin n ↦ c i j)
      exact ⟨k, hk⟩
    choose kmin hkMin using hkExists
    let k0 : Fin n := Classical.choice hne
    let x0 : Fin n → ℝ := openFacilityIndicator k0
    let y0 : Fin m → Fin n → ℝ := fun _ ↦ openFacilityIndicator k0
    have hx0 : ∀ j, x0 j = 0 ∨ x0 j = 1 := by
      intro j
      by_cases hj : j = k0
      · right
        simp [x0, openFacilityIndicator, hj]
      · left
        simp [x0, openFacilityIndicator, hj]
    have hk0Open : ∀ i : Fin m, x0 (k0) = 1 := by
      intro i
      simp [x0, openFacilityIndicator]
    have hy0Integer :
        (y0, x0) ∈ uncapacitated_facility_location_integer_feasible_set :=
      openArgminIndicatorAssignment_mem_integer_feasible_set hx0 (fun _ ↦ k0) hk0Open
    have hy0Source :
        (y0, x0) ∈ uncapacitated_facility_location_problem_feasible_set :=
      mem_uncapacitated_facility_location_problem_feasible_set_of_mem_integer_feasible_set
        hy0Integer
    have hy0Benders :
        ((fun i ↦ ∑ j, c i j * y0 i j), x0) ∈
          uncapacitated_facility_location_benders_reformulation_feasible_set c :=
      rowCosts_mem_bendersReformulationFeasibleSet_of_mem_problemFeasibleSet c hm hy0Source
    have hSourceNonempty : sourceSet.Nonempty := by
      refine ⟨_, ⟨(y0, x0), hy0Source, rfl⟩⟩
    have hBendersNonempty : bendersSet.Nonempty := by
      refine ⟨_, ⟨((fun i ↦ ∑ j, c i j * y0 i j), x0), hy0Benders, rfl⟩⟩
    have hSourceBddBelow : BddBelow sourceSet := by
      refine ⟨((((∑ i, c i (kmin i)) + ∑ j, min (f j) 0 : ℝ) : WithTop ℝ)), ?_⟩
      rintro _ ⟨⟨y, x⟩, hxy, rfl⟩
      exact
        (WithTop.coe_le_coe).2
          (sourceObjective_lowerBound_of_mem_problemFeasibleSet c f kmin hkMin hxy)
    have hBendersBddBelow : BddBelow bendersSet := by
      refine ⟨((((∑ i, c i (kmin i)) + ∑ j, min (f j) 0 : ℝ) : WithTop ℝ)), ?_⟩
      rintro _ ⟨⟨η, x⟩, hetax, rfl⟩
      obtain ⟨y, hySource, hle⟩ :=
        exists_sourceWitness_le_of_mem_bendersReformulationFeasibleSet c f hetax
      exact
        le_trans
          ((WithTop.coe_le_coe).2
            (sourceObjective_lowerBound_of_mem_problemFeasibleSet c f kmin hkMin hySource))
          hle
    rw [uncapacitated_facility_location_problem_value_eq_sInf,
      uncapacitated_facility_location_benders_reformulation_value]
    change sInf sourceSet = sInf bendersSet
    refine le_antisymm ?_ ?_
    · -- Every feasible Benders point is dominated by the source objective of an explicit
      -- indicator-assignment witness.
      exact le_csInf hBendersNonempty fun _ hb ↦ by
        rcases hb with ⟨⟨η, x⟩, hetax, rfl⟩
        obtain ⟨y, hySource, hle⟩ :=
          exists_sourceWitness_le_of_mem_bendersReformulationFeasibleSet c f hetax
        exact le_trans (csInf_le hSourceBddBelow ⟨(y, x), hySource, rfl⟩) hle
    · -- Every source-feasible assignment yields a Benders-feasible row-cost vector with the same
      -- objective value.
      exact le_csInf hSourceNonempty fun _ ha ↦ by
        rcases ha with ⟨⟨y, x⟩, hxy, rfl⟩
        have hrowCosts :
            ((fun i ↦ ∑ j, c i j * y i j), x) ∈
              uncapacitated_facility_location_benders_reformulation_feasible_set c :=
          rowCosts_mem_bendersReformulationFeasibleSet_of_mem_problemFeasibleSet c hm hxy
        have hsInfLe :
            sInf bendersSet ≤
              ((uncapacitated_facility_location_benders_reformulation_objective f
                  ((fun i ↦ ∑ j, c i j * y i j), x) : ℝ) : WithTop ℝ) :=
          csInf_le hBendersBddBelow
            ⟨((fun i ↦ ∑ j, c i j * y i j), x), hrowCosts, rfl⟩
        simpa [sourceObjective_eq_bendersObjective_of_rowCosts c f y x] using hsInfLe
  · have hSourceEmpty : sourceSet = ∅ := by
      ext z
      constructor
      · rintro ⟨⟨y, x⟩, hxy, rfl⟩
        haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
        let i0 : Fin m := ⟨0, hm⟩
        have hrow :
            ∑ j, y i0 j = 1 :=
          (mem_uncapacitated_facility_location_customer_subproblem_feasible_set_iff.mp
            ((mem_uncapacitated_facility_location_problem_feasible_set_iff_rows.mp hxy).1 i0)).1
        have : False := by
          simp at hrow
        exact this
      · intro hz
        cases hz
    have hBendersEmpty : bendersSet = ∅ := by
      ext z
      constructor
      · rintro ⟨⟨η, x⟩, hetax, rfl⟩
        haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
        rcases (mem_uncapacitated_facility_location_benders_reformulation_feasible_set_iff.mp
          hetax) with ⟨_, _, hsum⟩
        have : (1 : ℝ) ≤ 0 := by
          simpa using hsum
        linarith
      · intro hz
        cases hz
    rw [uncapacitated_facility_location_problem_value_eq_sInf,
      uncapacitated_facility_location_benders_reformulation_value]
    change sInf sourceSet = sInf bendersSet
    simp [hSourceEmpty, hBendersEmpty]

end Exercise820
