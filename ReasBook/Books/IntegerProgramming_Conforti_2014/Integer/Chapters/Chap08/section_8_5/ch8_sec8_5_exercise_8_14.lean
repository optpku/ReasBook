import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_12

open scoped BigOperators

-- Domain sampling note:
-- * core/canonical facility-location owners from Exercises 8.12 and 8.13:
--   `uncapacitated_facility_location_integer_feasible_set`,
--   `uncapacitated_facility_location_assignments_for_openings`, and
--   `uncapacitated_facility_location_objective`
-- * source-facing layer kept here: the Dantzig-Wolfe subset-column master system and its
--   projection back to the original assignment variables
-- * bridge/view declarations: `uncapacitated_facility_location_dw_assignment` and the main
--   reformulation theorem below

section Exercise814

variable {m n : ℕ}

/-- The nonempty client subsets indexing the Dantzig-Wolfe columns from Exercise 8.14. -/
abbrev UncapacitatedFacilityLocationDwClientSet (m : ℕ) :=
  {s : Finset (Fin m) // s.Nonempty}

/-- A Dantzig-Wolfe column family assigns a weight to each facility site `j` and each nonempty
client subset `S`. -/
abbrev UncapacitatedFacilityLocationDwColumns (m n : ℕ) :=
  Fin n → UncapacitatedFacilityLocationDwClientSet m → ℝ

/-- The assignment matrix `y` induced by the Dantzig-Wolfe variables `λ_S^j`: client `i` is
assigned to facility `j` exactly when the chosen subset for site `j` contains `i`. -/
def uncapacitated_facility_location_dw_assignment
    (lam : UncapacitatedFacilityLocationDwColumns m n) : Fin m → Fin n → ℝ :=
  fun i j ↦
    ∑ s,
      (if i ∈ s.1 then 1 else 0) * lam j s

/-- Evaluating the induced assignment matrix at `(i,j)` recovers the sum of the Dantzig-Wolfe
columns for facility `j` whose client subset contains `i`. -/
theorem uncapacitated_facility_location_dw_assignment_apply
    (lam : UncapacitatedFacilityLocationDwColumns m n)
    (i : Fin m)
    (j : Fin n) :
    uncapacitated_facility_location_dw_assignment lam i j =
      ∑ s, (if i ∈ s.1 then 1 else 0) * lam j s :=
  rfl

/-- The Dantzig-Wolfe master feasible set suggested in Exercise 8.14: `x_j` stays explicit,
and for each site `j` the binary column variable `λ_S^j` indicates that the open facility at
site `j` serves exactly the nonempty client set `S`. The master constraints require every client
to be covered exactly once, so the induced assignment matrix lies in the canonical fixed-opening
facility-location feasible set, and they enforce `∑_S λ_S^j ≤ x_j` for each facility site. -/
def uncapacitated_facility_location_dw_feasible_set :
    Set ((Fin n → ℝ) × UncapacitatedFacilityLocationDwColumns m n) :=
  {xlam |
    (∀ j s, xlam.2 j s = 0 ∨ xlam.2 j s = 1) ∧
      uncapacitated_facility_location_dw_assignment xlam.2 ∈
        uncapacitated_facility_location_assignments_for_openings xlam.1 ∧
      (∀ j, ∑ s, xlam.2 j s ≤ xlam.1 j)}

/-- Membership in `uncapacitated_facility_location_dw_feasible_set` expands to binary
Dantzig-Wolfe column variables, feasibility of the induced assignment matrix for the fixed-opening
owner from Exercise 8.12, and the sitewise bounds `∑_S λ_S^j ≤ x_j`. -/
theorem mem_uncapacitated_facility_location_dw_feasible_set_iff
    {xlam : (Fin n → ℝ) × UncapacitatedFacilityLocationDwColumns m n} :
    xlam ∈ uncapacitated_facility_location_dw_feasible_set ↔
      (∀ j s, xlam.2 j s = 0 ∨ xlam.2 j s = 1) ∧
        uncapacitated_facility_location_dw_assignment xlam.2 ∈
          uncapacitated_facility_location_assignments_for_openings xlam.1 ∧
        (∀ j, ∑ s, xlam.2 j s ≤ xlam.1 j) :=
  Iff.rfl

/-- Helper for Exercise 8.14: `assignedClients y j` is the client set served by facility `j` in
the integral assignment matrix `y`. -/
noncomputable def assignedClients
    (y : Fin m → Fin n → ℝ)
    (j : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun i ↦ y i j = 1)

/-- Helper for Exercise 8.14: `columnsFromAssignment y j s` is the one-hot Dantzig-Wolfe column
family that activates the nonempty client subset equal to `assignedClients y j`. -/
noncomputable def columnsFromAssignment
    (y : Fin m → Fin n → ℝ) : UncapacitatedFacilityLocationDwColumns m n :=
  fun j s ↦ if s.1 = assignedClients y j then 1 else 0

/-- Helper for Exercise 8.14: membership in `assignedClients y j` is exactly the statement that
client `i` is assigned to facility `j` with value `1`. -/
lemma assignedClients_mem_iff
    (y : Fin m → Fin n → ℝ)
    (i : Fin m)
    (j : Fin n) :
    i ∈ assignedClients y j ↔ y i j = 1 := by
  -- Unfold the filtered client set and reduce membership to the defining predicate.
  simp [assignedClients]

/-- Helper for Exercise 8.14: if some client is assigned to facility `j`, then the site-opening
variable at `j` must be `1`. -/
lemma openSite_of_assignedClients_nonempty
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : y ∈ uncapacitated_facility_location_assignments_for_openings x)
    (j : Fin n)
    (hj : (assignedClients y j).Nonempty) :
    x j = 1 := by
  -- Extract one served client from the nonempty assigned-client set.
  rcases hj with ⟨i, hi⟩
  have hij : y i j = 1 := by
    rw [← assignedClients_mem_iff y i j]
    exact hi
  -- Convert the assignment certificate into the opening certificate via Exercise 8.12.
  exact
    opening_eq_one_of_mem_uncapacitated_facility_location_assignments_for_openings hy hij

/-- Helper for Exercise 8.14: the one-hot column encoding contributes exactly one active subset
for facility `j` when `assignedClients y j` is nonempty, and contributes nothing otherwise. -/
lemma sum_columnsFromAssignment_eq
    (y : Fin m → Fin n → ℝ)
    (j : Fin n) :
    ∑ s, columnsFromAssignment y j s = if (assignedClients y j).Nonempty then 1 else 0 := by
  classical
  by_cases hj : (assignedClients y j).Nonempty
  · let s0 : UncapacitatedFacilityLocationDwClientSet m := ⟨assignedClients y j, hj⟩
    -- In the nonempty case, the sum has a single active subtype point.
    have hs0 : ∑ s, columnsFromAssignment y j s = columnsFromAssignment y j s0 := by
      refine Finset.sum_eq_single s0 ?_ ?_
      · intro s _ hs
        have hsNe : s.1 ≠ assignedClients y j := by
          intro hEq
          apply hs
          exact Subtype.ext hEq
        simp [columnsFromAssignment, hsNe]
      · simp
    rw [if_pos hj]
    calc
      ∑ s, columnsFromAssignment y j s = columnsFromAssignment y j s0 := hs0
      _ = 1 := by simp [columnsFromAssignment, s0]
  · -- If no nonempty subset matches `assignedClients y j`, every column coefficient is zero.
    rw [if_neg hj]
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hsNe : s.1 ≠ assignedClients y j := by
      intro hEq
      apply hj
      rw [← hEq]
      exact s.2
    simp [columnsFromAssignment, hsNe]

/-- Helper for Exercise 8.14: the one-hot Dantzig-Wolfe columns reconstructed from a feasible
assignment matrix recover that assignment under `uncapacitated_facility_location_dw_assignment`.
-/
lemma dwAssignment_columnsFromAssignment
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ}
    (hy : y ∈ uncapacitated_facility_location_assignments_for_openings x) :
    uncapacitated_facility_location_dw_assignment (columnsFromAssignment y) = y := by
  classical
  rcases (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mp hy with
    ⟨_, _, hbinary, _⟩
  -- Compare the reconstructed matrix and `y` entrywise.
  funext i
  funext j
  by_cases hj : (assignedClients y j).Nonempty
  · let s0 : UncapacitatedFacilityLocationDwClientSet m := ⟨assignedClients y j, hj⟩
    have hs0 :
        uncapacitated_facility_location_dw_assignment (columnsFromAssignment y) i j =
          (if i ∈ s0.1 then 1 else 0) * columnsFromAssignment y j s0 := by
      rw [uncapacitated_facility_location_dw_assignment_apply]
      -- In the nonempty branch, only the column indexed by `assignedClients y j` survives.
      refine Finset.sum_eq_single s0 ?_ ?_
      · intro s _ hs
        have hsNe : s.1 ≠ assignedClients y j := by
          intro hEq
          apply hs
          exact Subtype.ext hEq
        simp [columnsFromAssignment, hsNe]
      · simp
    rcases hbinary i j with hij | hij
    · have hiNotMem : i ∉ assignedClients y j := by
        intro hiMem
        have hiEq : y i j = 1 := (assignedClients_mem_iff y i j).mp hiMem
        exact zero_ne_one (hij.symm.trans hiEq)
      calc
        uncapacitated_facility_location_dw_assignment (columnsFromAssignment y) i j =
            (if i ∈ s0.1 then 1 else 0) * columnsFromAssignment y j s0 := hs0
        _ = 0 := by simp [s0, columnsFromAssignment, hiNotMem]
        _ = y i j := hij.symm
    · have hiMem : i ∈ assignedClients y j := by
        rw [assignedClients_mem_iff]
        exact hij
      calc
        uncapacitated_facility_location_dw_assignment (columnsFromAssignment y) i j =
            (if i ∈ s0.1 then 1 else 0) * columnsFromAssignment y j s0 := hs0
        _ = 1 := by simp [s0, columnsFromAssignment, hiMem]
        _ = y i j := hij.symm
  · have hsumZero :
      uncapacitated_facility_location_dw_assignment (columnsFromAssignment y) i j = 0 := by
      rw [uncapacitated_facility_location_dw_assignment_apply]
      -- If no subset is active for site `j`, every summand is zero.
      refine Finset.sum_eq_zero ?_
      intro s hs
      have hsNe : s.1 ≠ assignedClients y j := by
        intro hEq
        apply hj
        rw [← hEq]
        exact s.2
      simp [columnsFromAssignment, hsNe]
    rcases hbinary i j with hij | hij
    · exact hsumZero.trans hij.symm
    · have hiMem : i ∈ assignedClients y j := by
        rw [assignedClients_mem_iff]
        exact hij
      exact False.elim (hj ⟨i, hiMem⟩)

/-- Exercise 8.14. Using the binary variables `λ_S^j` for nonempty client sets `S`, the
uncapacitated facility-location feasible set from `(8.5)` is exactly the projection of the
Dantzig-Wolfe master system in which each client is covered once and each site `j` satisfies
`∑_S λ_S^j ≤ x_j`; the original assignment matrix is recovered by
`y_ij = ∑_{S : i ∈ S} λ_S^j`. -/
theorem exercise_8_14_dantzig_wolfe_reformulation
    {x : Fin n → ℝ}
    {y : Fin m → Fin n → ℝ} :
    (y, x) ∈ uncapacitated_facility_location_integer_feasible_set ↔
      ∃ lam : UncapacitatedFacilityLocationDwColumns m n,
        (x, lam) ∈ uncapacitated_facility_location_dw_feasible_set ∧
          y = uncapacitated_facility_location_dw_assignment lam := by
  constructor
  · intro hxy
    rcases (mem_uncapacitated_facility_location_integer_feasible_set_iff.mp hxy) with
      ⟨_, _, _, hxBinary⟩
    have hy : y ∈ uncapacitated_facility_location_assignments_for_openings x := by
      exact (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mpr hxy
    refine ⟨columnsFromAssignment y, ?_, ?_⟩
    · rw [mem_uncapacitated_facility_location_dw_feasible_set_iff]
      refine ⟨?_, ?_, ?_⟩
      · -- The one-hot column family is binary by construction.
        intro j s
        by_cases hs : s.1 = assignedClients y j
        · right
          simp [columnsFromAssignment, hs]
        · left
          simp [columnsFromAssignment, hs]
      · -- Transport feasibility of the induced assignment through the reconstruction lemma.
        simpa [dwAssignment_columnsFromAssignment hy] using hy
      · intro j
        rw [sum_columnsFromAssignment_eq y j]
        by_cases hj : (assignedClients y j).Nonempty
        · -- A nonempty served set forces the corresponding site to be open.
          simp [hj, openSite_of_assignedClients_nonempty hy j hj]
        · -- Otherwise the master column sum is zero, so only `0 ≤ x j` is needed.
          have hxNonneg : 0 ≤ x j := by
            rcases hxBinary j with hxj | hxj
            · have hxj' : x j = 0 := by
                simpa using hxj
              linarith
            · have hxj' : x j = 1 := by
                simpa using hxj
              linarith
          simpa [hj] using hxNonneg
    · -- The reconstructed DW assignment is exactly the original assignment matrix.
      symm
      exact dwAssignment_columnsFromAssignment hy
  · intro hdw
    rcases hdw with ⟨lam, hlam, rfl⟩
    rcases (mem_uncapacitated_facility_location_dw_feasible_set_iff.mp hlam) with
      ⟨_, hassign, _⟩
    -- The reverse implication is immediate from the master-system feasibility clause.
    exact (mem_uncapacitated_facility_location_assignments_for_openings_iff x).mp hassign

end Exercise814
