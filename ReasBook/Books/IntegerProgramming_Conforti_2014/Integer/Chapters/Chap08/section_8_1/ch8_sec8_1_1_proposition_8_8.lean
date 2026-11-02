import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_1_proposition_8_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_easy_block_feasible_set
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_proposition_8_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_remark_3_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import Mathlib.Data.EReal.Basic
import Mathlib.Order.WithBot

open scoped BigOperators Matrix

section Proposition88

variable {m n : ℕ}

/-- The linear-programming relaxation feasible set for the uncapacitated facility-location example:
assignment constraints, nonnegativity, linking inequalities, and bounds `0 ≤ y_j ≤ 1`. -/
def uncapacitated_facility_location_lp_feasible_set
    : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy |
    (∀ i, ∑ j, xy.1 i j = 1) ∧
      (∀ i j, 0 ≤ xy.1 i j) ∧
      (∀ i j, xy.1 i j ≤ xy.2 j) ∧
      (∀ j, 0 ≤ xy.2 j) ∧
      (∀ j, xy.2 j ≤ 1)}

/-- Membership in `uncapacitated_facility_location_lp_feasible_set` is exactly the defining
system of the LP relaxation: assignment equations, nonnegativity, linking inequalities, and
bounds `0 ≤ y_j ≤ 1`. -/
theorem mem_uncapacitated_facility_location_lp_feasible_set_iff
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    xy ∈ uncapacitated_facility_location_lp_feasible_set ↔
      (∀ i, ∑ j, xy.1 i j = 1) ∧
        (∀ i j, 0 ≤ xy.1 i j) ∧
        (∀ i j, xy.1 i j ≤ xy.2 j) ∧
        (∀ j, 0 ≤ xy.2 j) ∧
        (∀ j, xy.2 j ≤ 1) :=
  Iff.rfl

/-- The profit objective `∑_{i,j} c_ij x_ij - ∑_j f_j y_j` for the uncapacitated
facility-location example. -/
def uncapacitated_facility_location_objective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ i, ∑ j, c i j * xy.1 i j) - ∑ j, f j * xy.2 j

/-- Evaluating `uncapacitated_facility_location_objective` on `(y, x)` recovers the displayed
objective formula `∑_{i,j} c_ij y_ij - ∑_j f_j x_j`. -/
theorem uncapacitated_facility_location_objective_mk
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (y : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    uncapacitated_facility_location_objective c f (y, x) =
      (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j :=
  rfl

/-- The feasible set of the Lagrangian relaxation obtained by dropping the assignment equations
`∑_j x_ij = 1` and keeping the remaining linear constraints. -/
def uncapacitated_facility_location_lagrangian_feasible_set
    : Set ((Fin m → Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy |
    (∀ i j, 0 ≤ xy.1 i j) ∧
      (∀ i j, xy.1 i j ≤ xy.2 j) ∧
      (∀ j, 0 ≤ xy.2 j) ∧
      (∀ j, xy.2 j ≤ 1)}

/-- Membership in `uncapacitated_facility_location_lagrangian_feasible_set` means exactly that the
remaining nonnegativity, linking, and bound constraints of the LP relaxation hold after dropping
the assignment equations. -/
theorem mem_uncapacitated_facility_location_lagrangian_feasible_set_iff
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)} :
    xy ∈ uncapacitated_facility_location_lagrangian_feasible_set ↔
      (∀ i j, 0 ≤ xy.1 i j) ∧
        (∀ i j, xy.1 i j ≤ xy.2 j) ∧
        (∀ j, 0 ≤ xy.2 j) ∧
        (∀ j, xy.2 j ≤ 1) :=
  Iff.rfl

/-- Every LP-feasible point remains feasible after dropping the assignment equations. -/
theorem mem_uncapacitated_facility_location_lagrangian_feasible_set_of_mem_lp_feasible_set
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ uncapacitated_facility_location_lp_feasible_set) :
    xy ∈ uncapacitated_facility_location_lagrangian_feasible_set := by
  exact ⟨hxy.2.1, hxy.2.2.1, hxy.2.2.2.1, hxy.2.2.2.2⟩

/-- The source value `z_LR(λ)` for the uncapacitated facility-location example, represented as the
supremum of the Lagrangian objective over the relaxation feasible set. -/
noncomputable def uncapacitated_facility_location_lagrangian_relaxation_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) : ℝ :=
  sSup
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1) ''
      uncapacitated_facility_location_lagrangian_feasible_set)

/-- `uncapacitated_facility_location_lagrangian_relaxation_value c f lam` unfolds to the supremum
of the Proposition 8.7 Lagrangian objective over the relaxation feasible set. -/
theorem uncapacitated_facility_location_lagrangian_relaxation_value_eq_sSup
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) :
    uncapacitated_facility_location_lagrangian_relaxation_value c f lam =
      sSup
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1) ''
          uncapacitated_facility_location_lagrangian_feasible_set) :=
  rfl

/-- The source value `z_LD`, defined as the infimum of the Lagrangian-relaxation values over all
multiplier vectors `λ ∈ ℝ^m`. -/
noncomputable def uncapacitated_facility_location_lagrangian_dual_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : WithBot ℝ :=
  sInf
    (Set.range fun lam : Fin m → ℝ ↦
      ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) : WithBot ℝ))

/-- `uncapacitated_facility_location_lagrangian_dual_value c f` unfolds to the infimum of the
Lagrangian-relaxation values over all multiplier vectors `λ ∈ ℝ^m`. -/
theorem uncapacitated_facility_location_lagrangian_dual_value_eq_sInf
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_lagrangian_dual_value c f =
      sInf
        (Set.range fun lam : Fin m → ℝ ↦
          ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) :
            WithBot ℝ)) :=
  rfl

/-- The source value `z_LP`, represented as the supremum of the linear objective over the
linear-programming relaxation feasible set. -/
noncomputable def uncapacitated_facility_location_lp_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : WithBot ℝ :=
  sSup
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
      uncapacitated_facility_location_lp_feasible_set)

/-- `uncapacitated_facility_location_lp_value c f` unfolds to the supremum of the LP objective
over `uncapacitated_facility_location_lp_feasible_set`. -/
theorem uncapacitated_facility_location_lp_value_eq_sSup
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_lp_value c f =
      sSup
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
          uncapacitated_facility_location_lp_feasible_set) :=
  rfl

/-- Helper for Proposition 8.8: the flattened ambient space storing assignment variables
`y_ij` and opening variables `x_j` on a single sum type. -/
abbrev facilityLocationFlatVar (m n : ℕ) := (Fin m × Fin n) ⊕ Fin n

/-- Helper for Proposition 8.8: the split rows encoding `∑_j y_ij = 1` as the pair of
inequalities `∑_j y_ij ≤ 1` and `-∑_j y_ij ≤ -1`. -/
abbrev facilityLocationSplitRow (m : ℕ) := Fin m ⊕ Fin m

/-- Helper for Proposition 8.8: the easy-block rows encoding linking inequalities `y_ij ≤ x_j`
and upper bounds `x_j ≤ 1`. -/
abbrev facilityLocationEasyBlockRow (m n : ℕ) := (Fin m × Fin n) ⊕ Fin n

/-- Helper for Proposition 8.8: flatten a pair `(y, x)` into the sum-type ambient space used by
the generic Chapter 8.1 model. -/
def facilityLocationFlatten
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) :
    facilityLocationFlatVar m n → ℝ :=
  fun z ↦
    match z with
    | Sum.inl ij => xy.1 ij.1 ij.2
    | Sum.inr j => xy.2 j

/-- Helper for Proposition 8.8: unflatten a sum-type point back into assignment and opening
coordinates. -/
def facilityLocationUnflatten
    (v : facilityLocationFlatVar m n → ℝ) :
    (Fin m → Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i j ↦ v (Sum.inl (i, j)), fun j ↦ v (Sum.inr j))

/-- Helper for Proposition 8.8: the flattened objective vector with coefficients `c_ij` on the
assignment variables and `-f_j` on the opening variables. -/
def facilityLocationFlatObjective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    facilityLocationFlatVar m n → ℝ :=
  fun z ↦
    match z with
    | Sum.inl ij => c ij.1 ij.2
    | Sum.inr j => -f j

/-- Helper for Proposition 8.8: the split assignment matrix for the Chapter 8.1 generic model. -/
def facilityLocationSplitAssignmentMatrix :
    Matrix (facilityLocationSplitRow m) (facilityLocationFlatVar m n) ℝ :=
  fun row col ↦
    match row, col with
    | Sum.inl i, Sum.inl (i', _) => if i = i' then 1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr i, Sum.inl (i', _) => if i = i' then -1 else 0
    | Sum.inr _, Sum.inr _ => 0

/-- Helper for Proposition 8.8: the right-hand side of the split assignment inequalities. -/
def facilityLocationSplitAssignmentRhs : facilityLocationSplitRow m → ℝ :=
  Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

/-- Helper for Proposition 8.8: the easy-block matrix encoding `y_ij - x_j ≤ 0` and `x_j ≤ 1`
in flattened coordinates. -/
def facilityLocationEasyBlockMatrix :
    Matrix (facilityLocationEasyBlockRow m n) (facilityLocationFlatVar m n) ℝ :=
  fun row col ↦
    match row, col with
    | Sum.inl (i, j), Sum.inl (i', j') => if i = i' ∧ j = j' then 1 else 0
    | Sum.inl (_, j), Sum.inr j' => if j = j' then -1 else 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr j, Sum.inr j' => if j = j' then 1 else 0

/-- Helper for Proposition 8.8: the right-hand side of the flattened easy-block inequalities. -/
def facilityLocationEasyBlockRhs : facilityLocationEasyBlockRow m n → ℝ :=
  Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)

/-- Helper for Proposition 8.8: unflattening after flattening recovers the original pair `(y, x)`.
-/
theorem facilityLocationUnflatten_flatten
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) :
    facilityLocationUnflatten (m := m) (n := n) (facilityLocationFlatten xy) = xy := by
  rcases xy with ⟨y, x⟩
  -- Both components reduce definitionally once the sum-type cases are expanded.
  simp [facilityLocationUnflatten, facilityLocationFlatten]

/-- Helper for Proposition 8.8: flattening after unflattening recovers the original flat point. -/
theorem facilityLocationFlatten_unflatten
    (v : facilityLocationFlatVar m n → ℝ) :
    facilityLocationFlatten (m := m) (n := n)
      (facilityLocationUnflatten (m := m) (n := n) v) = v := by
  -- The flatten/unflatten pair is inverse by case splitting on the sum-type coordinate.
  funext z
  cases z with
  | inl ij =>
      cases ij
      rfl
  | inr j =>
      rfl

/-- Helper for Proposition 8.8: the flattened easy-block row `y_ij - x_j ≤ 0` evaluates to the
expected difference on the flat point. -/
lemma facilityLocationEasyBlockMatrix_mulVec_link
    (v : facilityLocationFlatVar m n → ℝ)
    (i : Fin m)
    (j : Fin n) :
    Matrix.mulVec (facilityLocationEasyBlockMatrix (m := m) (n := n)) v (Sum.inl (i, j)) =
      v (Sum.inl (i, j)) - v (Sum.inr j) := by
  -- `simp` collapses the row to the unique assignment coordinate and the matching opening
  -- coordinate.
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hsel :
      ∑ x : Fin m, ∑ x_1 : Fin n,
          (if i = x ∧ j = x_1 then v (Sum.inl (x, x_1)) else 0) =
        v (Sum.inl (i, j)) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hxi
      have hix : i ≠ x := fun h ↦ hxi h.symm
      simp [hix]
    · intro hi
      simp at hi
  simpa [sub_eq_add_neg, facilityLocationEasyBlockMatrix] using
    congrArg (fun t : ℝ ↦ t + -v (Sum.inr j)) hsel

/-- Helper for Proposition 8.8: the flattened easy-block row `x_j ≤ 1` reads off the opening
coordinate `x_j`. -/
lemma facilityLocationEasyBlockMatrix_mulVec_bound
    (v : facilityLocationFlatVar m n → ℝ)
    (j : Fin n) :
    Matrix.mulVec (facilityLocationEasyBlockMatrix (m := m) (n := n)) v (Sum.inr j) =
      v (Sum.inr j) := by
  -- The upper-bound row has a single nonzero coefficient on the opening variable `x_j`.
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  simp [facilityLocationEasyBlockMatrix]

/-- Helper for Proposition 8.8: the positive split assignment row evaluates to the assignment-row
sum `∑_j y_ij`. -/
lemma facilityLocationSplitAssignmentMatrix_mulVec_pos
    (v : facilityLocationFlatVar m n → ℝ)
    (i : Fin m) :
    Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n)) v (Sum.inl i) =
      ∑ j, v (Sum.inl (i, j)) := by
  -- The positive split row picks out exactly the assignment coordinates in row `i`.
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [facilityLocationSplitAssignmentMatrix]
  · intro x _ hxi
    have hix : i ≠ x := fun h ↦ hxi h.symm
    simp [facilityLocationSplitAssignmentMatrix, hix]
  · intro hi
    simp at hi

/-- Helper for Proposition 8.8: the negative split assignment row evaluates to
`-∑_j y_ij`. -/
lemma facilityLocationSplitAssignmentMatrix_mulVec_neg
    (v : facilityLocationFlatVar m n → ℝ)
    (i : Fin m) :
    Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n)) v (Sum.inr i) =
      -∑ j, v (Sum.inl (i, j)) := by
  -- The negative split row is the negated copy of the same assignment-row sum.
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [facilityLocationSplitAssignmentMatrix]
  · intro x _ hxi
    have hix : i ≠ x := fun h ↦ hxi h.symm
    simp [facilityLocationSplitAssignmentMatrix, hix]
  · intro hi
    simp at hi

/-- Helper for Proposition 8.8: the flattened objective vector evaluates to the original
facility-location objective on the unflattened point. -/
lemma facilityLocationFlatObjective_dotProduct
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) :
    dotProduct (facilityLocationFlatObjective (m := m) (n := n) c f)
        (facilityLocationFlatten (m := m) (n := n) xy) =
      uncapacitated_facility_location_objective c f xy := by
  rcases xy with ⟨y, x⟩
  -- Splitting the sum-type coordinates recovers the `y`-part and the `x`-part of the objective.
  rw [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
    uncapacitated_facility_location_objective_mk]
  simp [facilityLocationFlatObjective, facilityLocationFlatten]
  ring

/-- Helper for Proposition 8.8: the split assignment penalty with nonnegative multipliers `μ, ν`
collapses to the unrestricted penalty with multiplier `μ - ν`. -/
lemma facilityLocationSplitPenalty_eq
    (mu nu : Fin m → ℝ)
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) :
    dotProduct (Sum.elim mu nu)
        (facilityLocationSplitAssignmentRhs (m := m) -
          Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
            (facilityLocationFlatten (m := m) (n := n) xy)) =
      ∑ i, (mu i - nu i) * (1 - ∑ j, xy.1 i j) := by
  rcases xy with ⟨y, x⟩
  -- Evaluate the positive and negative split rows separately, then regroup the row penalties.
  have hExpand :
      dotProduct (Sum.elim mu nu)
          (facilityLocationSplitAssignmentRhs (m := m) -
            Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
              (facilityLocationFlatten (m := m) (n := n) (y, x))) =
        ∑ i, (mu i * (1 - ∑ j, y i j) + nu i * (-1 + ∑ j, y i j)) := by
    simp [dotProduct, Fintype.sum_sum_type, facilityLocationSplitAssignmentRhs,
      facilityLocationFlatten, facilityLocationSplitAssignmentMatrix_mulVec_pos,
      facilityLocationSplitAssignmentMatrix_mulVec_neg, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, left_distrib, ← Finset.sum_add_distrib]
  have hRegroup :
      ∑ i, (mu i * (1 - ∑ j, y i j) + nu i * (-1 + ∑ j, y i j)) =
        ∑ i, (mu i - nu i) * (1 - ∑ j, y i j) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  exact hExpand.trans hRegroup

/-- Helper for Proposition 8.8: the split-row penalized objective on the flattened variables
matches the facility-location Lagrangian objective with unrestricted multiplier `μ - ν`. -/
lemma splitLagrangianObjective_eq_facilityLocationLagrangianObjective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (mu nu : Fin m → ℝ)
    (xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)) :
    dotProduct (facilityLocationFlatObjective (m := m) (n := n) c f)
        (facilityLocationFlatten (m := m) (n := n) xy) +
      dotProduct (Sum.elim mu nu)
        (facilityLocationSplitAssignmentRhs (m := m) -
          Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
            (facilityLocationFlatten (m := m) (n := n) xy)) =
      facility_location_lagrangian_relaxation_value c f (fun i ↦ mu i - nu i) xy.2 xy.1 := by
  rcases xy with ⟨y, x⟩
  -- First rewrite the flattened objective and the split-row penalty in the original facility-
  -- location coordinates.
  rw [facilityLocationFlatObjective_dotProduct, facilityLocationSplitPenalty_eq,
    uncapacitated_facility_location_objective_mk, facility_location_lagrangian_relaxation_value]
  -- Then expand the split-row penalty into the row constants minus the rowwise assignment sums.
  have hpenalty :
      ∑ i, (mu i - nu i) * (1 - ∑ j, y i j) =
        (∑ i, (mu i - nu i)) - ∑ i, ∑ j, (mu i - nu i) * y i j := by
    have hmul :
        ∑ i, (mu i - nu i) * ∑ j, y i j =
          ∑ i, ∑ j, (mu i - nu i) * y i j := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mul_sum]
    calc
      ∑ i, (mu i - nu i) * (1 - ∑ j, y i j) =
          ∑ i, ((mu i - nu i) - (mu i - nu i) * ∑ j, y i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (∑ i, (mu i - nu i)) - ∑ i, ((mu i - nu i) * ∑ j, y i j) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i, (mu i - nu i)) - ∑ i, ∑ j, (mu i - nu i) * y i j := by
            rw [hmul]
  -- Finally, expand the Lagrangian coefficients and swap the double sums into the same normal
  -- form on both sides.
  rw [hpenalty]
  have hsumObjective :
      ∑ i, ∑ j, c i j * y i j =
        ∑ j, ∑ i, c i j * y i j := by
    rw [Finset.sum_comm]
  have hsumPenalty :
      ∑ i, ∑ j, (mu i - nu i) * y i j =
        ∑ j, ∑ i, (mu i - nu i) * y i j := by
    rw [Finset.sum_comm]
  have hfacilityPenaltyCombine :
      (∑ j, ∑ i, c i j * y i j) - (∑ j, ∑ i, (mu i - nu i) * y i j) =
        ∑ j, (∑ i, c i j * y i j - ∑ i, (mu i - nu i) * y i j) := by
    rw [← Finset.sum_sub_distrib]
  have hfacilitySplit :
      (∑ j, (∑ i, c i j * y i j - ∑ i, (mu i - nu i) * y i j)) - ∑ j, f j * x j =
        ∑ j, ((∑ i, c i j * y i j - ∑ i, (mu i - nu i) * y i j) - f j * x j) := by
    rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j +
        ((∑ i, (mu i - nu i)) - ∑ i, ∑ j, (mu i - nu i) * y i j) =
      (∑ i, (mu i - nu i)) +
        ((∑ i, ∑ j, c i j * y i j) - ∑ i, ∑ j, (mu i - nu i) * y i j - ∑ j, f j * x j) := by
          ring
    _ = (∑ i, (mu i - nu i)) +
        ((∑ j, ∑ i, c i j * y i j) - (∑ j, ∑ i, (mu i - nu i) * y i j) - ∑ j, f j * x j) := by
          rw [hsumObjective, hsumPenalty]
    _ = (∑ i, (mu i - nu i)) +
        ∑ j, ((∑ i, c i j * y i j - ∑ i, (mu i - nu i) * y i j) - f j * x j) := by
          rw [hfacilityPenaltyCombine, hfacilitySplit]
    _ = (∑ i, (mu i - nu i)) +
        ∑ j, ((∑ i, (c i j - (mu i - nu i)) * y i j) - f j * x j) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hrow :
              ∑ i, c i j * y i j - ∑ i, (mu i - nu i) * y i j =
                ∑ i, (c i j - (mu i - nu i)) * y i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
          rw [hrow]

/-- Helper for Proposition 8.8: the flattened variable owner reindexed to
`Fin (m * n + n)`. -/
private abbrev facilityLocationFlatVarEquiv (m n : ℕ) :
    facilityLocationFlatVar m n ≃ Fin (m * n + n) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

/-- Helper for Proposition 8.8: the split-row owner reindexed to `Fin (m + m)`. -/
private abbrev facilityLocationSplitRowEquiv (m : ℕ) :
    facilityLocationSplitRow m ≃ Fin (m + m) :=
  finSumFinEquiv

/-- Helper for Proposition 8.8: the easy-block matrix on explicit `Fin` owners. -/
private abbrev facilityLocationEasyBlockMatrixFin (m n : ℕ) :
    Matrix (Fin (m * n + n)) (Fin (m * n + n)) ℝ :=
  (facilityLocationEasyBlockMatrix (m := m) (n := n)).reindex
    (facilityLocationFlatVarEquiv m n) (facilityLocationFlatVarEquiv m n)

/-- Helper for Proposition 8.8: the easy-block right-hand side on explicit `Fin` owners. -/
private abbrev facilityLocationEasyBlockRhsFin (m n : ℕ) :
    Fin (m * n + n) → ℝ :=
  facilityLocationEasyBlockRhs (m := m) (n := n) ∘ (facilityLocationFlatVarEquiv m n).symm

/-- Helper for Proposition 8.8: the split assignment matrix on explicit `Fin` owners. -/
private abbrev facilityLocationSplitAssignmentMatrixFin (m n : ℕ) :
    Matrix (Fin (m + m)) (Fin (m * n + n)) ℝ :=
  (facilityLocationSplitAssignmentMatrix (m := m) (n := n)).reindex
    (facilityLocationSplitRowEquiv m) (facilityLocationFlatVarEquiv m n)

/-- Helper for Proposition 8.8: the split assignment right-hand side on explicit `Fin` owners. -/
private abbrev facilityLocationSplitAssignmentRhsFin (m : ℕ) :
    Fin (m + m) → ℝ :=
  facilityLocationSplitAssignmentRhs (m := m) ∘ (facilityLocationSplitRowEquiv m).symm

/-- Helper for Proposition 8.8: after reindexing the easy-block matrix to `Fin` owners, the
linking row still evaluates to `y_ij - x_j`. -/
lemma facilityLocationEasyBlockMatrixFin_mulVec_link
    (v : Fin (m * n + n) → ℝ)
    (i : Fin m)
    (j : Fin n) :
    Matrix.mulVec (facilityLocationEasyBlockMatrixFin m n) v
        (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) =
      v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) -
        v (facilityLocationFlatVarEquiv m n (Sum.inr j)) := by
  let eVar : facilityLocationFlatVar m n ≃ Fin (m * n + n) := facilityLocationFlatVarEquiv m n
  -- Reindex back to the sum-type owner, then reuse the already-proved row evaluation there.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (facilityLocationEasyBlockMatrix (m := m) (n := n)) v
      eVar.symm eVar.symm
  calc
    Matrix.mulVec (facilityLocationEasyBlockMatrixFin m n) v
        (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) =
      Matrix.mulVec (facilityLocationEasyBlockMatrix (m := m) (n := n)) (v ∘ eVar)
        (Sum.inl (i, j)) := by
        simpa [facilityLocationEasyBlockMatrixFin, eVar] using
          congrFun hmul (eVar (Sum.inl (i, j)))
    _ = (v ∘ eVar) (Sum.inl (i, j)) - (v ∘ eVar) (Sum.inr j) := by
        simpa [Function.comp_apply] using
          facilityLocationEasyBlockMatrix_mulVec_link (m := m) (n := n) (v := v ∘ eVar) i j
    _ = v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) -
        v (facilityLocationFlatVarEquiv m n (Sum.inr j)) := rfl

/-- Helper for Proposition 8.8: after reindexing the easy-block matrix to `Fin` owners, the
upper-bound row still reads off `x_j`. -/
lemma facilityLocationEasyBlockMatrixFin_mulVec_bound
    (v : Fin (m * n + n) → ℝ)
    (j : Fin n) :
    Matrix.mulVec (facilityLocationEasyBlockMatrixFin m n) v
        (facilityLocationFlatVarEquiv m n (Sum.inr j)) =
      v (facilityLocationFlatVarEquiv m n (Sum.inr j)) := by
  let eVar : facilityLocationFlatVar m n ≃ Fin (m * n + n) := facilityLocationFlatVarEquiv m n
  -- Reindex back to the sum-type owner, then use the original easy-block upper-bound row.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (facilityLocationEasyBlockMatrix (m := m) (n := n)) v
      eVar.symm eVar.symm
  calc
    Matrix.mulVec (facilityLocationEasyBlockMatrixFin m n) v
        (facilityLocationFlatVarEquiv m n (Sum.inr j)) =
      Matrix.mulVec (facilityLocationEasyBlockMatrix (m := m) (n := n)) (v ∘ eVar) (Sum.inr j) := by
        simpa [facilityLocationEasyBlockMatrixFin, eVar] using congrFun hmul (eVar (Sum.inr j))
    _ = (v ∘ eVar) (Sum.inr j) := by
        simpa [Function.comp_apply] using
          facilityLocationEasyBlockMatrix_mulVec_bound (m := m) (n := n) (v := v ∘ eVar) j
    _ = v (facilityLocationFlatVarEquiv m n (Sum.inr j)) := rfl

/-- Helper for Proposition 8.8: after reindexing the split assignment matrix to `Fin` owners, the
positive row still evaluates to `∑_j y_ij`. -/
lemma facilityLocationSplitAssignmentMatrixFin_mulVec_pos
    (v : Fin (m * n + n) → ℝ)
    (i : Fin m) :
    Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
        (facilityLocationSplitRowEquiv m (Sum.inl i)) =
      ∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) := by
  let eVar : facilityLocationFlatVar m n ≃ Fin (m * n + n) := facilityLocationFlatVarEquiv m n
  let eRow : facilityLocationSplitRow m ≃ Fin (m + m) := facilityLocationSplitRowEquiv m
  -- Reindex back to the sum-type row owner, then read off the positive assignment row there.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (facilityLocationSplitAssignmentMatrix (m := m) (n := n)) v
      eRow.symm eVar.symm
  calc
    Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
        (facilityLocationSplitRowEquiv m (Sum.inl i)) =
      Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
        (v ∘ eVar) (Sum.inl i) := by
        simpa [facilityLocationSplitAssignmentMatrixFin, eVar, eRow] using
          congrFun hmul (eRow (Sum.inl i))
    _ = ∑ j, (v ∘ eVar) (Sum.inl (i, j)) := by
        simpa [Function.comp_apply] using
          facilityLocationSplitAssignmentMatrix_mulVec_pos (m := m) (n := n) (v := v ∘ eVar) i
    _ = ∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rfl

/-- Helper for Proposition 8.8: after reindexing the split assignment matrix to `Fin` owners, the
negative row still evaluates to `-∑_j y_ij`. -/
lemma facilityLocationSplitAssignmentMatrixFin_mulVec_neg
    (v : Fin (m * n + n) → ℝ)
    (i : Fin m) :
    Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
        (facilityLocationSplitRowEquiv m (Sum.inr i)) =
      -∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) := by
  let eVar : facilityLocationFlatVar m n ≃ Fin (m * n + n) := facilityLocationFlatVarEquiv m n
  let eRow : facilityLocationSplitRow m ≃ Fin (m + m) := facilityLocationSplitRowEquiv m
  -- Reindex back to the sum-type row owner, then read off the negative assignment row there.
  have hmul :=
    Matrix.submatrix_mulVec_equiv (facilityLocationSplitAssignmentMatrix (m := m) (n := n)) v
      eRow.symm eVar.symm
  calc
    Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
        (facilityLocationSplitRowEquiv m (Sum.inr i)) =
      Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
        (v ∘ eVar) (Sum.inr i) := by
        have hrow' := congrFun hmul (eRow (Sum.inr i))
        calc
          Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
              (facilityLocationSplitRowEquiv m (Sum.inr i)) =
            Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
              (v ∘ eVar) (eRow.symm (eRow (Sum.inr i))) := by
                simpa [facilityLocationSplitAssignmentMatrixFin, eVar, eRow] using hrow'
          _ = Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
              (v ∘ eVar) (Sum.inr i) := by
                rw [eRow.symm_apply_apply]
    _ = -∑ j, (v ∘ eVar) (Sum.inl (i, j)) := by
        simpa [Function.comp_apply] using
          facilityLocationSplitAssignmentMatrix_mulVec_neg (m := m) (n := n) (v := v ∘ eVar) i
    _ = -∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) := by
        simp [eVar, Function.comp_apply]

/-- Helper for Proposition 8.8: an integral real in the interval `[0, 1]` is either `0` or `1`.
-/
lemma intEqZeroOrOneOfCastBetweenZeroAndOne
    (z : ℤ)
    (hz_nonneg : 0 ≤ (z : ℝ))
    (hz_le_one : (z : ℝ) ≤ 1) :
    z = 0 ∨ z = 1 := by
  -- Move the interval bounds back to `ℤ` and close the two-point interval arithmetically.
  have hz_nonneg' : 0 ≤ z := by
    exact_mod_cast hz_nonneg
  have hz_le_one' : z ≤ 1 := by
    exact_mod_cast hz_le_one
  omega

/-- Helper for Proposition 8.8: after the explicit `Fin` reindex, the easy-block feasible set is
exactly the continuous facility-location relaxation feasible set. -/
lemma facilityLocationFinReindexLagrangianFeasible_iff
    (v : Fin (m * n + n) → ℝ) :
    v ∈ easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
        (facilityLocationEasyBlockRhsFin m n) ↔
      facilityLocationUnflatten (m := m) (n := n)
          (v ∘ facilityLocationFlatVarEquiv m n) ∈
        uncapacitated_facility_location_lagrangian_feasible_set := by
  rw [mem_easy_block_feasible_set_iff,
    mem_uncapacitated_facility_location_lagrangian_feasible_set_iff]
  constructor
  · rintro ⟨hrows, hnonneg⟩
    -- Read the `Fin`-indexed inequalities back in the original facility-location coordinates.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      simpa [facilityLocationUnflatten, Function.comp_apply] using
        hnonneg (facilityLocationFlatVarEquiv m n (Sum.inl (i, j)))
    · intro i j
      have hdiff :
          v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) -
              v (facilityLocationFlatVarEquiv m n (Sum.inr j)) ≤ 0 := by
        have hrow :=
          hrows (facilityLocationFlatVarEquiv m n (Sum.inl (i, j)))
        rw [facilityLocationEasyBlockMatrixFin_mulVec_link] at hrow
        have hrow0 :
            v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) -
                v (facilityLocationFlatVarEquiv m n (Sum.inr j)) ≤ 0 := by
          simpa [facilityLocationEasyBlockRhs, facilityLocationFlatVarEquiv] using hrow
        exact hrow0
      exact sub_nonpos.mp <| by
        simpa [facilityLocationUnflatten, Function.comp_apply] using hdiff
    · intro j
      simpa [facilityLocationUnflatten, Function.comp_apply] using
        hnonneg (facilityLocationFlatVarEquiv m n (Sum.inr j))
    · intro j
      have hrow := hrows (facilityLocationFlatVarEquiv m n (Sum.inr j))
      rw [facilityLocationEasyBlockMatrixFin_mulVec_bound] at hrow
      have hbound : v (facilityLocationFlatVarEquiv m n (Sum.inr j)) ≤ 1 := by
        simpa [facilityLocationEasyBlockRhsFin, facilityLocationFlatVarEquiv] using hrow
      simpa [facilityLocationUnflatten, Function.comp_apply] using hbound
  · intro hv
    rcases hv with ⟨hy_nonneg, hlink, hx_nonneg, hx_le_one⟩
    -- Case-split on each reindexed row and coordinate to rebuild the `Fin`-indexed inequalities.
    refine ⟨?_, ?_⟩
    · intro r
      rcases hsplit : (facilityLocationFlatVarEquiv m n).symm r with ij | j
      · rcases ij with ⟨i, j⟩
        have hr : r = facilityLocationFlatVarEquiv m n (Sum.inl (i, j)) := by
          simpa [hsplit] using ((facilityLocationFlatVarEquiv m n).apply_symm_apply r).symm
        rw [hr]
        have hdiff :
            v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) -
                v (facilityLocationFlatVarEquiv m n (Sum.inr j)) ≤ 0 := by
          exact sub_nonpos.mpr <| by
            simpa [facilityLocationUnflatten, Function.comp_apply] using hlink i j
        have hrow :
            Matrix.mulVec (facilityLocationEasyBlockMatrixFin m n) v
                (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) ≤
              facilityLocationEasyBlockRhsFin m n
                (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) := by
          rw [facilityLocationEasyBlockMatrixFin_mulVec_link]
          simpa [facilityLocationEasyBlockRhs, facilityLocationFlatVarEquiv] using hdiff
        exact hrow
      · have hr : r = facilityLocationFlatVarEquiv m n (Sum.inr j) := by
          simpa [hsplit] using ((facilityLocationFlatVarEquiv m n).apply_symm_apply r).symm
        rw [hr]
        have hrow :
            Matrix.mulVec (facilityLocationEasyBlockMatrixFin m n) v
                (facilityLocationFlatVarEquiv m n (Sum.inr j)) ≤
              facilityLocationEasyBlockRhsFin m n
                (facilityLocationFlatVarEquiv m n (Sum.inr j)) := by
          rw [facilityLocationEasyBlockMatrixFin_mulVec_bound]
          simpa [facilityLocationEasyBlockRhsFin, facilityLocationFlatVarEquiv,
            facilityLocationUnflatten, Function.comp_apply] using hx_le_one j
        exact hrow
    · intro r
      rcases hsplit : (facilityLocationFlatVarEquiv m n).symm r with ij | j
      · rcases ij with ⟨i, j⟩
        have hr : r = facilityLocationFlatVarEquiv m n (Sum.inl (i, j)) := by
          simpa [hsplit] using ((facilityLocationFlatVarEquiv m n).apply_symm_apply r).symm
        rw [hr]
        simpa [facilityLocationUnflatten, Function.comp_apply] using hy_nonneg i j
      · have hr : r = facilityLocationFlatVarEquiv m n (Sum.inr j) := by
          simpa [hsplit] using ((facilityLocationFlatVarEquiv m n).apply_symm_apply r).symm
        rw [hr]
        simpa [facilityLocationUnflatten, Function.comp_apply] using hx_nonneg j

/-- Helper for Proposition 8.8: after the explicit `Fin` reindex, the Chapter 8.1 feasible set is
exactly the LP relaxation feasible set of the facility-location model. -/
lemma facilityLocationFinReindexLpFeasible_iff
    (v : Fin (m * n + n) → ℝ) :
    v ∈ lagrangian_integer_feasible_set
        (facilityLocationSplitAssignmentMatrixFin m n)
        (facilityLocationSplitAssignmentRhsFin m)
        (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n)) ↔
      facilityLocationUnflatten (m := m) (n := n)
          (v ∘ facilityLocationFlatVarEquiv m n) ∈
        uncapacitated_facility_location_lp_feasible_set := by
  rw [mem_lagrangian_integer_feasible_set_iff]
  rw [mem_uncapacitated_facility_location_lp_feasible_set_iff]
  constructor
  · rintro ⟨hEasy, hSplit⟩
    have hLag :=
      (facilityLocationFinReindexLagrangianFeasible_iff (m := m) (n := n) (v := v)).1 hEasy
    rcases hLag with ⟨hy_nonneg, hlink, hx_nonneg, hx_le_one⟩
    -- The easy block gives the continuous side constraints, and the split rows recover the row
    -- equalities.
    refine ⟨?_, hy_nonneg, hlink, hx_nonneg, hx_le_one⟩
    intro i
    have hpos :
        ∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) ≤ 1 := by
      have hrow := hSplit (facilityLocationSplitRowEquiv m (Sum.inl i))
      rw [facilityLocationSplitAssignmentMatrixFin_mulVec_pos] at hrow
      simpa [facilityLocationSplitAssignmentRhsFin, facilityLocationSplitRowEquiv] using hrow
    have hneg :
        -∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) ≤ -1 := by
      have hrow := hSplit (facilityLocationSplitRowEquiv m (Sum.inr i))
      rw [facilityLocationSplitAssignmentMatrixFin_mulVec_neg] at hrow
      have hsymm :
          (facilityLocationSplitRowEquiv m).symm
              (facilityLocationSplitRowEquiv m (Sum.inr i)) = Sum.inr i := by
        simpa [facilityLocationSplitRowEquiv] using
          (finSumFinEquiv_symm_apply_natAdd (m := m) i)
      have hrhs :
          facilityLocationSplitAssignmentRhsFin m
              (facilityLocationSplitRowEquiv m (Sum.inr i)) = -1 := by
        change facilityLocationSplitAssignmentRhs (m := m)
            ((facilityLocationSplitRowEquiv m).symm
              ((facilityLocationSplitRowEquiv m) (Sum.inr i))) = -1
        rw [hsymm, facilityLocationSplitAssignmentRhs]
        rfl
      have hneg0 :
          -∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) ≤ -1 := by
        rwa [hrhs] at hrow
      exact hneg0
    have hEq :
        ∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) = 1 := by
      linarith
    simpa [facilityLocationUnflatten, Function.comp_apply] using hEq
  · intro hv
    have hEasy :
        v ∈ easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n) := by
      refine (facilityLocationFinReindexLagrangianFeasible_iff (m := m) (n := n) (v := v)).2 ?_
      exact
        mem_uncapacitated_facility_location_lagrangian_feasible_set_of_mem_lp_feasible_set hv
    rcases (mem_uncapacitated_facility_location_lp_feasible_set_iff.mp hv) with
      ⟨hassign, -, _, _, _⟩
    -- Reindex each split row back to its facility row and insert the assignment equality.
    refine ⟨hEasy, ?_⟩
    intro r
    rcases hsplit : (facilityLocationSplitRowEquiv m).symm r with i | i
    · have hr : r = facilityLocationSplitRowEquiv m (Sum.inl i) := by
        simpa [hsplit] using ((facilityLocationSplitRowEquiv m).apply_symm_apply r).symm
      rw [hr]
      have hEq :
          ∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) = 1 := by
        simpa [facilityLocationUnflatten, Function.comp_apply] using hassign i
      have hrow :
          Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
              (facilityLocationSplitRowEquiv m (Sum.inl i)) ≤
            facilityLocationSplitAssignmentRhsFin m
              (facilityLocationSplitRowEquiv m (Sum.inl i)) := by
        rw [facilityLocationSplitAssignmentMatrixFin_mulVec_pos]
        simpa [facilityLocationSplitAssignmentRhsFin, facilityLocationSplitRowEquiv] using hEq.le
      exact hrow
    · have hr : r = facilityLocationSplitRowEquiv m (Sum.inr i) := by
        simpa [hsplit] using ((facilityLocationSplitRowEquiv m).apply_symm_apply r).symm
      rw [hr]
      have hEq :
          -∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) = -1 := by
        have hassign' :
            ∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) = 1 := by
          simpa [facilityLocationUnflatten, Function.comp_apply] using hassign i
        rw [hassign']
      have hrow :
          Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v
              (facilityLocationSplitRowEquiv m (Sum.inr i)) ≤
            facilityLocationSplitAssignmentRhsFin m
              (facilityLocationSplitRowEquiv m (Sum.inr i)) := by
        rw [facilityLocationSplitAssignmentMatrixFin_mulVec_neg]
        have hsymm :
            (facilityLocationSplitRowEquiv m).symm
                (facilityLocationSplitRowEquiv m (Sum.inr i)) = Sum.inr i := by
          simpa [facilityLocationSplitRowEquiv] using
            (finSumFinEquiv_symm_apply_natAdd (m := m) i)
        have hrhs :
            facilityLocationSplitAssignmentRhsFin m
                (facilityLocationSplitRowEquiv m (Sum.inr i)) = -1 := by
          change facilityLocationSplitAssignmentRhs (m := m)
              ((facilityLocationSplitRowEquiv m).symm
                ((facilityLocationSplitRowEquiv m) (Sum.inr i))) = -1
          rw [hsymm, facilityLocationSplitAssignmentRhs]
          rfl
        have hneg0 :
            -∑ j, v (facilityLocationFlatVarEquiv m n (Sum.inl (i, j))) ≤ -1 := by
          linarith
        rwa [hrhs]
      exact hrow

/-- Helper for Proposition 8.8: the canonical order embedding from `WithBot ℝ` into `EReal`
forgets only the unavailable top point. -/
private def realToWithTop : ℝ ↪o WithTop ℝ where
  toFun := fun r ↦ (r : WithTop ℝ)
  inj' := by
    intro a b h
    simpa using h
  map_rel_iff' := by
    intro a b
    simp

/-- Helper for Proposition 8.8: embed `WithBot ℝ` into `EReal` without creating any new finite
values. -/
private def withBotRealToEReal : WithBot ℝ ↪o EReal :=
  realToWithTop.withBotMap

/-- Helper for Proposition 8.8: the `WithBot`-to-`EReal` embedding sends real values to the same
real point in `EReal`. -/
@[simp] lemma withBotRealToEReal_coe (r : ℝ) :
    withBotRealToEReal (((r : ℝ) : WithBot ℝ)) = ((r : ℝ) : EReal) :=
  rfl

/-- Helper for Proposition 8.8: the `WithBot`-to-`EReal` embedding preserves the bottom element.
-/
@[simp] lemma withBotRealToEReal_bot :
    withBotRealToEReal (⊥ : WithBot ℝ) = (⊥ : EReal) :=
  rfl

/-- Helper for Proposition 8.8: the reindexed easy-block feasible set is convex because it is the
intersection of a polyhedron with the nonnegative orthant. -/
lemma facilityLocationEasyBlockFin_convex :
    Convex ℝ (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
      (facilityLocationEasyBlockRhsFin m n)) := by
  -- Convexity is inherited from the row-inequality polyhedron and the coordinatewise lower bound.
  exact
    (polyhedron_le_set_convex (facilityLocationEasyBlockMatrixFin m n)
      (facilityLocationEasyBlockRhsFin m n)).inter (convex_Ici 0)

/-- Helper for Proposition 8.8: the reindexed flat objective computes the same dot product as the
sum-type objective before reindexing. -/
lemma facilityLocationFlatObjectiveFin_dotProduct
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (v : Fin (m * n + n) → ℝ) :
    dotProduct
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        v =
      dotProduct (facilityLocationFlatObjective (m := m) (n := n) c f)
        (v ∘ facilityLocationFlatVarEquiv m n) := by
  -- Reindex the finite owner back to the sum-type coordinates in the dot product.
  exact
    comp_equiv_symm_dotProduct
      (u := facilityLocationFlatObjective (m := m) (n := n) c f)
      (x := v)
      (e := facilityLocationFlatVarEquiv m n)

/-- Helper for Proposition 8.8: the reindexed flat objective matches the original facility-location
objective on the unflattened point. -/
lemma facilityLocationFlatObjectiveFin_dotProduct_eq_objective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (v : Fin (m * n + n) → ℝ) :
    dotProduct
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        v =
      uncapacitated_facility_location_objective c f
        (facilityLocationUnflatten (m := m) (n := n)
          (v ∘ facilityLocationFlatVarEquiv m n)) := by
  -- First move the dot product back to the sum-type owner, then use the existing flatten bridge.
  rw [facilityLocationFlatObjectiveFin_dotProduct]
  simpa [Function.comp_apply, facilityLocationFlatten_unflatten] using
    facilityLocationFlatObjective_dotProduct (m := m) (n := n) c f
      (facilityLocationUnflatten (m := m) (n := n)
        (v ∘ facilityLocationFlatVarEquiv m n))

/-- Helper for Proposition 8.8: extract the positive split-row multipliers from a reindexed
Chapter 8.1 multiplier vector. -/
private def facilityLocationSplitMultiplierPos
    (lam : Fin (m + m) → ℝ) :
    Fin m → ℝ :=
  fun i ↦ lam (facilityLocationSplitRowEquiv m (Sum.inl i))

/-- Helper for Proposition 8.8: extract the negative split-row multipliers from a reindexed
Chapter 8.1 multiplier vector. -/
private def facilityLocationSplitMultiplierNeg
    (lam : Fin (m + m) → ℝ) :
    Fin m → ℝ :=
  fun i ↦ lam (facilityLocationSplitRowEquiv m (Sum.inr i))

/-- Helper for Proposition 8.8: the extracted positive/negative split multipliers reconstruct the
original `Fin (m + m)` multiplier vector. -/
lemma facilityLocationSplitMultiplier_reconstruct
    (lam : Fin (m + m) → ℝ) :
    Sum.elim
        (facilityLocationSplitMultiplierPos (m := m) lam)
        (facilityLocationSplitMultiplierNeg (m := m) lam) ∘
      (facilityLocationSplitRowEquiv m).symm = lam :=
by
  -- Reindex the `Fin (m + m)` owner back to the split-row sum type and read off each branch.
  funext r
  rcases hsplit : (facilityLocationSplitRowEquiv m).symm r with i | i
  · have hr : r = facilityLocationSplitRowEquiv m (Sum.inl i) := by
      simpa [hsplit] using ((facilityLocationSplitRowEquiv m).apply_symm_apply r).symm
    calc
      ((Sum.elim
          (facilityLocationSplitMultiplierPos (m := m) lam)
          (facilityLocationSplitMultiplierNeg (m := m) lam)) ∘
          (facilityLocationSplitRowEquiv m).symm) r =
          (Sum.elim
            (facilityLocationSplitMultiplierPos (m := m) lam)
            (facilityLocationSplitMultiplierNeg (m := m) lam)) (Sum.inl i) := by
              simp [Function.comp_apply, hsplit]
      _ = lam (facilityLocationSplitRowEquiv m (Sum.inl i)) := rfl
      _ = lam r := by rw [hr]
  · have hr : r = facilityLocationSplitRowEquiv m (Sum.inr i) := by
      simpa [hsplit] using ((facilityLocationSplitRowEquiv m).apply_symm_apply r).symm
    calc
      ((Sum.elim
          (facilityLocationSplitMultiplierPos (m := m) lam)
          (facilityLocationSplitMultiplierNeg (m := m) lam)) ∘
          (facilityLocationSplitRowEquiv m).symm) r =
          (Sum.elim
            (facilityLocationSplitMultiplierPos (m := m) lam)
            (facilityLocationSplitMultiplierNeg (m := m) lam)) (Sum.inr i) := by
              simp [Function.comp_apply, hsplit]
      _ = lam (facilityLocationSplitRowEquiv m (Sum.inr i)) := rfl
      _ = lam r := by rw [hr]

/-- Helper for Proposition 8.8: the reindexed split-row slack vector is exactly the original
split-row slack vector transported through the row equivalence. -/
lemma facilityLocationSplitAssignmentSlackFin_eq
    (v : Fin (m * n + n) → ℝ) :
    facilityLocationSplitAssignmentRhsFin m -
        Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v =
      (fun r ↦
        facilityLocationSplitAssignmentRhs (m := m) ((facilityLocationSplitRowEquiv m).symm r) -
          Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
            (v ∘ facilityLocationFlatVarEquiv m n) ((facilityLocationSplitRowEquiv m).symm r)) := by
  let eVar : facilityLocationFlatVar m n ≃ Fin (m * n + n) := facilityLocationFlatVarEquiv m n
  let eRow : facilityLocationSplitRow m ≃ Fin (m + m) := facilityLocationSplitRowEquiv m
  have hmul :=
    Matrix.submatrix_mulVec_equiv (facilityLocationSplitAssignmentMatrix (m := m) (n := n)) v
      eRow.symm eVar.symm
  -- The reindexed right-hand side and the reindexed matrix-vector product transport together.
  funext r
  have hmulr := congrFun hmul r
  simp [facilityLocationSplitAssignmentRhsFin, eRow, eVar, hmulr]

/-- Helper for Proposition 8.8: the reindexed Chapter 8.1 split objective matches the current
facility-location Lagrangian objective with multiplier `μ - ν`. -/
lemma splitFinLagrangianObjective_eq_facilityLocationLagrangianObjective
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin (m + m) → ℝ)
    (v : Fin (m * n + n) → ℝ) :
    dotProduct
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        v +
      dotProduct lam
        (facilityLocationSplitAssignmentRhsFin m -
          Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) =
      facility_location_lagrangian_relaxation_value c f
        (fun i ↦
          facilityLocationSplitMultiplierPos (m := m) lam i -
            facilityLocationSplitMultiplierNeg (m := m) lam i)
        (facilityLocationUnflatten (m := m) (n := n)
          (v ∘ facilityLocationFlatVarEquiv m n)).2
        (facilityLocationUnflatten (m := m) (n := n)
          (v ∘ facilityLocationFlatVarEquiv m n)).1 :=
by
  let eVar : facilityLocationFlatVar m n ≃ Fin (m * n + n) := facilityLocationFlatVarEquiv m n
  let eRow : facilityLocationSplitRow m ≃ Fin (m + m) := facilityLocationSplitRowEquiv m
  let slack : facilityLocationSplitRow m → ℝ :=
    facilityLocationSplitAssignmentRhs (m := m) -
      Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n)) (v ∘ eVar)
  let xy :
      (Fin m → Fin n → ℝ) × (Fin n → ℝ) :=
    facilityLocationUnflatten (m := m) (n := n) (v ∘ eVar)
  have hlam :
      lam ∘ eRow =
        Sum.elim
          (facilityLocationSplitMultiplierPos (m := m) lam)
          (facilityLocationSplitMultiplierNeg (m := m) lam) := by
    -- On each split-row branch, the positive and negative extracted multipliers recover `lam`.
    funext r
    cases r with
    | inl i =>
        rfl
    | inr i =>
        rfl
  have hslack :
      facilityLocationSplitAssignmentRhsFin m -
          Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v =
        slack ∘ eRow.symm := by
    -- The `Fin`-indexed split slack is just the original slack transported through the row
    -- equivalence.
    simpa [slack, eRow, eVar] using
      facilityLocationSplitAssignmentSlackFin_eq (m := m) (n := n) (v := v)
  -- Move both the objective vector and the split slack back to the original sum-type owners.
  calc
    dotProduct
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        v +
      dotProduct lam
        (facilityLocationSplitAssignmentRhsFin m -
          Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) =
        dotProduct (facilityLocationFlatObjective (m := m) (n := n) c f) (v ∘ eVar) +
          dotProduct
            (Sum.elim
              (facilityLocationSplitMultiplierPos (m := m) lam)
              (facilityLocationSplitMultiplierNeg (m := m) lam))
            slack := by
          rw [facilityLocationFlatObjectiveFin_dotProduct]
          rw [hslack]
          rw [dotProduct_comp_equiv_symm (u := lam) (x := slack) (e := eRow)]
          simp [hlam, eVar, eRow]
    _ =
        dotProduct (facilityLocationFlatObjective (m := m) (n := n) c f)
            (facilityLocationFlatten (m := m) (n := n) xy) +
          dotProduct
            (Sum.elim
              (facilityLocationSplitMultiplierPos (m := m) lam)
              (facilityLocationSplitMultiplierNeg (m := m) lam))
            (facilityLocationSplitAssignmentRhs (m := m) -
              Matrix.mulVec (facilityLocationSplitAssignmentMatrix (m := m) (n := n))
                (facilityLocationFlatten (m := m) (n := n) xy)) := by
          -- The unflatten/flatten equivalence lets us reuse the already-proved sum-type bridge.
          simp [xy, slack, facilityLocationFlatten_unflatten, eVar]
    _ =
        facility_location_lagrangian_relaxation_value c f
          (fun i ↦
            facilityLocationSplitMultiplierPos (m := m) lam i -
              facilityLocationSplitMultiplierNeg (m := m) lam i)
          xy.2 xy.1 := by
          simpa using
            splitLagrangianObjective_eq_facilityLocationLagrangianObjective
              (m := m) (n := n) c f
              (facilityLocationSplitMultiplierPos (m := m) lam)
              (facilityLocationSplitMultiplierNeg (m := m) lam)
              xy
    _ = facility_location_lagrangian_relaxation_value c f
          (fun i ↦
            facilityLocationSplitMultiplierPos (m := m) lam i -
              facilityLocationSplitMultiplierNeg (m := m) lam i)
          (facilityLocationUnflatten (m := m) (n := n)
            (v ∘ facilityLocationFlatVarEquiv m n)).2
          (facilityLocationUnflatten (m := m) (n := n)
            (v ∘ facilityLocationFlatVarEquiv m n)).1 := by
          rfl

/-- Helper for Proposition 8.8: the Proposition 8.7 binary optimizer also satisfies the
continuous relaxation used in Proposition 8.8. -/
lemma lagrangianSolution_memUncapacitatedRelaxationFeasibleSet
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) :
    lagrangian_relaxation_solution c f lam ∈
      uncapacitated_facility_location_lagrangian_feasible_set := by
  rw [mem_uncapacitated_facility_location_lagrangian_feasible_set_iff]
  rcases
      (mem_facility_location_lagrangian_relaxation_feasible_set_iff.mp
        (lagrangian_relaxation_solution_mem_feasible_set c f lam)) with
    ⟨hlink, hybin, hxbin⟩
  refine ⟨?_, hlink, ?_, ?_⟩
  · -- Binary assignment coordinates are automatically nonnegative.
    intro i j
    rcases hybin i j with hij | hij <;> simp [hij]
  · -- Binary opening coordinates are automatically nonnegative.
    intro j
    rcases hxbin j with hj | hj <;> simp [hj]
  · -- Binary opening coordinates are bounded above by `1`.
    intro j
    rcases hxbin j with hj | hj <;> simp [hj]

/-- Helper for Proposition 8.8: every continuous-relaxation column contribution is bounded by the
positive part of the corresponding reduced profit. -/
lemma relaxedColumnContribution_le_positivePartReducedProfit
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ uncapacitated_facility_location_lagrangian_feasible_set)
    (j : Fin n) :
    ((∑ i, (c i j - lam i) * xy.1 i j) - f j * xy.2 j) ≤
      max (facility_location_reduced_profit c f lam j) 0 := by
  rcases (mem_uncapacitated_facility_location_lagrangian_feasible_set_iff.mp hxy) with
    ⟨hy_nonneg, hlink, hx_nonneg, hx_le_one⟩
  have hterm :
      ∀ i, (c i j - lam i) * xy.1 i j ≤ max (c i j - lam i) 0 * xy.2 j := by
    intro i
    by_cases hij : 0 ≤ c i j - lam i
    · -- Positive coefficients are controlled by the linking inequality `y_ij ≤ x_j`.
      have hmax : max (c i j - lam i) 0 = c i j - lam i := max_eq_left hij
      calc
        (c i j - lam i) * xy.1 i j ≤ (c i j - lam i) * xy.2 j := by
          exact mul_le_mul_of_nonneg_left (hlink i j) hij
        _ = max (c i j - lam i) 0 * xy.2 j := by rw [hmax]
    · -- Nonpositive coefficients contribute at most `0`, hence at most the positive-part term.
      have hcoeff : c i j - lam i ≤ 0 := le_of_not_ge hij
      have hmax : max (c i j - lam i) 0 = 0 := max_eq_right hcoeff
      calc
        (c i j - lam i) * xy.1 i j ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hcoeff (hy_nonneg i j)
        _ = max (c i j - lam i) 0 * xy.2 j := by simp [hmax]
  have hsum :
      ∑ i, (c i j - lam i) * xy.1 i j ≤
        ∑ i, max (c i j - lam i) 0 * xy.2 j := by
    exact Finset.sum_le_sum fun i _ ↦ hterm i
  have hreduced :
      ((∑ i, max (c i j - lam i) 0) - f j) * xy.2 j ≤
        max (facility_location_reduced_profit c f lam j) 0 := by
    by_cases hr : 0 ≤ facility_location_reduced_profit c f lam j
    · -- If the reduced profit is nonnegative, the opening variable scales it by at most `1`.
      have hmax :
          max (facility_location_reduced_profit c f lam j) 0 =
            facility_location_reduced_profit c f lam j := max_eq_left hr
      have hmul :
          facility_location_reduced_profit c f lam j * xy.2 j ≤
            facility_location_reduced_profit c f lam j := by
        calc
          facility_location_reduced_profit c f lam j * xy.2 j ≤
              facility_location_reduced_profit c f lam j * 1 := by
                exact mul_le_mul_of_nonneg_left (hx_le_one j) hr
          _ = facility_location_reduced_profit c f lam j := by ring_nf
      calc
        ((∑ i, max (c i j - lam i) 0) - f j) * xy.2 j =
            facility_location_reduced_profit c f lam j * xy.2 j := by
              rw [facility_location_reduced_profit]
        _ ≤ facility_location_reduced_profit c f lam j := hmul
        _ = max (facility_location_reduced_profit c f lam j) 0 := by rw [hmax]
    · -- If the reduced profit is nonpositive, the column contribution is at most `0`.
      have hrle : facility_location_reduced_profit c f lam j ≤ 0 := le_of_not_ge hr
      have hmax :
          max (facility_location_reduced_profit c f lam j) 0 = 0 := max_eq_right hrle
      calc
        ((∑ i, max (c i j - lam i) 0) - f j) * xy.2 j =
            facility_location_reduced_profit c f lam j * xy.2 j := by
              rw [facility_location_reduced_profit]
        _ ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hrle (hx_nonneg j)
        _ = max (facility_location_reduced_profit c f lam j) 0 := by rw [hmax]
  -- First replace every column term by its positive-part upper bound, then factor out `x_j`.
  calc
    ((∑ i, (c i j - lam i) * xy.1 i j) - f j * xy.2 j) ≤
        (∑ i, max (c i j - lam i) 0 * xy.2 j) - f j * xy.2 j := by
          exact sub_le_sub_right hsum _
    _ = ((∑ i, max (c i j - lam i) 0) * xy.2 j) - f j * xy.2 j := by
          rw [← Finset.sum_mul]
    _ = ((∑ i, max (c i j - lam i) 0) - f j) * xy.2 j := by
          rw [← sub_mul]
    _ ≤ max (facility_location_reduced_profit c f lam j) 0 := hreduced

/-- Helper for Proposition 8.8: on LP-feasible points the assignment-equality penalty vanishes, so
the Lagrangian objective agrees with the original LP objective. -/
lemma lagrangianObjective_eq_objective_of_memLpFeasibleSet
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ uncapacitated_facility_location_lp_feasible_set) :
    facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1 =
      uncapacitated_facility_location_objective c f xy := by
  rcases xy with ⟨y, x⟩
  rcases (mem_uncapacitated_facility_location_lp_feasible_set_iff.mp hxy) with
    ⟨hassign, -, -, -, -⟩
  have hrow :
      ∀ i, lam i + ∑ j, (c i j - lam i) * y i j = ∑ j, c i j * y i j := by
    intro i
    -- Use the row equation `∑_j y_ij = 1` to cancel the Lagrange multiplier in row `i`.
    calc
      lam i + ∑ j, (c i j - lam i) * y i j =
          lam i + ((∑ j, c i j * y i j) - ∑ j, lam i * y i j) := by
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib]
      _ = lam i + ((∑ j, c i j * y i j) - lam i * ∑ j, y i j) := by
            rw [← Finset.mul_sum]
      _ = lam i + ((∑ j, c i j * y i j) - lam i * 1) := by rw [hassign i]
      _ = ∑ j, c i j * y i j := by
            ring_nf
  -- Reindex the double sums rowwise and cancel the vanished penalty.
  calc
    facility_location_lagrangian_relaxation_value c f lam x y =
        ((∑ i, lam i) + ∑ i, ∑ j, (c i j - lam i) * y i j) - ∑ j, f j * x j := by
          rw [facility_location_lagrangian_relaxation_value, Finset.sum_sub_distrib,
            Finset.sum_comm]
          ring_nf
    _ = (∑ i, ∑ j, c i j * y i j) - ∑ j, f j * x j := by
          congr 1
          calc
            (∑ i, lam i) + ∑ i, ∑ j, (c i j - lam i) * y i j =
                ∑ i, (lam i + ∑ j, (c i j - lam i) * y i j) := by
                  rw [← Finset.sum_add_distrib]
            _ = ∑ i, ∑ j, c i j * y i j := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  exact hrow i
    _ = uncapacitated_facility_location_objective c f (y, x) := by
          rw [uncapacitated_facility_location_objective_mk]

/-- Helper for Proposition 8.8: every feasible point of the continuous relaxation is bounded above
by the closed-form expression from part (i). -/
lemma relaxationPointValue_le_closedForm
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ)
    {xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ)}
    (hxy : xy ∈ uncapacitated_facility_location_lagrangian_feasible_set) :
    facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1 ≤
      (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i := by
  have hcolumn :
      ∑ j, ((∑ i, (c i j - lam i) * xy.1 i j) - f j * xy.2 j) ≤
        ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
    -- Sum the columnwise positive-part bounds across all facilities.
    exact Finset.sum_le_sum fun j _ ↦
      relaxedColumnContribution_le_positivePartReducedProfit c f lam hxy j
  -- Add the constant `∑_i λ_i` to the summed column bound.
  calc
    facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1 =
        (∑ i, lam i) + ∑ j, ((∑ i, (c i j - lam i) * xy.1 i j) - f j * xy.2 j) := by
          rfl
    _ ≤ (∑ i, lam i) + ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_left hcolumn (∑ i, lam i)
    _ = (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i := by
          rw [add_comm]

/-- Helper for Proposition 8.8: every LP-feasible point is bounded above by every Lagrangian
relaxation value, so the LP value is at most the dual value. -/
lemma uncapacitatedFacilityLocation_lpValue_le_lagrangianDualValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_lp_value c f ≤
      uncapacitated_facility_location_lagrangian_dual_value c f := by
  classical
  rw [uncapacitated_facility_location_lagrangian_dual_value_eq_sInf]
  refine le_csInf ?_ ?_
  · refine ⟨((uncapacitated_facility_location_lagrangian_relaxation_value c f 0 : ℝ) :
      WithBot ℝ), ?_⟩
    exact ⟨0, rfl⟩
  rintro _ ⟨lam, rfl⟩
  rw [uncapacitated_facility_location_lp_value_eq_sSup]
  let S : Set (WithBot ℝ) :=
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
      uncapacitated_facility_location_lp_feasible_set)
  change sSup S ≤ ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) :
    WithBot ℝ)
  by_cases hS : S.Nonempty
  · refine csSup_le hS ?_
    rintro _ ⟨xy, hxy, rfl⟩
    have hfeas :
        xy ∈ uncapacitated_facility_location_lagrangian_feasible_set :=
      mem_uncapacitated_facility_location_lagrangian_feasible_set_of_mem_lp_feasible_set hxy
    have hBdd :
        BddAbove
          ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
              facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1) ''
            uncapacitated_facility_location_lagrangian_feasible_set) := by
      refine ⟨(∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i, ?_⟩
      rintro _ ⟨xy', hxy', rfl⟩
      exact relaxationPointValue_le_closedForm c f lam hxy'
    have hcandidateReal :
        facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1 ≤
          uncapacitated_facility_location_lagrangian_relaxation_value c f lam := by
      rw [uncapacitated_facility_location_lagrangian_relaxation_value_eq_sSup]
      exact le_csSup hBdd ⟨xy, hfeas, rfl⟩
    -- Rewrite the candidate value back to the original LP objective before inserting it into the
    -- relaxation supremum.
    exact
      (show ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ) ≤
          ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) : WithBot ℝ)
        by
          rw [← lagrangianObjective_eq_objective_of_memLpFeasibleSet c f lam hxy]
          exact_mod_cast hcandidateReal)
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty]
    simp

/-- Closed form for Proposition 8.8 (1): for any given `λ ∈ ℝ^m`, the
Lagrangian-relaxation value satisfies
`z_LR(λ) = ∑_j ((∑_i (c_ij - λ_i)^+ - f_j)^+) + ∑_i λ_i`. -/
theorem uncapacitated_facility_location_lagrangian_relaxation_value_eq
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) :
    uncapacitated_facility_location_lagrangian_relaxation_value c f lam =
      (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i := by
  rw [uncapacitated_facility_location_lagrangian_relaxation_value_eq_sSup]
  apply le_antisymm
  · have hNonempty :
        ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
            facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1) ''
          uncapacitated_facility_location_lagrangian_feasible_set).Nonempty := by
      refine ⟨facility_location_lagrangian_relaxation_value c f lam
        (lagrangian_relaxation_solution c f lam).2
        (lagrangian_relaxation_solution c f lam).1, ?_⟩
      exact ⟨lagrangian_relaxation_solution c f lam,
        lagrangianSolution_memUncapacitatedRelaxationFeasibleSet c f lam, rfl⟩
    exact csSup_le hNonempty fun _ hx ↦ by
      rcases hx with ⟨xy, hxy, rfl⟩
      exact relaxationPointValue_le_closedForm c f lam hxy
  · -- Insert the Proposition 8.7 optimizer as a witness for the supremum.
    have hBdd :
        BddAbove
          ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
              facility_location_lagrangian_relaxation_value c f lam xy.2 xy.1) ''
            uncapacitated_facility_location_lagrangian_feasible_set) := by
      refine ⟨(∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i, ?_⟩
      rintro _ ⟨xy, hxy, rfl⟩
      exact relaxationPointValue_le_closedForm c f lam hxy
    refine le_csSup hBdd ?_
    refine ⟨lagrangian_relaxation_solution c f lam,
      lagrangianSolution_memUncapacitatedRelaxationFeasibleSet c f lam, ?_⟩
    -- The Proposition 8.7 optimizer attains the positive-part bound in every column.
    change facility_location_lagrangian_relaxation_value c f lam
        (lagrangian_relaxation_solution c f lam).2
        (lagrangian_relaxation_solution c f lam).1 =
      (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i
    rw [lagrangian_relaxation_solution_assignment, lagrangian_relaxation_solution_open]
    calc
      facility_location_lagrangian_relaxation_value c f lam
          (lagrangian_relaxation_open_decision c f lam)
          (lagrangian_relaxation_assignment_decision c f lam) =
            (∑ i, lam i) + ∑ j,
              ((∑ i, (c i j - lam i) *
                  lagrangian_relaxation_assignment_decision c f lam i j) -
                f j * lagrangian_relaxation_open_decision c f lam j) := by
                  rfl
      _ = (∑ i, lam i) + ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact solution_column_objective_eq_positive_part_reduced_profit c f lam j
      _ = (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i := by
            rw [add_comm]

/-- Helper for Proposition 8.8: the Proposition 8.7 optimizer still attains the continuous
facility-location relaxation value from Proposition 8.8 (1). -/
lemma lagrangianSolution_attainsUncapacitatedRelaxationValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) :
    facility_location_lagrangian_relaxation_value c f lam
        (lagrangian_relaxation_solution c f lam).2
        (lagrangian_relaxation_solution c f lam).1 =
      uncapacitated_facility_location_lagrangian_relaxation_value c f lam :=
by
  -- Evaluate the explicit Proposition 8.7 optimizer columnwise, then rewrite the resulting
  -- closed form to Proposition 8.8 (1).
  calc
    facility_location_lagrangian_relaxation_value c f lam
        (lagrangian_relaxation_solution c f lam).2
        (lagrangian_relaxation_solution c f lam).1 =
          (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i := by
            rw [lagrangian_relaxation_solution_assignment, lagrangian_relaxation_solution_open]
            calc
              facility_location_lagrangian_relaxation_value c f lam
                  (lagrangian_relaxation_open_decision c f lam)
                  (lagrangian_relaxation_assignment_decision c f lam) =
                    (∑ i, lam i) + ∑ j,
                      ((∑ i, (c i j - lam i) *
                          lagrangian_relaxation_assignment_decision c f lam i j) -
                        f j * lagrangian_relaxation_open_decision c f lam j) := by
                          rfl
              _ = (∑ i, lam i) + ∑ j, max (facility_location_reduced_profit c f lam j) 0 := by
                    congr 1
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    exact solution_column_objective_eq_positive_part_reduced_profit c f lam j
              _ = (∑ j, max (facility_location_reduced_profit c f lam j) 0) + ∑ i, lam i := by
                    rw [add_comm]
    _ = uncapacitated_facility_location_lagrangian_relaxation_value c f lam := by
          rw [uncapacitated_facility_location_lagrangian_relaxation_value_eq]

/-- Helper for Proposition 8.8: flattening and reindexing the Proposition 8.7 optimizer produces
an integral point of the reindexed easy block. -/
lemma lagrangianSolution_flattenFin_mem_pureIntegerPoints
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin m → ℝ) :
    (facilityLocationFlatten (m := m) (n := n) (lagrangian_relaxation_solution c f lam) ∘
        (facilityLocationFlatVarEquiv m n).symm) ∈
      pure_integer_points (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
        (facilityLocationEasyBlockRhsFin m n)) :=
by
  let v :
      Fin (m * n + n) → ℝ :=
    facilityLocationFlatten (m := m) (n := n) (lagrangian_relaxation_solution c f lam) ∘
      (facilityLocationFlatVarEquiv m n).symm
  have hvcomp :
      v ∘ facilityLocationFlatVarEquiv m n =
        facilityLocationFlatten (m := m) (n := n) (lagrangian_relaxation_solution c f lam) := by
    -- Reindexing forward and back on the flat owner is definitionally the identity.
    funext z
    simp [v]
  rw [mem_pure_integer_points_iff_forall]
  refine ⟨?_, ?_⟩
  · -- The explicit Proposition 8.7 optimizer is already feasible for the continuous relaxation.
    refine (facilityLocationFinReindexLagrangianFeasible_iff (m := m) (n := n) (v := v)).2 ?_
    rw [hvcomp, facilityLocationUnflatten_flatten]
    exact lagrangianSolution_memUncapacitatedRelaxationFeasibleSet (m := m) (n := n) c f lam
  · -- Every reindexed coordinate is one of the binary values `0` or `1`, hence integral.
    intro r
    rcases hsplit : (facilityLocationFlatVarEquiv m n).symm r with ij | j
    · rcases ij with ⟨i, j⟩
      rcases
          (mem_facility_location_lagrangian_relaxation_feasible_set_iff.mp
            (lagrangian_relaxation_solution_mem_feasible_set c f lam)).2.1 i j with hij | hij
      · refine ⟨0, ?_⟩
        simpa [v, hsplit, facilityLocationFlatten] using hij
      · refine ⟨1, ?_⟩
        simpa [v, hsplit, facilityLocationFlatten] using hij
    · have hcoord :
        v r = (lagrangian_relaxation_solution c f lam).2 j := by
          simp [v, hsplit, facilityLocationFlatten]
      rcases
          (mem_facility_location_lagrangian_relaxation_feasible_set_iff.mp
            (lagrangian_relaxation_solution_mem_feasible_set c f lam)).2.2 j with hj | hj
      · refine ⟨0, ?_⟩
        simpa [v, hsplit, facilityLocationFlatten] using hj
      · refine ⟨1, ?_⟩
        simpa [v, hsplit, facilityLocationFlatten] using hj

/-- Helper for Proposition 8.8: before any convex-hull rewrite, the reindexed split Lagrangian
objective image over the easy block is exactly the current facility-location Lagrangian objective
image over `uncapacitated_facility_location_lagrangian_feasible_set`. -/
lemma facilityLocationFinLagrangianObjectiveImage_eq
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin (m + m) → ℝ) :
    Set.image
        (fun v : Fin (m * n + n) → ℝ ↦
          ((dotProduct
              ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
                (facilityLocationFlatVarEquiv m n).symm)
              v +
            dotProduct lam
              (facilityLocationSplitAssignmentRhsFin m -
                Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) : ℝ) : EReal))
        (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n)) =
      Set.image
        (fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
          ((facility_location_lagrangian_relaxation_value c f
              (fun i ↦
                facilityLocationSplitMultiplierPos (m := m) lam i -
                  facilityLocationSplitMultiplierNeg (m := m) lam i)
              xy.2 xy.1 : ℝ) : EReal))
        uncapacitated_facility_location_lagrangian_feasible_set := by
  -- Both directions use the same `Fin`/sum-type reindexing bridge for feasible points and the
  -- pointwise split-objective normalization established above.
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨facilityLocationUnflatten (m := m) (n := n)
        (v ∘ facilityLocationFlatVarEquiv m n), ?_, ?_⟩
    · exact (facilityLocationFinReindexLagrangianFeasible_iff (m := m) (n := n) (v := v)).1 hv
    · simpa using
        congrArg
          (fun t : ℝ ↦ (t : EReal))
          (splitFinLagrangianObjective_eq_facilityLocationLagrangianObjective
            (m := m) (n := n) c f lam v).symm
  · rintro ⟨xy, hxy, rfl⟩
    let v : Fin (m * n + n) → ℝ :=
      facilityLocationFlatten (m := m) (n := n) xy ∘
        (facilityLocationFlatVarEquiv m n).symm
    have hvComp :
        v ∘ facilityLocationFlatVarEquiv m n =
          facilityLocationFlatten (m := m) (n := n) xy := by
      -- Reindexing forward after reindexing backward is the identity on flat coordinates.
      funext z
      simp [v]
    have hvUnflatten :
        facilityLocationUnflatten (m := m) (n := n)
            (v ∘ facilityLocationFlatVarEquiv m n) = xy := by
      -- Flattening then unflattening is the identity on the facility-location coordinates.
      rw [hvComp, facilityLocationUnflatten_flatten]
    refine ⟨v, ?_, ?_⟩
    · -- Reflatten the facility-location point and transport feasibility back to `Fin` owners.
      refine (facilityLocationFinReindexLagrangianFeasible_iff (m := m) (n := n) (v := v)).2 ?_
      rw [hvUnflatten]
      exact hxy
    · -- The reindexed split objective is definitionally the same point after reflattening.
      calc
        ((dotProduct
            ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
              (facilityLocationFlatVarEquiv m n).symm)
            v +
          dotProduct lam
            (facilityLocationSplitAssignmentRhsFin m -
              Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) : ℝ) : EReal) =
            ((facility_location_lagrangian_relaxation_value c f
                (fun i ↦
                  facilityLocationSplitMultiplierPos (m := m) lam i -
                    facilityLocationSplitMultiplierNeg (m := m) lam i)
                (facilityLocationUnflatten (m := m) (n := n)
                  (v ∘ facilityLocationFlatVarEquiv m n)).2
                (facilityLocationUnflatten (m := m) (n := n)
                  (v ∘ facilityLocationFlatVarEquiv m n)).1 : ℝ) : EReal) := by
              exact
                congrArg
                  (fun t : ℝ ↦ (t : EReal))
                  (splitFinLagrangianObjective_eq_facilityLocationLagrangianObjective
                    (m := m) (n := n) c f lam v)
        _ =
            ((facility_location_lagrangian_relaxation_value c f
                (fun i ↦
                  facilityLocationSplitMultiplierPos (m := m) lam i -
                    facilityLocationSplitMultiplierNeg (m := m) lam i)
                xy.2 xy.1 : ℝ) : EReal) := by
              rw [hvUnflatten]

/-- Helper for Proposition 8.8: the reindexed split LP objective image is exactly the current
facility-location LP objective image after embedding real objective values into `EReal`. -/
lemma facilityLocationFinLpObjectiveImage_eq
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    Set.image
        (fun v : Fin (m * n + n) → ℝ ↦
          ((dotProduct
              ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
                (facilityLocationFlatVarEquiv m n).symm)
              v : ℝ) : EReal))
        (lagrangian_integer_feasible_set
          (facilityLocationSplitAssignmentMatrixFin m n)
          (facilityLocationSplitAssignmentRhsFin m)
          (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
            (facilityLocationEasyBlockRhsFin m n))) =
      Set.image
        (fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
          ((uncapacitated_facility_location_objective c f xy : ℝ) : EReal))
        uncapacitated_facility_location_lp_feasible_set := by
  -- The LP feasible-set reindexing and the objective reindexing are already available pointwise,
  -- so the image-set bridge is just a two-sided witness argument.
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨facilityLocationUnflatten (m := m) (n := n)
        (v ∘ facilityLocationFlatVarEquiv m n), ?_, ?_⟩
    · exact (facilityLocationFinReindexLpFeasible_iff (m := m) (n := n) (v := v)).1 hv
    · simpa using
        congrArg
          (fun t : ℝ ↦ (t : EReal))
          (facilityLocationFlatObjectiveFin_dotProduct_eq_objective
            (m := m) (n := n) c f v).symm
  · rintro ⟨xy, hxy, rfl⟩
    let v : Fin (m * n + n) → ℝ :=
      facilityLocationFlatten (m := m) (n := n) xy ∘
        (facilityLocationFlatVarEquiv m n).symm
    have hvComp :
        v ∘ facilityLocationFlatVarEquiv m n =
          facilityLocationFlatten (m := m) (n := n) xy := by
      -- Reindexing forward after reindexing backward is the identity on flat coordinates.
      funext z
      simp [v]
    have hvUnflatten :
        facilityLocationUnflatten (m := m) (n := n)
            (v ∘ facilityLocationFlatVarEquiv m n) = xy := by
      -- Flattening then unflattening is the identity on the facility-location coordinates.
      rw [hvComp, facilityLocationUnflatten_flatten]
    refine ⟨v, ?_, ?_⟩
    · -- Reflatten the LP-feasible facility-location point and move it to the generic owner.
      refine (facilityLocationFinReindexLpFeasible_iff (m := m) (n := n) (v := v)).2 ?_
      rw [hvUnflatten]
      exact hxy
    · -- The reindexed flat objective computes the same real value on the reflattened point.
      calc
        ((dotProduct
            ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
              (facilityLocationFlatVarEquiv m n).symm)
            v : ℝ) : EReal) =
            ((uncapacitated_facility_location_objective c f
                (facilityLocationUnflatten (m := m) (n := n)
                  (v ∘ facilityLocationFlatVarEquiv m n)) : ℝ) : EReal) := by
              exact
                congrArg
                  (fun t : ℝ ↦ (t : EReal))
                  (facilityLocationFlatObjectiveFin_dotProduct_eq_objective
                    (m := m) (n := n) c f v)
        _ = ((uncapacitated_facility_location_objective c f xy : ℝ) : EReal) := by
              rw [hvUnflatten]

/-- Helper for Proposition 8.8: combine the easy-block inequalities `A₂ *ᵥ x ≤ b₂` and the
coordinatewise nonnegativity constraints `0 ≤ x` into a single polyhedral system. -/
private abbrev easyBlockPolyhedronMatrix
    {r n : ℕ}
    (A₂ : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin (r + n)) (Fin n) ℝ :=
  (Matrix.fromRows A₂ (-(1 : Matrix (Fin n) (Fin n) ℝ))).submatrix
    finSumFinEquiv.symm (Equiv.refl _)

/-- Helper for Proposition 8.8: the right-hand side for the single-matrix presentation of
`easy_block_feasible_set A₂ b₂`. -/
private abbrev easyBlockPolyhedronRhs
    {r n : ℕ}
    (b₂ : Fin r → ℝ) :
    Fin (r + n) → ℝ :=
  Sum.elim b₂ (fun _ ↦ 0) ∘ finSumFinEquiv.symm

/-- Helper for Proposition 8.8: `easy_block_feasible_set A₂ b₂` is exactly the polyhedron cut out
by `easyBlockPolyhedronMatrix A₂` and `easyBlockPolyhedronRhs b₂`. -/
lemma mem_easyBlockPolyhedron_iff
    {r n : ℕ}
    (A₂ : Matrix (Fin r) (Fin n) ℝ)
    (b₂ : Fin r → ℝ)
    (x : Fin n → ℝ) :
    x ∈ polyhedron_le_set (easyBlockPolyhedronMatrix A₂) (easyBlockPolyhedronRhs b₂) ↔
      x ∈ easy_block_feasible_set A₂ b₂ := by
  let Araw : Matrix (Fin r ⊕ Fin n) (Fin n) ℝ :=
    Matrix.fromRows A₂ (-(1 : Matrix (Fin n) (Fin n) ℝ))
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw x finSumFinEquiv.symm (Equiv.refl _)
  rw [mem_polyhedron_le_set_iff, mem_easy_block_feasible_set_iff]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      have hrow := hx (finSumFinEquiv (Sum.inl i))
      have hEq :
          (easyBlockPolyhedronMatrix A₂ *ᵥ x) (finSumFinEquiv (Sum.inl i)) =
            (Araw *ᵥ x) (Sum.inl i) := by
        simpa [easyBlockPolyhedronMatrix, Araw] using congrFun hmul (finSumFinEquiv (Sum.inl i))
      have hRhs :
          easyBlockPolyhedronRhs (r := r) (n := n) b₂ (finSumFinEquiv (Sum.inl i)) = b₂ i := by
        simp [easyBlockPolyhedronRhs]
      rw [hEq, hRhs] at hrow
      simpa [Araw, Matrix.fromRows_mulVec] using hrow
    · intro j
      have hrow := hx (finSumFinEquiv (Sum.inr j))
      have hEq :
          (easyBlockPolyhedronMatrix A₂ *ᵥ x) (finSumFinEquiv (Sum.inr j)) =
            (Araw *ᵥ x) (Sum.inr j) := by
        simpa [easyBlockPolyhedronMatrix, Araw] using congrFun hmul (finSumFinEquiv (Sum.inr j))
      have hRhs :
          easyBlockPolyhedronRhs (r := r) (n := n) b₂ (finSumFinEquiv (Sum.inr j)) = 0 := by
        simp [easyBlockPolyhedronRhs]
      rw [hEq, hRhs] at hrow
      have hneg : -x j ≤ 0 := by
        simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec] using hrow
      exact neg_nonpos.mp hneg
  · rintro ⟨hxA, hxNonneg⟩
    intro row
    rcases hsplit : finSumFinEquiv.symm row with i | j
    · have hr : row = finSumFinEquiv (Sum.inl i) := by
        simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
      rw [hr]
      have hrow :
          (easyBlockPolyhedronMatrix A₂ *ᵥ x) (finSumFinEquiv (Sum.inl i)) ≤
            easyBlockPolyhedronRhs (r := r) (n := n) b₂ (finSumFinEquiv (Sum.inl i)) := by
        have hEq :
            (easyBlockPolyhedronMatrix A₂ *ᵥ x) (finSumFinEquiv (Sum.inl i)) =
              (Araw *ᵥ x) (Sum.inl i) := by
          simpa [easyBlockPolyhedronMatrix, Araw] using
            congrFun hmul (finSumFinEquiv (Sum.inl i))
        have hRhs :
            easyBlockPolyhedronRhs (r := r) (n := n) b₂ (finSumFinEquiv (Sum.inl i)) = b₂ i := by
          simp [easyBlockPolyhedronRhs]
        rw [hEq, hRhs]
        simpa [Araw, Matrix.fromRows_mulVec] using hxA i
      exact hrow
    · have hr : row = finSumFinEquiv (Sum.inr j) := by
        simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
      rw [hr]
      have hrow :
          (easyBlockPolyhedronMatrix A₂ *ᵥ x) (finSumFinEquiv (Sum.inr j)) ≤
            easyBlockPolyhedronRhs (r := r) (n := n) b₂ (finSumFinEquiv (Sum.inr j)) := by
        have hEq :
            (easyBlockPolyhedronMatrix A₂ *ᵥ x) (finSumFinEquiv (Sum.inr j)) =
              (Araw *ᵥ x) (Sum.inr j) := by
          simpa [easyBlockPolyhedronMatrix, Araw] using
            congrFun hmul (finSumFinEquiv (Sum.inr j))
        have hRhs :
            easyBlockPolyhedronRhs (r := r) (n := n) b₂ (finSumFinEquiv (Sum.inr j)) = 0 := by
          simp [easyBlockPolyhedronRhs]
        rw [hEq, hRhs]
        have hneg : -x j ≤ 0 := neg_nonpos.mpr (hxNonneg j)
        simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec] using hneg
      exact hrow

/-- Helper for Proposition 8.8: the easy block equals its single-matrix polyhedral presentation.
-/
lemma easyBlockPolyhedron_eq
    {r n : ℕ}
    (A₂ : Matrix (Fin r) (Fin n) ℝ)
    (b₂ : Fin r → ℝ) :
    polyhedron_le_set (easyBlockPolyhedronMatrix A₂) (easyBlockPolyhedronRhs b₂) =
      easy_block_feasible_set A₂ b₂ := by
  ext x
  exact mem_easyBlockPolyhedron_iff A₂ b₂ x

/-- Helper for Proposition 8.8: the Lagrangian dual owner for a polyhedral base set
`polyhedron_le_set C d`. -/
noncomputable def polyhedralLagrangianDualValue
    {m₁ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ) : EReal :=
  sInf
    ((fun lam : Fin m₁ → ℝ ↦
        lagrangian_relaxation_value A₁ b₁ c (polyhedron_le_set C d) lam) ''
      Set.Ici (0 : Fin m₁ → ℝ))

/-- Helper for Proposition 8.8: `polyhedralLagrangianDualValue A₁ b₁ c C d` unfolds to the
infimum of the polyhedral Lagrangian-relaxation values over the nonnegative multipliers. -/
theorem polyhedralLagrangianDualValue_eq_sInf
    {m₁ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ) :
    polyhedralLagrangianDualValue A₁ b₁ c C d =
      sInf
        ((fun lam : Fin m₁ → ℝ ↦
            lagrangian_relaxation_value A₁ b₁ c (polyhedron_le_set C d) lam) ''
          Set.Ici (0 : Fin m₁ → ℝ)) :=
  rfl

/-- Helper for Proposition 8.8: the penalized objective over `A₁ x ≤ b₁` splits into the dualized
objective for `c - λ A₁` plus the constant term `λ b₁`. -/
lemma penalizedObjective_eq_dualizedObjective
    {m₁ n : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ)
    (x : Fin n → ℝ) :
    c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) =
      (c - lam ᵥ* A₁) ⬝ᵥ x + lam ⬝ᵥ b₁ := by
  calc
    c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x)
        = c ⬝ᵥ x + (lam ⬝ᵥ b₁ - lam ⬝ᵥ (A₁ *ᵥ x)) := by
            rw [dotProduct_sub]
    _ = c ⬝ᵥ x + (lam ⬝ᵥ b₁ - (lam ᵥ* A₁) ⬝ᵥ x) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (c - lam ᵥ* A₁) ⬝ᵥ x + lam ⬝ᵥ b₁ := by
          rw [sub_dotProduct]
          ring

/-- Helper for Proposition 8.8: on a polyhedral base set `polyhedron_le_set C d`, LP strong
duality identifies the Lagrangian dual with the corresponding linear-programming value whenever
the feasible region is nonempty. -/
lemma polyhedralLagrangianDualValue_eq_integerProgramValue
    {m₁ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ)
    (h_nonempty :
      Set.Nonempty (lagrangian_integer_feasible_set A₁ b₁ (polyhedron_le_set C d)) ∨
        Set.Nonempty
          (dual_feasible_region
            ((Matrix.fromRows A₁ C).submatrix finSumFinEquiv.symm (Equiv.refl _))
            c)) :
    polyhedralLagrangianDualValue A₁ b₁ c C d =
      integer_program_value A₁ b₁ c (polyhedron_le_set C d) := by
  let stackedA :
      Matrix (Fin (m₁ + p)) (Fin n) ℝ :=
    (Matrix.fromRows A₁ C).submatrix finSumFinEquiv.symm (Equiv.refl _)
  let stackedb : Fin (m₁ + p) → ℝ :=
    Sum.elim b₁ d ∘ finSumFinEquiv.symm
  have hRegion :
      lagrangian_integer_feasible_set A₁ b₁ (polyhedron_le_set C d) =
        primal_feasible_region stackedA stackedb := by
    ext x
    have hmul :=
      Matrix.submatrix_mulVec_equiv (Matrix.fromRows A₁ C) x finSumFinEquiv.symm (Equiv.refl _)
    rw [mem_lagrangian_integer_feasible_set_iff, mem_polyhedron_le_set_iff,
      mem_primal_feasible_region_iff]
    constructor
    · rintro ⟨hxC, hxA⟩ r
      rcases hsplit : finSumFinEquiv.symm r with i | j
      · have hr : r = finSumFinEquiv (Sum.inl i) := by
          simpa [hsplit] using (finSumFinEquiv.apply_symm_apply r).symm
        rw [hr]
        have hEq :
            (stackedA *ᵥ x) (finSumFinEquiv (Sum.inl i)) =
              (Matrix.fromRows A₁ C *ᵥ x) (Sum.inl i) := by
          simpa [stackedA] using congrFun hmul (finSumFinEquiv (Sum.inl i))
        have hRhs :
            stackedb (finSumFinEquiv (Sum.inl i)) = b₁ i := by
          simp [stackedb]
        rw [hEq, hRhs]
        simpa [Matrix.fromRows_mulVec] using hxA i
      · have hr : r = finSumFinEquiv (Sum.inr j) := by
          simpa [hsplit] using (finSumFinEquiv.apply_symm_apply r).symm
        rw [hr]
        have hEq :
            (stackedA *ᵥ x) (finSumFinEquiv (Sum.inr j)) =
              (Matrix.fromRows A₁ C *ᵥ x) (Sum.inr j) := by
          simpa [stackedA] using congrFun hmul (finSumFinEquiv (Sum.inr j))
        have hRhs :
            stackedb (finSumFinEquiv (Sum.inr j)) = d j := by
          simp [stackedb]
        rw [hEq, hRhs]
        simpa [Matrix.fromRows_mulVec] using hxC j
    · intro hx
      refine ⟨?_, ?_⟩
      · intro j
        have hrow := hx (finSumFinEquiv (Sum.inr j))
        have hEq :
            (stackedA *ᵥ x) (finSumFinEquiv (Sum.inr j)) =
              (Matrix.fromRows A₁ C *ᵥ x) (Sum.inr j) := by
          simpa [stackedA] using congrFun hmul (finSumFinEquiv (Sum.inr j))
        have hRhs :
            stackedb (finSumFinEquiv (Sum.inr j)) = d j := by
          simp [stackedb]
        rw [hEq, hRhs] at hrow
        simpa [Matrix.fromRows_mulVec] using hrow
      · intro i
        have hrow := hx (finSumFinEquiv (Sum.inl i))
        have hEq :
            (stackedA *ᵥ x) (finSumFinEquiv (Sum.inl i)) =
              (Matrix.fromRows A₁ C *ᵥ x) (Sum.inl i) := by
          simpa [stackedA] using congrFun hmul (finSumFinEquiv (Sum.inl i))
        have hRhs :
            stackedb (finSumFinEquiv (Sum.inl i)) = b₁ i := by
          simp [stackedb]
        rw [hEq, hRhs] at hrow
        simpa [Matrix.fromRows_mulVec] using hrow
  have hWeak :
      integer_program_value A₁ b₁ c (polyhedron_le_set C d) ≤
        polyhedralLagrangianDualValue A₁ b₁ c C d := by
    rw [integer_program_value_eq_sSup, polyhedralLagrangianDualValue_eq_sInf]
    refine le_sInf ?_
    rintro _ ⟨lam, hlam, rfl⟩
    exact integer_program_value_le_lagrangian_relaxation_value A₁ b₁ c
      (polyhedron_le_set C d) lam hlam
  have hDualUpper :
      polyhedralLagrangianDualValue A₁ b₁ c C d ≤
        sInf
          ((fun u : Fin (m₁ + p) → ℝ ↦ ((u ⬝ᵥ stackedb : ℝ) : EReal)) ''
            dual_feasible_region stackedA c) := by
    rw [polyhedralLagrangianDualValue_eq_sInf]
    refine le_sInf ?_
    rintro _ ⟨u, hu, rfl⟩
    let lam : Fin m₁ → ℝ := fun i ↦ u (Fin.castAdd p i)
    let mu : Fin p → ℝ := fun i ↦ u (Fin.natAdd m₁ i)
    have hlamNonneg : 0 ≤ lam := by
      intro i
      rcases (mem_dual_feasible_region_iff stackedA c u).mp hu with ⟨_, huNonneg⟩
      exact huNonneg (Fin.castAdd p i)
    have hmuNonneg : 0 ≤ mu := by
      intro i
      rcases (mem_dual_feasible_region_iff stackedA c u).mp hu with ⟨_, huNonneg⟩
      exact huNonneg (Fin.natAdd m₁ i)
    have hvecSplit :
        lam ᵥ* A₁ + mu ᵥ* C = c := by
      have hvec :=
        Matrix.submatrix_vecMul_equiv (Matrix.fromRows A₁ C) u finSumFinEquiv.symm (Equiv.refl _)
      have huSplit :
          (u ∘ finSumFinEquiv) ᵥ* Matrix.fromRows A₁ C = c := by
        rcases (mem_dual_feasible_region_iff stackedA c u).mp hu with ⟨huEq, _⟩
        ext j
        calc
          ((u ∘ finSumFinEquiv) ᵥ* Matrix.fromRows A₁ C) j = (u ᵥ* stackedA) j := by
              symm
              simpa [stackedA] using congrFun hvec j
          _ = c j := congrFun huEq j
      have hlamEq : ((u ∘ finSumFinEquiv) ∘ Sum.inl) = lam := by
        funext i
        rfl
      have hmuEq : ((u ∘ finSumFinEquiv) ∘ Sum.inr) = mu := by
        funext i
        rfl
      ext j
      simpa [Matrix.vecMul_fromRows, hlamEq, hmuEq] using congrFun huSplit j
    have hmuDual :
        mu ∈ dual_feasible_region C (c - lam ᵥ* A₁) := by
      rw [mem_dual_feasible_region_iff]
      refine ⟨?_, hmuNonneg⟩
      ext j
      have hj := congrFun hvecSplit j
      exact (eq_sub_iff_add_eq).2 <| by simpa [Pi.sub_apply, add_comm] using hj
    have hstackedObjective :
        u ⬝ᵥ stackedb = lam ⬝ᵥ b₁ + mu ⬝ᵥ d := by
      rw [dotProduct, dotProduct, dotProduct, Fin.sum_univ_add]
      simp [lam, mu, stackedb]
    have hRelaxLe :
        lagrangian_relaxation_value A₁ b₁ c (polyhedron_le_set C d) lam ≤
          ((u ⬝ᵥ stackedb : ℝ) : EReal) := by
      rw [lagrangian_relaxation_value_eq_sSup]
      refine sSup_le ?_
      rintro _ ⟨x, hxC, rfl⟩
      have hxPrimal : x ∈ primal_feasible_region C d := by
        exact (mem_primal_feasible_region_iff C d x).2 <|
          by simpa [polyhedron_le_set] using hxC
      have hweak :
          (c - lam ᵥ* A₁) ⬝ᵥ x ≤ mu ⬝ᵥ d :=
        weak_duality_feasible_pair C d (c - lam ᵥ* A₁) hxPrimal hmuDual
      have hpenalized :
          c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) ≤ lam ⬝ᵥ b₁ + mu ⬝ᵥ d := by
        rw [penalizedObjective_eq_dualizedObjective A₁ b₁ c lam x]
        linarith
      have hpenalizedE :
          ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) ≤
            ((lam ⬝ᵥ b₁ + mu ⬝ᵥ d : ℝ) : EReal) := by
        exact_mod_cast hpenalized
      simpa [hstackedObjective] using hpenalizedE
    have hLamInfs :
        polyhedralLagrangianDualValue A₁ b₁ c C d ≤
          lagrangian_relaxation_value A₁ b₁ c (polyhedron_le_set C d) lam := by
      rw [polyhedralLagrangianDualValue_eq_sInf]
      exact sInf_le ⟨lam, hlamNonneg, rfl⟩
    exact hLamInfs.trans hRelaxLe
  have hDuality :
      sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region stackedA stackedb) =
        sInf
          ((fun u : Fin (m₁ + p) → ℝ ↦ ((u ⬝ᵥ stackedb : ℝ) : EReal)) ''
            dual_feasible_region stackedA c) := by
    have hStackedNonempty :
        Set.Nonempty (primal_feasible_region stackedA stackedb) ∨
          Set.Nonempty (dual_feasible_region stackedA c) := by
      rcases h_nonempty with hprimal | hdual
      · left
        rw [← hRegion]
        exact hprimal
      · right
        simpa [stackedA] using hdual
    exact linear_program_duality_eq_except_both_empty stackedA stackedb c hStackedNonempty
  refine le_antisymm ?_ hWeak
  calc
    polyhedralLagrangianDualValue A₁ b₁ c C d ≤
        sInf
          ((fun u : Fin (m₁ + p) → ℝ ↦ ((u ⬝ᵥ stackedb : ℝ) : EReal)) ''
            dual_feasible_region stackedA c) := hDualUpper
    _ =
        sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region stackedA stackedb) := hDuality.symm
    _ = integer_program_value A₁ b₁ c (polyhedron_le_set C d) := by
        rw [integer_program_value_eq_sSup, ← hRegion]

/-- Helper for Proposition 8.8: the split-row Lagrangian dual over the continuous easy block. -/
noncomputable def facilityLocationSplitContinuousDualValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) : EReal :=
  sInf
    ((fun lam : Fin (m + m) → ℝ ↦
        lagrangian_relaxation_value
          (facilityLocationSplitAssignmentMatrixFin m n)
          (facilityLocationSplitAssignmentRhsFin m)
          ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
            (facilityLocationFlatVarEquiv m n).symm)
          (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
            (facilityLocationEasyBlockRhsFin m n))
          lam) ''
      Set.Ici (0 : Fin (m + m) → ℝ))

/-- Helper for Proposition 8.8: `facilityLocationSplitContinuousDualValue c f` unfolds to the
infimum of the split-row relaxation values over all nonnegative split multipliers. -/
theorem facilityLocationSplitContinuousDualValue_eq_sInf
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    facilityLocationSplitContinuousDualValue (m := m) (n := n) c f =
      sInf
        ((fun lam : Fin (m + m) → ℝ ↦
            lagrangian_relaxation_value
              (facilityLocationSplitAssignmentMatrixFin m n)
              (facilityLocationSplitAssignmentRhsFin m)
              ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
                (facilityLocationFlatVarEquiv m n).symm)
              (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
                (facilityLocationEasyBlockRhsFin m n))
              lam) ''
          Set.Ici (0 : Fin (m + m) → ℝ)) :=
  rfl

/-- Helper for Proposition 8.8: when `Fin n` is nonempty, the LP relaxation has a canonical
feasible point obtained by opening one facility and assigning every customer to it. -/
lemma uncapacitatedFacilityLocationLpFeasible_nonempty
    [Nonempty (Fin n)] :
    Set.Nonempty (uncapacitated_facility_location_lp_feasible_set (m := m) (n := n)) := by
  classical
  let j₀ : Fin n := Classical.choice ‹Nonempty (Fin n)›
  refine ⟨(fun _ j ↦ if j = j₀ then 1 else 0, fun j ↦ if j = j₀ then 1 else 0), ?_⟩
  rw [mem_uncapacitated_facility_location_lp_feasible_set_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · intro i j
    by_cases hj : j = j₀
    · simp [hj]
    · simp [hj]
  · intro i j
    by_cases hj : j = j₀
    · simp [hj]
    · simp [hj]
  · intro j
    by_cases hj : j = j₀
    · simp [hj]
    · simp [hj]
  · intro j
    by_cases hj : j = j₀
    · simp [hj]
    · simp [hj]

/-- Helper for Proposition 8.8: when `Fin n` is nonempty, the split-row continuous dual equals
the LP relaxation value by LP strong duality on the stacked polyhedral system. -/
lemma facilityLocationSplitContinuousDualValue_eq_lpValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    facilityLocationSplitContinuousDualValue (m := m) (n := n) c f =
      integer_program_value
        (facilityLocationSplitAssignmentMatrixFin m n)
        (facilityLocationSplitAssignmentRhsFin m)
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n)) := by
  have h_nonempty :
      Set.Nonempty
          (lagrangian_integer_feasible_set
            (facilityLocationSplitAssignmentMatrixFin m n)
            (facilityLocationSplitAssignmentRhsFin m)
            (polyhedron_le_set
              (easyBlockPolyhedronMatrix (facilityLocationEasyBlockMatrixFin m n))
              (easyBlockPolyhedronRhs (facilityLocationEasyBlockRhsFin m n)))) ∨
        Set.Nonempty
          (dual_feasible_region
            ((Matrix.fromRows
                (facilityLocationSplitAssignmentMatrixFin m n)
                (easyBlockPolyhedronMatrix (facilityLocationEasyBlockMatrixFin m n))).submatrix
              finSumFinEquiv.symm (Equiv.refl _))
            ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
              (facilityLocationFlatVarEquiv m n).symm)) := by
    by_cases hnonempty : Nonempty (Fin n)
    · letI : Nonempty (Fin n) := hnonempty
      left
      rcases uncapacitatedFacilityLocationLpFeasible_nonempty (m := m) (n := n) with ⟨xy, hxy⟩
      have hvComp :
          (facilityLocationFlatten (m := m) (n := n) xy ∘
              (facilityLocationFlatVarEquiv m n).symm) ∘
              facilityLocationFlatVarEquiv m n =
            facilityLocationFlatten (m := m) (n := n) xy := by
        funext z
        simp
      have hvUnflatten :
          facilityLocationUnflatten (m := m) (n := n)
              ((facilityLocationFlatten (m := m) (n := n) xy ∘
                  (facilityLocationFlatVarEquiv m n).symm) ∘
                facilityLocationFlatVarEquiv m n) = xy := by
        rw [hvComp, facilityLocationUnflatten_flatten]
      refine ⟨facilityLocationFlatten (m := m) (n := n) xy ∘
          (facilityLocationFlatVarEquiv m n).symm, ?_⟩
      rw [mem_lagrangian_integer_feasible_set_iff]
      refine ⟨?_, ?_⟩
      · rw [easyBlockPolyhedron_eq]
        refine (facilityLocationFinReindexLagrangianFeasible_iff
          (m := m) (n := n)
          (v := facilityLocationFlatten (m := m) (n := n) xy ∘
            (facilityLocationFlatVarEquiv m n).symm)).2 ?_
        rw [hvUnflatten]
        exact
          mem_uncapacitated_facility_location_lagrangian_feasible_set_of_mem_lp_feasible_set hxy
      · have hvLp :
            facilityLocationFlatten (m := m) (n := n) xy ∘
                (facilityLocationFlatVarEquiv m n).symm ∈
              lagrangian_integer_feasible_set
                (facilityLocationSplitAssignmentMatrixFin m n)
                (facilityLocationSplitAssignmentRhsFin m)
                (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
                  (facilityLocationEasyBlockRhsFin m n)) := by
          refine (facilityLocationFinReindexLpFeasible_iff
            (m := m) (n := n)
            (v := facilityLocationFlatten (m := m) (n := n) xy ∘
              (facilityLocationFlatVarEquiv m n).symm)).2 ?_
          rw [hvUnflatten]
          exact hxy
        exact hvLp.2
    · right
      have hn0 : n = 0 := by
        cases n with
        | zero =>
            rfl
        | succ n' =>
            exfalso
            exact hnonempty ⟨0⟩
      subst hn0
      refine ⟨0, ?_⟩
      rw [mem_dual_feasible_region_iff]
      refine ⟨?_, ?_⟩
      · ext j
        exact Fin.elim0 j
      · intro r
        simp
  rw [facilityLocationSplitContinuousDualValue_eq_sInf]
  rw [← easyBlockPolyhedron_eq (facilityLocationEasyBlockMatrixFin m n)
    (facilityLocationEasyBlockRhsFin m n)]
  simpa [polyhedralLagrangianDualValue] using
    polyhedralLagrangianDualValue_eq_integerProgramValue
      (A₁ := facilityLocationSplitAssignmentMatrixFin m n)
      (b₁ := facilityLocationSplitAssignmentRhsFin m)
      (c := ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
        (facilityLocationFlatVarEquiv m n).symm))
      (C := easyBlockPolyhedronMatrix (facilityLocationEasyBlockMatrixFin m n))
      (d := easyBlockPolyhedronRhs (facilityLocationEasyBlockRhsFin m n))
      h_nonempty

/-- Helper for Proposition 8.8: each reindexed split Lagrangian relaxation value over
`conv(pure_integer_points Q)` is exactly the current unrestricted facility-location relaxation
value at the difference multiplier `μ - ν`. -/
lemma splitFinLagrangianRelaxationValue_eq_uncapacitatedRelaxationValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ)
    (lam : Fin (m + m) → ℝ) :
    lagrangian_relaxation_value
        (facilityLocationSplitAssignmentMatrixFin m n)
        (facilityLocationSplitAssignmentRhsFin m)
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        (convexHull ℝ
          (pure_integer_points (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
            (facilityLocationEasyBlockRhsFin m n))))
        lam =
      ((uncapacitated_facility_location_lagrangian_relaxation_value c f
          (fun i ↦
            facilityLocationSplitMultiplierPos (m := m) lam i -
              facilityLocationSplitMultiplierNeg (m := m) lam i) : ℝ) : EReal) :=
by
  let lamDiff : Fin m → ℝ := fun i ↦
    facilityLocationSplitMultiplierPos (m := m) lam i -
      facilityLocationSplitMultiplierNeg (m := m) lam i
  let Q :
      Set (Fin (m * n + n) → ℝ) :=
    convexHull ℝ
      (pure_integer_points (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
        (facilityLocationEasyBlockRhsFin m n)))
  rw [lagrangian_relaxation_value_eq_sSup,
    uncapacitated_facility_location_lagrangian_relaxation_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨v, hvQ, rfl⟩
    have hvEasy :
        v ∈ easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n) := by
      refine convexHull_min ?_ facilityLocationEasyBlockFin_convex hvQ
      intro x hx
      exact (mem_pure_integer_points_iff.mp hx).1
    have hvLag :
        facilityLocationUnflatten (m := m) (n := n)
            (v ∘ facilityLocationFlatVarEquiv m n) ∈
          uncapacitated_facility_location_lagrangian_feasible_set :=
      (facilityLocationFinReindexLagrangianFeasible_iff (m := m) (n := n) (v := v)).1 hvEasy
    have hBdd :
        BddAbove
          ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
              facility_location_lagrangian_relaxation_value c f lamDiff xy.2 xy.1) ''
            uncapacitated_facility_location_lagrangian_feasible_set) := by
      refine ⟨(∑ j, max (facility_location_reduced_profit c f lamDiff j) 0) + ∑ i, lamDiff i, ?_⟩
      rintro _ ⟨xy, hxy, rfl⟩
      exact relaxationPointValue_le_closedForm (m := m) (n := n) c f lamDiff hxy
    have hcandidate :
        facility_location_lagrangian_relaxation_value c f lamDiff
            (facilityLocationUnflatten (m := m) (n := n)
              (v ∘ facilityLocationFlatVarEquiv m n)).2
            (facilityLocationUnflatten (m := m) (n := n)
              (v ∘ facilityLocationFlatVarEquiv m n)).1 ≤
          uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff := by
      rw [uncapacitated_facility_location_lagrangian_relaxation_value_eq_sSup]
      exact le_csSup hBdd ⟨_, hvLag, rfl⟩
    calc
      ((dotProduct
          ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
            (facilityLocationFlatVarEquiv m n).symm)
          v +
        dotProduct lam
          (facilityLocationSplitAssignmentRhsFin m -
            Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) : ℝ) : EReal) =
          ((facility_location_lagrangian_relaxation_value c f lamDiff
              (facilityLocationUnflatten (m := m) (n := n)
                (v ∘ facilityLocationFlatVarEquiv m n)).2
              (facilityLocationUnflatten (m := m) (n := n)
                (v ∘ facilityLocationFlatVarEquiv m n)).1 : ℝ) : EReal) := by
            exact
              congrArg
                (fun t : ℝ ↦ (t : EReal))
                (splitFinLagrangianObjective_eq_facilityLocationLagrangianObjective
                  (m := m) (n := n) c f lam v)
      _ ≤ ((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) :
            EReal) := by
            exact_mod_cast hcandidate
  · let v :
        Fin (m * n + n) → ℝ :=
      facilityLocationFlatten (m := m) (n := n)
          (lagrangian_relaxation_solution c f lamDiff) ∘
        (facilityLocationFlatVarEquiv m n).symm
    have hvPure :
        v ∈ pure_integer_points (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n)) := by
      simpa [lamDiff, v] using
        lagrangianSolution_flattenFin_mem_pureIntegerPoints (m := m) (n := n) c f lamDiff
    refine le_sSup ?_
    refine ⟨v, subset_convexHull ℝ _ hvPure, ?_⟩
    have hvComp :
        v ∘ facilityLocationFlatVarEquiv m n =
          facilityLocationFlatten (m := m) (n := n)
            (lagrangian_relaxation_solution c f lamDiff) := by
      funext z
      simp [v]
    have hvUnflatten :
        facilityLocationUnflatten (m := m) (n := n)
            (v ∘ facilityLocationFlatVarEquiv m n) =
          lagrangian_relaxation_solution c f lamDiff := by
      rw [hvComp, facilityLocationUnflatten_flatten]
    calc
      ((dotProduct
          ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
            (facilityLocationFlatVarEquiv m n).symm)
          v +
        dotProduct lam
          (facilityLocationSplitAssignmentRhsFin m -
            Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) : ℝ) : EReal) =
          ((facility_location_lagrangian_relaxation_value c f lamDiff
              (facilityLocationUnflatten (m := m) (n := n)
                (v ∘ facilityLocationFlatVarEquiv m n)).2
              (facilityLocationUnflatten (m := m) (n := n)
                (v ∘ facilityLocationFlatVarEquiv m n)).1 : ℝ) : EReal) := by
            exact
              congrArg
                (fun t : ℝ ↦ (t : EReal))
                (splitFinLagrangianObjective_eq_facilityLocationLagrangianObjective
                  (m := m) (n := n) c f lam v)
      _ =
          ((facility_location_lagrangian_relaxation_value c f lamDiff
              (lagrangian_relaxation_solution c f lamDiff).2
              (lagrangian_relaxation_solution c f lamDiff).1 : ℝ) : EReal) := by
            rw [hvUnflatten]
      _ =
          ((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) :
            EReal) := by
            exact
              congrArg
                (fun t : ℝ ↦ (t : EReal))
                (lagrangianSolution_attainsUncapacitatedRelaxationValue
                  (m := m) (n := n) c f lamDiff)

/-- Helper for Proposition 8.8: every LP-feasible point has objective value bounded above by the
relaxation value at `λ = 0`, so the current LP image set is bounded above in `WithBot ℝ`. -/
lemma facilityLocationLpImage_bddAbove
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    BddAbove
      ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
          ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
        uncapacitated_facility_location_lp_feasible_set) :=
by
  refine ⟨((uncapacitated_facility_location_lagrangian_relaxation_value c f 0 : ℝ) :
    WithBot ℝ), ?_⟩
  rintro _ ⟨xy, hxy, rfl⟩
  have hreal :
      uncapacitated_facility_location_objective c f xy ≤
        uncapacitated_facility_location_lagrangian_relaxation_value c f 0 := by
    -- On LP-feasible points the Lagrangian penalty vanishes, and the `λ = 0` relaxation value is
    -- exactly the closed-form upper bound from Proposition 8.8 (1).
    rw [← lagrangianObjective_eq_objective_of_memLpFeasibleSet (m := m) (n := n) c f 0 hxy]
    rw [uncapacitated_facility_location_lagrangian_relaxation_value_eq]
    exact
      relaxationPointValue_le_closedForm (m := m) (n := n) c f 0
        (mem_uncapacitated_facility_location_lagrangian_feasible_set_of_mem_lp_feasible_set hxy)
  exact
    (show ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ) ≤
        ((uncapacitated_facility_location_lagrangian_relaxation_value c f 0 : ℝ) : WithBot ℝ) by
      exact_mod_cast hreal)

/-- Helper for Proposition 8.8: the `WithBot`-to-`EReal` embedding preserves suprema of nonempty
bounded-above sets of finite values. -/
lemma withBotRealToEReal_csSup
    {S : Set (WithBot ℝ)}
    (hS : S.Nonempty)
    (hBdd : BddAbove S) :
    withBotRealToEReal (sSup S) = sSup (withBotRealToEReal '' S) :=
by
  let R : Set ℝ := {r | ((r : ℝ) : WithBot ℝ) ∈ S}
  by_cases hR : R.Nonempty
  · have hRbdd : BddAbove R := by
      rcases hBdd with ⟨u, hu⟩
      rcases hR with ⟨r, hr⟩
      have hur : ((r : ℝ) : WithBot ℝ) ≤ u := hu <| by simpa [R] using hr
      rcases eq_or_ne u ⊥ with rfl | hu_ne_bot
      · exact (WithBot.not_coe_le_bot r hur).elim
      · rcases WithBot.ne_bot_iff_exists.mp hu_ne_bot with ⟨u', rfl⟩
        refine ⟨u', ?_⟩
        intro r hr
        simpa [R] using hu hr
    let T : Set (WithBot ℝ) := ((↑) : ℝ → WithBot ℝ) '' R
    have hTne : T.Nonempty := by
      rcases hR with ⟨r, hr⟩
      exact ⟨(r : WithBot ℝ), ⟨r, hr, rfl⟩⟩
    have hTsub : T ⊆ S := by
      rintro _ ⟨r, hr, rfl⟩
      simpa [R] using hr
    have hTbdd : BddAbove T := by
      rcases hBdd with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      intro x hx
      exact hu (hTsub hx)
    have hSsub : S ⊆ insert (⊥ : WithBot ℝ) T := by
      intro x hx
      rcases eq_or_ne x ⊥ with rfl | hxbot
      · simp [T]
      · rcases WithBot.ne_bot_iff_exists.mp hxbot with ⟨r, rfl⟩
        right
        refine ⟨r, ?_, rfl⟩
        simpa [R] using hx
    have hTsSup : (sSup T : WithBot ℝ) = ((sSup R : ℝ) : WithBot ℝ) := by
      refine le_antisymm ?_ ?_
      · refine csSup_le hTne ?_
        rintro _ ⟨r, hr, rfl⟩
        exact_mod_cast le_csSup hRbdd hr
      · have hsSupT_ne_bot : (sSup T : WithBot ℝ) ≠ (⊥ : WithBot ℝ) := by
          rcases hR with ⟨r, hr⟩
          have hmem : ((r : ℝ) : WithBot ℝ) ∈ T := ⟨r, hr, rfl⟩
          have hle : ((r : ℝ) : WithBot ℝ) ≤ (sSup T : WithBot ℝ) := le_csSup hTbdd hmem
          exact fun hbot ↦ WithBot.not_coe_le_bot r (hbot ▸ hle)
        have hsup_le : sSup R ≤ (sSup T : WithBot ℝ).unbot hsSupT_ne_bot := by
          refine csSup_le hR ?_
          intro r hr
          have hmem : ((r : ℝ) : WithBot ℝ) ∈ T := ⟨r, hr, rfl⟩
          have hle : ((r : ℝ) : WithBot ℝ) ≤ (sSup T : WithBot ℝ) := le_csSup hTbdd hmem
          simpa using hle
        simpa using hsup_le
    have hSsSup : (sSup S : WithBot ℝ) = ((sSup R : ℝ) : WithBot ℝ) := by
      refine le_antisymm ?_ ?_
      · have hleST : (sSup S : WithBot ℝ) ≤ (sSup T : WithBot ℝ) := by
          refine csSup_le hS ?_
          intro x hx
          rcases eq_or_ne x ⊥ with rfl | hxbot
          · rcases hR with ⟨r, hr⟩
            exact bot_le.trans <| le_csSup hTbdd ⟨r, hr, rfl⟩
          · rcases WithBot.ne_bot_iff_exists.mp hxbot with ⟨r, rfl⟩
            have hrT : ((r : ℝ) : WithBot ℝ) ∈ T := ⟨r, by simpa [R] using hx, rfl⟩
            exact le_csSup hTbdd hrT
        calc
          (sSup S : WithBot ℝ) ≤ (sSup T : WithBot ℝ) := hleST
          _ = ((sSup R : ℝ) : WithBot ℝ) := hTsSup
      · calc
          ((sSup R : ℝ) : WithBot ℝ) = (sSup T : WithBot ℝ) := hTsSup.symm
          _ ≤ (sSup S : WithBot ℝ) := by
            refine csSup_le hTne ?_
            intro x hx
            exact le_csSup hBdd (hTsub hx)
    let U : Set EReal := ((↑) : ℝ → EReal) '' R
    have hUsub : U ⊆ withBotRealToEReal '' S := by
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨((r : ℝ) : WithBot ℝ), ?_, ?_⟩
      · simpa [R] using hr
      · simp
    have hImageSub : withBotRealToEReal '' S ⊆ insert (⊥ : EReal) U := by
      rintro _ ⟨x, hx, rfl⟩
      rcases eq_or_ne x ⊥ with rfl | hxbot
      · simp
      · rcases WithBot.ne_bot_iff_exists.mp hxbot with ⟨r, rfl⟩
        right
        refine ⟨r, ?_, by simp⟩
        simpa [R] using hx
    have hUsSup : sSup (withBotRealToEReal '' S) = ((sSup R : ℝ) : EReal) := by
      have hUsSup' : sSup U = ((sSup R : ℝ) : EReal) := by
        refine le_antisymm ?_ ?_
        · refine sSup_le ?_
          rintro _ ⟨r, hr, rfl⟩
          exact_mod_cast le_csSup hRbdd hr
        · have hUbdd : BddAbove U := by
            rcases hRbdd with ⟨u, hu⟩
            refine ⟨(u : EReal), ?_⟩
            rintro _ ⟨r, hr, rfl⟩
            exact_mod_cast hu hr
          have hsSupU_ne_bot : sSup U ≠ (⊥ : EReal) := by
            rcases hR with ⟨r, hr⟩
            have hmem : ((r : ℝ) : EReal) ∈ U := ⟨r, hr, rfl⟩
            have hle : ((r : ℝ) : EReal) ≤ sSup U := le_sSup hmem
            exact fun hbot ↦ (not_le_of_gt (EReal.bot_lt_coe r)) (hbot ▸ hle)
          have hsSupU_ne_top : sSup U ≠ (⊤ : EReal) := by
            rcases hRbdd with ⟨u, hu⟩
            have hsup_le : sSup U ≤ (u : EReal) := by
              refine sSup_le ?_
              rintro _ ⟨r, hr, rfl⟩
              exact_mod_cast hu hr
            exact fun htop ↦ (EReal.coe_lt_top u).not_ge (htop ▸ hsup_le)
          have hsup_le : sSup R ≤ (sSup U).toReal := by
            refine csSup_le hR ?_
            intro r hr
            have hmem : ((r : ℝ) : EReal) ∈ U := ⟨r, hr, rfl⟩
            have hle : ((r : ℝ) : EReal) ≤ sSup U := le_sSup hmem
            exact EReal.toReal_le_toReal hle (EReal.coe_ne_bot r) hsSupU_ne_top
          calc
            ((sSup R : ℝ) : EReal) ≤ (((sSup U).toReal : ℝ) : EReal) := by
              exact_mod_cast hsup_le
            _ ≤ sSup U := EReal.coe_toReal_le hsSupU_ne_bot
      refine le_antisymm ?_ ?_
      · calc
          sSup (withBotRealToEReal '' S) ≤ sSup U :=
            sSup_le_sSup_of_subset_insert_bot (α := EReal) hImageSub
          _ = ((sSup R : ℝ) : EReal) := hUsSup'
      · calc
          ((sSup R : ℝ) : EReal) = sSup U := hUsSup'.symm
          _ ≤ sSup (withBotRealToEReal '' S) := by
            refine sSup_le ?_
            intro x hx
            exact le_sSup (hUsub hx)
    rw [hSsSup, hUsSup]
    simp
  · have hbot : (⊥ : WithBot ℝ) ∈ S := by
      rcases hS with ⟨x, hx⟩
      rcases eq_or_ne x ⊥ with rfl | hxbot
      · simpa using hx
      · rcases WithBot.ne_bot_iff_exists.mp hxbot with ⟨r, rfl⟩
        exfalso
        apply hR
        exact ⟨r, by simpa [R] using hx⟩
    have hSeq : S = ({⊥} : Set (WithBot ℝ)) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        rcases eq_or_ne x ⊥ with rfl | hxbot
        · simp
        · rcases WithBot.ne_bot_iff_exists.mp hxbot with ⟨r, rfl⟩
          exfalso
          apply hR
          exact ⟨r, by simpa [R] using hx⟩
      · intro x hx
        simpa [Set.mem_singleton_iff.mp hx] using hbot
    have hImageEq : withBotRealToEReal '' S = ({(⊥ : EReal)} : Set EReal) := by
      rw [hSeq]
      ext z
      simp
    rw [hImageEq, hSeq]
    simp

/-- Helper for Proposition 8.8: the reindexed split LP value is exactly the current LP value after
embedding `WithBot ℝ` into `EReal`. -/
lemma splitFinLpValue_eq_uncapacitatedLpValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    integer_program_value
        (facilityLocationSplitAssignmentMatrixFin m n)
        (facilityLocationSplitAssignmentRhsFin m)
        ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
          (facilityLocationFlatVarEquiv m n).symm)
        (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n)) =
      withBotRealToEReal (uncapacitated_facility_location_lp_value c f) :=
by
  let SW : Set (WithBot ℝ) :=
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ)) ''
      uncapacitated_facility_location_lp_feasible_set)
  let SE : Set EReal :=
    ((fun xy : (Fin m → Fin n → ℝ) × (Fin n → ℝ) ↦
        ((uncapacitated_facility_location_objective c f xy : ℝ) : EReal)) ''
      uncapacitated_facility_location_lp_feasible_set)
  rw [integer_program_value_eq_sSup, uncapacitated_facility_location_lp_value_eq_sSup]
  have hImage :
      ((fun v : Fin (m * n + n) → ℝ ↦
          ((dotProduct
              ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
                (facilityLocationFlatVarEquiv m n).symm)
              v : ℝ) : EReal)) ''
        lagrangian_integer_feasible_set
          (facilityLocationSplitAssignmentMatrixFin m n)
          (facilityLocationSplitAssignmentRhsFin m)
          (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
            (facilityLocationEasyBlockRhsFin m n))) =
        withBotRealToEReal '' SW := by
    calc
      ((fun v : Fin (m * n + n) → ℝ ↦
          ((dotProduct
              ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
                (facilityLocationFlatVarEquiv m n).symm)
              v : ℝ) : EReal)) ''
        lagrangian_integer_feasible_set
          (facilityLocationSplitAssignmentMatrixFin m n)
          (facilityLocationSplitAssignmentRhsFin m)
          (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
            (facilityLocationEasyBlockRhsFin m n))) =
          SE := facilityLocationFinLpObjectiveImage_eq (m := m) (n := n) c f
      _ = withBotRealToEReal '' SW := by
          ext z
          constructor
          · rintro ⟨xy, hxy, rfl⟩
            refine ⟨((uncapacitated_facility_location_objective c f xy : ℝ) : WithBot ℝ), ?_, ?_⟩
            · exact ⟨xy, hxy, rfl⟩
            · simp
          · rintro ⟨w, hw, rfl⟩
            rcases hw with ⟨xy, hxy, rfl⟩
            exact ⟨xy, hxy, by simp⟩
  rw [hImage]
  by_cases hSW : SW.Nonempty
  · exact (withBotRealToEReal_csSup (S := SW) hSW
      (facilityLocationLpImage_bddAbove (m := m) (n := n) c f)).symm
  · have hEmpty : SW = ∅ := Set.not_nonempty_iff_eq_empty.mp hSW
    simp [SW, hEmpty]

/-- Helper for Proposition 8.8: once the split-row Chapter 8.1 model is transported from the
sum-type ambient space to an explicit `Fin (m * n + n)` ambient space, LP strong duality on the
continuous easy block yields the missing inequality `z_LD ≤ z_LP`. -/
lemma uncapacitatedFacilityLocation_lagrangianDualValue_le_lpValue
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_lagrangian_dual_value c f ≤
      uncapacitated_facility_location_lp_value c f :=
by
  apply withBotRealToEReal.le_iff_le.mp
  let A₁ := facilityLocationSplitAssignmentMatrixFin m n
  let b₁ := facilityLocationSplitAssignmentRhsFin m
  let c₁ := ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
    (facilityLocationFlatVarEquiv m n).symm)
  have hDualLe :
      withBotRealToEReal (uncapacitated_facility_location_lagrangian_dual_value c f) ≤
        facilityLocationSplitContinuousDualValue (m := m) (n := n) c f := by
    rw [facilityLocationSplitContinuousDualValue_eq_sInf]
    refine le_sInf ?_
    rintro _ ⟨lam, hlam, rfl⟩
    let lamDiff : Fin m → ℝ := fun i ↦
      facilityLocationSplitMultiplierPos (m := m) lam i -
        facilityLocationSplitMultiplierNeg (m := m) lam i
    let v :
        Fin (m * n + n) → ℝ :=
      facilityLocationFlatten (m := m) (n := n)
          (lagrangian_relaxation_solution c f lamDiff) ∘
        (facilityLocationFlatVarEquiv m n).symm
    have hCurrent :
        uncapacitated_facility_location_lagrangian_dual_value c f ≤
          (((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) :
            WithBot ℝ)) := by
      rw [uncapacitated_facility_location_lagrangian_dual_value_eq_sInf]
      have hmem :
          (((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) :
            WithBot ℝ)) ∈
            Set.range (fun lam : Fin m → ℝ ↦
              ((uncapacitated_facility_location_lagrangian_relaxation_value c f lam : ℝ) :
                WithBot ℝ)) := ⟨lamDiff, rfl⟩
      exact csInf_le (OrderBot.bddBelow _) hmem
    have hAttain :
        ((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) : EReal) ≤
          lagrangian_relaxation_value A₁ b₁ c₁
            (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
              (facilityLocationEasyBlockRhsFin m n))
            lam := by
      rw [lagrangian_relaxation_value_eq_sSup]
      refine le_sSup ?_
      refine ⟨v, ?_, ?_⟩
      · exact (mem_pure_integer_points_iff.mp
          (lagrangianSolution_flattenFin_mem_pureIntegerPoints
            (m := m) (n := n) c f lamDiff)).1
      · have hvComp :
            v ∘ facilityLocationFlatVarEquiv m n =
              facilityLocationFlatten (m := m) (n := n)
                (lagrangian_relaxation_solution c f lamDiff) := by
          funext z
          simp [v]
        have hvUnflatten :
            facilityLocationUnflatten (m := m) (n := n)
                (v ∘ facilityLocationFlatVarEquiv m n) =
              lagrangian_relaxation_solution c f lamDiff := by
          rw [hvComp, facilityLocationUnflatten_flatten]
        calc
          ((dotProduct
              ((facilityLocationFlatObjective (m := m) (n := n) c f) ∘
                (facilityLocationFlatVarEquiv m n).symm)
              v +
            dotProduct lam
              (facilityLocationSplitAssignmentRhsFin m -
                Matrix.mulVec (facilityLocationSplitAssignmentMatrixFin m n) v) : ℝ) : EReal) =
              ((facility_location_lagrangian_relaxation_value c f lamDiff
                  (facilityLocationUnflatten (m := m) (n := n)
                    (v ∘ facilityLocationFlatVarEquiv m n)).2
                  (facilityLocationUnflatten (m := m) (n := n)
                    (v ∘ facilityLocationFlatVarEquiv m n)).1 : ℝ) : EReal) := by
                exact
                  congrArg
                    (fun t : ℝ ↦ (t : EReal))
                    (splitFinLagrangianObjective_eq_facilityLocationLagrangianObjective
                      (m := m) (n := n) c f lam v)
          _ =
              ((facility_location_lagrangian_relaxation_value c f lamDiff
                  (lagrangian_relaxation_solution c f lamDiff).2
                  (lagrangian_relaxation_solution c f lamDiff).1 : ℝ) : EReal) := by
                rw [hvUnflatten]
          _ =
              ((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) :
                EReal) := by
                exact
                  congrArg
                    (fun t : ℝ ↦ (t : EReal))
                    (lagrangianSolution_attainsUncapacitatedRelaxationValue
                      (m := m) (n := n) c f lamDiff)
    calc
      withBotRealToEReal (uncapacitated_facility_location_lagrangian_dual_value c f) ≤
          ((uncapacitated_facility_location_lagrangian_relaxation_value c f lamDiff : ℝ) :
            EReal) := by
            simpa [lamDiff] using withBotRealToEReal.monotone hCurrent
      _ ≤ lagrangian_relaxation_value A₁ b₁ c₁
            (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
              (facilityLocationEasyBlockRhsFin m n))
            lam := hAttain
  calc
    withBotRealToEReal (uncapacitated_facility_location_lagrangian_dual_value c f) ≤
        facilityLocationSplitContinuousDualValue (m := m) (n := n) c f := hDualLe
    _ = integer_program_value A₁ b₁ c₁
        (easy_block_feasible_set (facilityLocationEasyBlockMatrixFin m n)
          (facilityLocationEasyBlockRhsFin m n)) := by
          simpa [A₁, b₁, c₁] using
            facilityLocationSplitContinuousDualValue_eq_lpValue (m := m) (n := n) c f
    _ = withBotRealToEReal (uncapacitated_facility_location_lp_value c f) := by
      simpa [A₁, b₁, c₁] using
        splitFinLpValue_eq_uncapacitatedLpValue (m := m) (n := n) c f

/-- Proposition 8.8 (2). The Lagrangian dual value equals the linear-programming relaxation value:
`z_LD = z_LP`. -/
theorem uncapacitated_facility_location_lagrangian_dual_value_eq_lp_value
    (c : Fin m → Fin n → ℝ)
    (f : Fin n → ℝ) :
    uncapacitated_facility_location_lagrangian_dual_value c f =
      uncapacitated_facility_location_lp_value c f := by
  -- Route correction: the source of the remaining gap is now isolated in the reverse inequality
  -- `z_LD ≤ z_LP`; the weak-duality half was already proved directly above.
  exact le_antisymm
    (uncapacitatedFacilityLocation_lagrangianDualValue_le_lpValue c f)
    (uncapacitatedFacilityLocation_lpValue_le_lagrangianDualValue c f)

end Proposition88
