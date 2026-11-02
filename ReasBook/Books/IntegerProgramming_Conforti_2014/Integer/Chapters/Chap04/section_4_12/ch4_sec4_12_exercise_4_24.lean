import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_definition_4_6_extra_1

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: integral and totally dual integral matrix systems from Chapter 4
-- * sampled owner declarations: Chapter 4.1 `rational_matrix_polyhedron` and `is_integral`,
--   together with Chapter 4.6 `totally_dual_integral`
-- * owner abstraction: the source-facing covering system of Exercise 4.24 is best expressed as a
--   concrete polyhedron, with a thin bridge to the canonical Chapter 4 `≤`-system owner
-- * source/core/bridge triage: `exercise_4_24_polyhedron` is source-facing, `is_integral` and
--   `totally_dual_integral` are core/canonical owners, and the stacked `constraint_matrix` /
--   `constraint_rhs` pair is the bridge/view into that owner
-- * primitive data: the displayed integral matrix and right-hand side vector
-- * derived API: the rational `≤`-presentation of the same polyhedron and the Chapter 4
--   integrality/TDI predicates on that presentation

/-- The `4 × 6` matrix displayed in Exercise 4.24. -/
def exercise_4_24_matrix : Matrix (Fin 4) (Fin 6) ℤ :=
  !![(1 : ℤ), 1, 0, 1, 0, 0;
    1, 0, 1, 0, 1, 0;
    0, 1, 1, 0, 0, 1;
    0, 0, 0, 1, 1, 1]

/-- The right-hand side vector `1` for the system in Exercise 4.24. -/
def exercise_4_24_rhs : Fin 4 → ℤ :=
  ![(1 : ℤ), 1, 1, 1]

/-- The canonical `≤`-system matrix encoding the covering constraints `A x ≥ 1` and the
nonnegativity constraints `x ≥ 0`. -/
def exercise_4_24_constraint_matrix : Matrix (Fin (4 + 6)) (Fin 6) ℚ :=
  !![(-1 : ℚ), -1, 0, -1, 0, 0;
    -1, 0, -1, 0, -1, 0;
    0, -1, -1, 0, 0, -1;
    0, 0, 0, -1, -1, -1;
    -1, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, -1]

/-- The canonical `≤`-system right-hand side encoding `A x ≥ 1` and `x ≥ 0`. -/
def exercise_4_24_constraint_rhs : Fin (4 + 6) → ℚ :=
  ![(-1 : ℚ), -1, -1, -1, 0, 0, 0, 0, 0, 0]

/-- The polyhedron `P = {x ≥ 0 : A x ≥ 1}` from Exercise 4.24. -/
def exercise_4_24_polyhedron : Set (Fin 6 → ℝ) :=
  {x |
    (exercise_4_24_matrix.map (Int.castRingHom ℝ)) *ᵥ x ≥ (Int.cast ∘ exercise_4_24_rhs) ∧
      0 ≤ x}

/-- Membership in `exercise_4_24_polyhedron` is exactly the covering system `x ≥ 0`, `A x ≥ 1`.
-/
theorem mem_exercise_4_24_polyhedron_iff
    (x : Fin 6 → ℝ) :
    x ∈ exercise_4_24_polyhedron ↔
      (exercise_4_24_matrix.map (Int.castRingHom ℝ)) *ᵥ x ≥ (Int.cast ∘ exercise_4_24_rhs) ∧
        0 ≤ x :=
  Iff.rfl

/-- Helper for Exercise 4.24: explicit expansion of a `Fin 9` sum. -/
private lemma exercise_4_24_sum_univ_nine
    {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_eight, add_assoc]

/-- Helper for Exercise 4.24: explicit expansion of a `Fin 10` sum. -/
private lemma exercise_4_24_sum_univ_ten
    {M : Type*} [AddCommMonoid M] (f : Fin 10 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_succ]
  simp [exercise_4_24_sum_univ_nine, add_assoc]

/-- Helper for Exercise 4.24: the displayed `4 × 6` covering matrix evaluates on a vector `x` to
the four explicit covering left-hand sides. -/
lemma exercise_4_24_matrix_mulVec
    (x : Fin 6 → ℝ) :
    (exercise_4_24_matrix.map (Int.castRingHom ℝ)) *ᵥ x =
      ![x 0 + x 1 + x 3, x 0 + x 2 + x 4, x 1 + x 2 + x 5, x 3 + x 4 + x 5] := by
  ext i
  fin_cases i
  · simpa [exercise_4_24_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 4.24: the stacked `≤`-system matrix evaluates on a vector `x` to the ten
explicit covering and nonnegativity left-hand sides. -/
lemma exercise_4_24_constraint_mulVec
    (x : Fin 6 → ℝ) :
    (exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ x =
      ![-(x 0 + x 1 + x 3), -(x 0 + x 2 + x 4), -(x 1 + x 2 + x 5), -(x 3 + x 4 + x 5),
        -x 0, -x 1, -x 2, -x 3, -x 4, -x 5] := by
  -- Evaluate the fixed `10 × 6` matrix row by row once, so later proofs can rewrite cleanly.
  ext i
  fin_cases i
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
      add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 4.24: the dual row vector `y` applied to the stacked constraint matrix
produces the six explicit column equations used in the dual system. -/
lemma exercise_4_24_vecMul_constraint
    (y : Fin 10 → ℝ) :
    y ᵥ* (exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) =
      ![-(y 0 + y 1 + y 4), -(y 0 + y 2 + y 5), -(y 1 + y 2 + y 6), -(y 0 + y 3 + y 7),
        -(y 1 + y 3 + y 8), -(y 2 + y 3 + y 9)] := by
  -- The fixed column formulas are proved once by extensionality over `Fin 6`.
  ext j
  fin_cases j
  · simpa [exercise_4_24_constraint_matrix, Matrix.vecMul, dotProduct, exercise_4_24_sum_univ_ten,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.vecMul, dotProduct, exercise_4_24_sum_univ_ten,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.vecMul, dotProduct, exercise_4_24_sum_univ_ten,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.vecMul, dotProduct, exercise_4_24_sum_univ_ten,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.vecMul, dotProduct, exercise_4_24_sum_univ_ten,
      add_assoc, add_left_comm, add_comm]
  · simpa [exercise_4_24_constraint_matrix, Matrix.vecMul, dotProduct, exercise_4_24_sum_univ_ten,
      add_assoc, add_left_comm, add_comm]

/-- Helper for Exercise 4.24: the dual objective against the stacked right-hand side is exactly
the negative sum of the four covering variables. -/
lemma exercise_4_24_rhs_dot
    (y : Fin 10 → ℝ) :
    y ⬝ᵥ (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ)) = -(y 0 + y 1 + y 2 + y 3) := by
  -- Only the first four right-hand-side coordinates are nonzero.
  simpa [dotProduct, exercise_4_24_constraint_rhs, exercise_4_24_sum_univ_ten,
    add_assoc, add_left_comm, add_comm]

/-- Bridge/view: the source-facing covering polyhedron is the canonical rational `≤`-system
presentation obtained by stacking `-A` with `-I`. -/
theorem exercise_4_24_polyhedron_eq_rational_matrix_polyhedron :
    exercise_4_24_polyhedron =
      rational_matrix_polyhedron exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
  -- Rewrite the stacked system once into the ten scalar inequalities from the source statement.
  ext x
  constructor
  · intro hx
    rw [mem_exercise_4_24_polyhedron_iff] at hx
    rw [mem_rational_matrix_polyhedron, exercise_4_24_constraint_mulVec]
    rw [exercise_4_24_matrix_mulVec] at hx
    rcases hx with ⟨hcover, hnonneg⟩
    intro i
    fin_cases i
    · simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using neg_le_neg (hcover 0)
    · simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using neg_le_neg (hcover 1)
    · simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using neg_le_neg (hcover 2)
    · simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using neg_le_neg (hcover 3)
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr (hnonneg 0)
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr (hnonneg 1)
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr (hnonneg 2)
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr (hnonneg 3)
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr (hnonneg 4)
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr (hnonneg 5)
  · intro hx
    rw [mem_exercise_4_24_polyhedron_iff]
    rw [exercise_4_24_matrix_mulVec]
    rw [mem_rational_matrix_polyhedron, exercise_4_24_constraint_mulVec] at hx
    constructor
    · intro i
      fin_cases i
      · have h := neg_le_neg (hx 0)
        simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 1)
        simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 2)
        simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 3)
        simpa [exercise_4_24_rhs, exercise_4_24_constraint_rhs] using h
    · intro j
      fin_cases j
      · have h := neg_le_neg (hx 4)
        simpa [exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 5)
        simpa [exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 6)
        simpa [exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 7)
        simpa [exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 8)
        simpa [exercise_4_24_constraint_rhs] using h
      · have h := neg_le_neg (hx 9)
        simpa [exercise_4_24_constraint_rhs] using h

/-- Helper for Exercise 4.24: the covering polyhedron is the nonnegative matrix polyhedron for
the negated covering system `-A x ≤ -1`. -/
theorem exercise_4_24_polyhedron_eq_nonnegative_matrix_polyhedron :
    exercise_4_24_polyhedron =
      nonnegative_matrix_polyhedron (-exercise_4_24_matrix) (-exercise_4_24_rhs) := by
  -- Negating the covering rows turns `A x ≥ 1` into the standard `≤`-presentation.
  ext x
  rw [mem_exercise_4_24_polyhedron_iff]
  constructor
  · rintro ⟨hcover, hnonneg⟩
    refine ⟨?_, hnonneg⟩
    intro i
    fin_cases i
    · simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using
        neg_le_neg (hcover 0)
    · simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using
        neg_le_neg (hcover 1)
    · simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using
        neg_le_neg (hcover 2)
    · simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using
        neg_le_neg (hcover 3)
  · rintro ⟨hcover, hnonneg⟩
    refine ⟨?_, hnonneg⟩
    intro i
    fin_cases i
    · have h := neg_le_neg (hcover 0)
      simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using h
    · have h := neg_le_neg (hcover 1)
      simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using h
    · have h := neg_le_neg (hcover 2)
      simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using h
    · have h := neg_le_neg (hcover 3)
      simpa [nonnegative_matrix_polyhedron, exercise_4_24_matrix, exercise_4_24_rhs,
        Matrix.mulVec, dotProduct, Fin.sum_univ_six, add_assoc, add_left_comm, add_comm] using h

/-- Helper for Exercise 4.24: the integral objective vector `c = -𝟙` used to witness the failure
of total dual integrality. -/
def exercise_4_24_negOnesObjective : Fin 6 → ℤ :=
  fun _ ↦ -1

/-- Helper for Exercise 4.24: every feasible primal point has objective value at most `-2` for the
objective `c = -𝟙`. The proof is the textbook sum of the four covering inequalities. -/
lemma exercise_4_24_primal_objective_le_negTwo
    {x : Fin 6 → ℝ}
    (hx : x ∈ rational_matrix_polyhedron
      exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs) :
    ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ x) ≤ -2 := by
  -- Route correction: after normalizing the stacked rows once, the source proof is just one
  -- scalar `linarith` computation on the four covering inequalities.
  rw [mem_rational_matrix_polyhedron, exercise_4_24_constraint_mulVec] at hx
  have h0 : 1 ≤ x 0 + x 1 + x 3 := by
    simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 0)
  have h1 : 1 ≤ x 0 + x 2 + x 4 := by
    simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 1)
  have h2 : 1 ≤ x 1 + x 2 + x 5 := by
    simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 2)
  have h3 : 1 ≤ x 3 + x 4 + x 5 := by
    simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 3)
  have hsum : 2 ≤ x 0 + x 1 + x 2 + x 3 + x 4 + x 5 := by
    linarith
  -- Normalize the objective to the negative total edge weight and finish with the summed bound.
  have hobj :
      ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ x) =
        -(x 0 + x 1 + x 2 + x 3 + x 4 + x 5) := by
    simp [exercise_4_24_negOnesObjective, dotProduct, Fin.sum_univ_six,
      add_assoc, add_comm]
  rw [hobj]
  linarith

/-- Helper for Exercise 4.24: dual feasibility for the objective `c = -𝟙` is exactly the
`K₄`-stable-set system `u_i + u_j + z_e = 1` together with coordinatewise nonnegativity. -/
lemma mem_exercise_4_24_dual_feasible_region_negOnes_iff
    {y : Fin 10 → ℝ} :
    y ∈ rational_dual_feasible_region
      exercise_4_24_constraint_matrix exercise_4_24_negOnesObjective ↔
      0 ≤ y ∧
        y 0 + y 1 + y 4 = 1 ∧
        y 0 + y 2 + y 5 = 1 ∧
        y 1 + y 2 + y 6 = 1 ∧
        y 0 + y 3 + y 7 = 1 ∧
        y 1 + y 3 + y 8 = 1 ∧
        y 2 + y 3 + y 9 = 1 := by
  -- Rewrite the six dual column equations into the scalar system from the textbook statement.
  rw [mem_rational_dual_feasible_region_iff, exercise_4_24_vecMul_constraint]
  constructor
  · rintro ⟨hyEq, hyNonneg⟩
    have h0 : y 0 + y 1 + y 4 = 1 := by
      have h := congrArg (fun v ↦ v 0) hyEq
      simpa [exercise_4_24_negOnesObjective] using neg_eq_iff_eq_neg.mp h
    have h1 : y 0 + y 2 + y 5 = 1 := by
      have h := congrArg (fun v ↦ v 1) hyEq
      simpa [exercise_4_24_negOnesObjective] using neg_eq_iff_eq_neg.mp h
    have h2 : y 1 + y 2 + y 6 = 1 := by
      have h := congrArg (fun v ↦ v 2) hyEq
      simpa [exercise_4_24_negOnesObjective] using neg_eq_iff_eq_neg.mp h
    have h3 : y 0 + y 3 + y 7 = 1 := by
      have h := congrArg (fun v ↦ v 3) hyEq
      simpa [exercise_4_24_negOnesObjective] using neg_eq_iff_eq_neg.mp h
    have h4 : y 1 + y 3 + y 8 = 1 := by
      have h := congrArg (fun v ↦ v 4) hyEq
      simpa [exercise_4_24_negOnesObjective] using neg_eq_iff_eq_neg.mp h
    have h5 : y 2 + y 3 + y 9 = 1 := by
      have h := congrArg (fun v ↦ v 5) hyEq
      simpa [exercise_4_24_negOnesObjective] using neg_eq_iff_eq_neg.mp h
    exact ⟨hyNonneg, h0, h1, h2, h3, h4, h5⟩
  · rintro ⟨hyNonneg, h0, h1, h2, h3, h4, h5⟩
    refine ⟨?_, hyNonneg⟩
    ext j
    fin_cases j
    · have : -(y 0 + y 1 + y 4) = (-1 : ℝ) := by linarith
      simpa [exercise_4_24_negOnesObjective] using this
    · have : -(y 0 + y 2 + y 5) = (-1 : ℝ) := by linarith
      simpa [exercise_4_24_negOnesObjective] using this
    · have : -(y 1 + y 2 + y 6) = (-1 : ℝ) := by linarith
      simpa [exercise_4_24_negOnesObjective] using this
    · have : -(y 0 + y 3 + y 7) = (-1 : ℝ) := by linarith
      simpa [exercise_4_24_negOnesObjective] using this
    · have : -(y 1 + y 3 + y 8) = (-1 : ℝ) := by linarith
      simpa [exercise_4_24_negOnesObjective] using this
    · have : -(y 2 + y 3 + y 9) = (-1 : ℝ) := by linarith
      simpa [exercise_4_24_negOnesObjective] using this

/-- Helper for Exercise 4.24: any lineality direction inside a subset of the covering polyhedron
must vanish because a sufficiently negative translate breaks one nonnegativity coordinate. -/
lemma eq_zero_of_mem_linealitySpace_of_subset_exercise_4_24_polyhedron
    {F : Set (Fin 6 → ℝ)} (hF_subset : F ⊆ exercise_4_24_polyhedron)
    {r x : Fin 6 → ℝ}
    (hr : r ∈ linealitySpace F)
    (hx : x ∈ F) :
    r = 0 := by
  -- Reuse the Exercise 4.11 contradiction pattern with the nonnegativity half of this polyhedron.
  rw [mem_linealitySpace_iff] at hr
  ext j
  by_contra hne
  let a : ℝ := (-x j - 1) / r j
  have hxaF : x + a • r ∈ F := hr hx a
  have hxa_nonneg : 0 ≤ x j + a * r j := by
    have hxaP : x + a • r ∈ exercise_4_24_polyhedron := hF_subset hxaF
    have hcoord := (Iff.mp (mem_exercise_4_24_polyhedron_iff (x + a • r)) hxaP).2 j
    simpa [a, Pi.add_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hcoord
  have hrj : r j ≠ 0 := by
    simpa using hne
  have hcalc : x j + a * r j = -1 := by
    dsimp [a]
    field_simp [hrj]
    ring
  linarith [hxa_nonneg]

/-- Helper for Exercise 4.24: an extreme point of `polyhedron_le_set A b` admits `n` active rows
whose coefficient vectors are linearly independent. -/
lemma exists_active_linearlyIndependent_rows_of_extremePoint_polyhedron
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbar_vertex : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
    ∃ I : Fin n ↪ Fin m,
      (∀ i : Fin n, (A *ᵥ xbar) (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : Fin n ↦ A (I i)) := by
  classical
  let activeRows : Set (Fin n → ℝ) :=
    Set.range fun i : {i // (A *ᵥ xbar) i = b i} ↦ A i.1
  have hspan : Submodule.span ℝ activeRows = ⊤ := by
    by_contra hspan_ne
    let K : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ activeRows
    have hKlt : K < ⊤ := lt_of_le_of_ne le_top hspan_ne
    obtain ⟨φ, hφ_ne, hKker⟩ := Submodule.exists_le_ker_of_lt_top K hKlt
    let r : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm φ
    have hr_ne : r ≠ 0 := by
      intro hr
      apply hφ_ne
      simpa [r, hr] using ((dotProductEquiv ℝ (Fin n)).apply_symm_apply φ).symm
    have hactive_eval : ∀ i : Fin m, (A *ᵥ xbar) i = b i → (A *ᵥ r) i = 0 := by
      intro i hi
      have hAi_mem : A i ∈ K := by
        refine Submodule.subset_span ?_
        exact ⟨⟨i, hi⟩, rfl⟩
      have hφAi : φ (A i) = 0 := by
        simpa using hKker hAi_mem
      have hφr : (dotProductEquiv ℝ (Fin n)) r = φ := by
        simp [r]
      have hdot : dotProduct r (A i) = 0 := by
        simpa [hφAi] using congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) ↦ f (A i)) hφr
      have hrowdot : dotProduct (A i) r = 0 := by
        simpa [dotProduct_comm] using hdot
      simpa [Matrix.mulVec, dotProduct] using hrowdot
    let δ : Fin m → ℝ := fun i ↦
      if hi : (A *ᵥ xbar) i = b i then 1
      else if hzero : (A *ᵥ r) i = 0 then 1
      else (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|
    have hδ_pos : ∀ i : Fin m, 0 < δ i := by
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · simp [δ, hi]
      · by_cases hzero : (A *ᵥ r) i = 0
        · simp [δ, hi, hzero]
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hnum : 0 < b i - (A *ᵥ xbar) i := sub_pos.mpr hlt
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          simp [δ, hi, hzero, div_pos hnum hden]
    let δs : Finset ℝ := insert 1 (Finset.univ.image δ)
    let ε : ℝ := δs.min' (by simp [δs]) / 2
    have hmin_pos : 0 < δs.min' (by simp [δs]) := by
      have hmin_mem : δs.min' (by simp [δs]) ∈ δs := Finset.min'_mem _ _
      rcases Finset.mem_insert.mp hmin_mem with h1 | himage
      · simpa [h1]
      · rcases Finset.mem_image.mp himage with ⟨i, _, hi⟩
        rw [← hi]
        exact hδ_pos i
    have hε_pos : 0 < ε := half_pos hmin_pos
    have hε_le : ∀ i : Fin m, ε ≤ δ i := by
      intro i
      have hmin_le : δs.min' (by simp [δs]) ≤ δ i := by
        apply Finset.min'_le
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      have hhalf_le : δs.min' (by simp [δs]) / 2 ≤ δs.min' (by simp [δs]) := by
        linarith
      exact hhalf_le.trans hmin_le
    have hperturb_eval (σ : ℝ) (i : Fin m) :
        (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp
    have hperturb_mem : ∀ {σ : ℝ}, |σ| ≤ ε → xbar + σ • r ∈ polyhedron_le_set A b := by
      intro σ hσ
      rw [mem_polyhedron_le_set_iff]
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · calc
          (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
          _ = b i := by simp [hi, hactive_eval i hi]
          _ ≤ b i := le_rfl
      · by_cases hzero : (A *ᵥ r) i = 0
        · calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ = (A *ᵥ xbar) i := by simp [hzero]
            _ ≤ b i := hxbar i
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hσ_bound : |σ| ≤ (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by
            calc
              |σ| ≤ ε := hσ
              _ ≤ δ i := hε_le i
              _ = (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by simp [δ, hi, hzero]
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          have hmul_le :
              |σ| * |(A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            have hmul := mul_le_mul_of_nonneg_right hσ_bound hden.le
            have hcancel :
                ((b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|) * |(A *ᵥ r) i| =
                  b i - (A *ᵥ xbar) i := by
              field_simp [hden.ne']
            simpa [hcancel] using hmul
          have habs_le : |σ * (A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            simpa [abs_mul] using hmul_le
          have hterm_le : σ * (A *ᵥ r) i ≤ b i - (A *ᵥ xbar) i := by
            exact (le_abs_self _).trans habs_le
          calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ ≤ b i := by linarith
    let xMinus : Fin n → ℝ := xbar - ε • r
    let xPlus : Fin n → ℝ := xbar + ε • r
    have hxMinus : xMinus ∈ polyhedron_le_set A b := by
      have hneg : |(-ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xMinus, sub_eq_add_neg] using (hperturb_mem (σ := -ε) hneg)
    have hxPlus : xPlus ∈ polyhedron_le_set A b := by
      have hpos : |(ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xPlus] using (hperturb_mem (σ := ε) hpos)
    have hxMinus_ne : xMinus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := sub_eq_self.mp hEq
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxPlus_ne : xPlus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := by
        have := congrArg (fun u : Fin n → ℝ ↦ u - xbar) hEq
        simpa [xPlus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxbar_segment : xbar ∈ segment ℝ xMinus xPlus := by
      simpa [xMinus, xPlus] using (mem_segment_sub_add (𝕜 := ℝ) xbar (ε • r))
    have hxbar_open : xbar ∈ openSegment ℝ xMinus xPlus := by
      exact mem_openSegment_of_ne_left_right hxMinus_ne hxPlus_ne hxbar_segment
    have hxext := (mem_extremePoints_iff_left).mp hxbar_vertex
    exact hxMinus_ne (hxext.2 xMinus hxMinus xPlus hxPlus hxbar_open)
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ activeRows) = n := by
    rw [hspan]
    simpa using (Module.finrank_fin_fun ℝ (n := n))
  obtain ⟨g, hg_mem, _hg_span, hg_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ activeRows
  let e : Fin (Module.finrank ℝ ↥(Submodule.span ℝ activeRows)) ≃ Fin n :=
    (Fin.castOrderIso hdim).toEquiv
  let rows : Fin n → Fin n → ℝ := fun i ↦ g (e.symm i)
  have hrows_mem : ∀ i : Fin n, rows i ∈ activeRows := by
    intro i
    exact hg_mem (e.symm i)
  have hrows_linear : LinearIndependent ℝ rows := by
    exact (linearIndependent_equiv e.symm).2 hg_linear
  have hrows_mem' :
      ∀ i : Fin n, ∃ j : {j // (A *ᵥ xbar) j = b j}, A j.1 = rows i := by
    intro i
    simpa [activeRows] using hrows_mem i
  let chosen : Fin n → {j // (A *ᵥ xbar) j = b j} :=
    fun i ↦ Classical.choose (hrows_mem' i)
  have hchosen_row : ∀ i : Fin n, A (chosen i).1 = rows i := by
    intro i
    exact Classical.choose_spec (hrows_mem' i)
  have hchosen_injective : Function.Injective fun i : Fin n ↦ (chosen i).1 := by
    intro i j hij
    apply hrows_linear.injective
    calc
      rows i = A (chosen i).1 := (hchosen_row i).symm
      _ = A (chosen j).1 := by simpa [hij]
      _ = rows j := hchosen_row j
  let I : Fin n ↪ Fin m := ⟨fun i ↦ (chosen i).1, hchosen_injective⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    exact (chosen i).2
  · have hrows : (fun i : Fin n ↦ A (I i)) = rows := by
      funext i
      exact hchosen_row i
    simpa [hrows] using hrows_linear

/-- Helper for Exercise 4.24: an active nonnegativity row of the stacked system forces the
corresponding coordinate to vanish. -/
lemma exercise_4_24_eq_zero_of_active_nonnegativity_row
    {x : Fin 6 → ℝ} {r : Fin 10}
    (hr : 4 ≤ r)
    (hEq :
      ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ x) r =
        (exercise_4_24_constraint_rhs r : ℝ)) :
    ∃ j : Fin 6, r = ⟨j.1 + 4, by omega⟩ ∧ x j = 0 := by
  -- Evaluate the active row explicitly; rows `4` through `9` are the equations `-x_j = 0`.
  fin_cases r
  · exfalso
    cases hr
  · exfalso
    exact (show ¬ ((4 : Fin 10) ≤ 1) from by decide) hr
  · exfalso
    exact (show ¬ ((4 : Fin 10) ≤ 2) from by decide) hr
  · exfalso
    exact (show ¬ ((4 : Fin 10) ≤ 3) from by decide) hr
  · refine ⟨0, by decide, ?_⟩
    have hEq' := hEq
    rw [exercise_4_24_constraint_mulVec] at hEq'
    simpa [exercise_4_24_constraint_rhs] using hEq'
  · refine ⟨1, by decide, ?_⟩
    have hEq' := hEq
    rw [exercise_4_24_constraint_mulVec] at hEq'
    simpa [exercise_4_24_constraint_rhs] using hEq'
  · refine ⟨2, by decide, ?_⟩
    have hEq' := hEq
    rw [exercise_4_24_constraint_mulVec] at hEq'
    simpa [exercise_4_24_constraint_rhs] using hEq'
  · refine ⟨3, by decide, ?_⟩
    have hEq' := hEq
    rw [exercise_4_24_constraint_mulVec] at hEq'
    simpa [exercise_4_24_constraint_rhs] using hEq'
  · refine ⟨4, by decide, ?_⟩
    have hEq' := hEq
    rw [exercise_4_24_constraint_mulVec] at hEq'
    simpa [exercise_4_24_constraint_rhs] using hEq'
  · refine ⟨5, by decide, ?_⟩
    have hEq' := hEq
    rw [exercise_4_24_constraint_mulVec] at hEq'
    simpa [exercise_4_24_constraint_rhs] using hEq'

/-- Helper for Exercise 4.24: every ambient vertex of the stacked rational presentation has at
least two zero coordinates, because six active independent rows cannot come from only the four
covering inequalities. -/
lemma exercise_4_24_extremePoint_has_two_zero_coordinates
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ) :
    ∃ i j : Fin 6, i ≠ j ∧ x i = 0 ∧ x j = 0 := by
  have hxP :
      x ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs :=
    extremePoints_subset hx
  obtain ⟨I, hActive, _hLinInd⟩ :=
    exists_active_linearlyIndependent_rows_of_extremePoint_polyhedron
      ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)))
      (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ))
      hxP
      (by simpa [rational_matrix_polyhedron] using hx)
  let coverRows : Finset (Fin 6) := Finset.univ.filter (fun i : Fin 6 ↦ I i < 4)
  have hcoverRows_card : coverRows.card ≤ 4 := by
    let f : coverRows → (Finset.univ : Finset (Fin 4)) := fun i ↦
      ⟨⟨I i.1, (Finset.mem_filter.mp i.2).2⟩, by simp⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply I.injective
      apply Fin.ext
      exact congrArg (fun z ↦ z.1.1) hab
    simpa [coverRows, f] using
      (Finset.card_le_card_of_injective
        (s := coverRows)
        (t := (Finset.univ : Finset (Fin 4)))
        (f := f)
        hf)
  have hpartition :
      coverRows.card +
          (Finset.univ.filter (fun i : Fin 6 ↦ 4 ≤ I i)).card = 6 := by
    simpa [coverRows, Nat.not_lt] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i : Fin 6 ↦ I i < 4))
  have hnonnegRows_card : 2 ≤ (Finset.univ.filter (fun i : Fin 6 ↦ 4 ≤ I i)).card := by
    linarith
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (by simpa using hnonnegRows_card)
  have hIa_ge : 4 ≤ I a := (Finset.mem_filter.mp ha).2
  have hIb_ge : 4 ≤ I b := (Finset.mem_filter.mp hb).2
  have hIa_eq :
      ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ x) (I a) =
        (exercise_4_24_constraint_rhs (I a) : ℝ) :=
    hActive a
  have hIb_eq :
      ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ x) (I b) =
        (exercise_4_24_constraint_rhs (I b) : ℝ) :=
    hActive b
  rcases exercise_4_24_eq_zero_of_active_nonnegativity_row hIa_ge hIa_eq with
    ⟨i, hirow, hix⟩
  rcases exercise_4_24_eq_zero_of_active_nonnegativity_row hIb_ge hIb_eq with
    ⟨j, hjrow, hjx⟩
  have hij : i ≠ j := by
    intro hijEq
    apply hab
    apply I.injective
    rw [hirow, hjrow, hijEq]
  exact ⟨i, j, hij, hix, hjx⟩

/-- Helper for Exercise 4.24: feasibility in the stacked rational presentation is exactly the
ten scalar inequalities from the displayed covering system. -/
private lemma exercise_4_24_mem_rational_matrix_polyhedron_iff
    {x : Fin 6 → ℝ} :
    x ∈ rational_matrix_polyhedron
      exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs ↔
      1 ≤ x 0 + x 1 + x 3 ∧
        1 ≤ x 0 + x 2 + x 4 ∧
        1 ≤ x 1 + x 2 + x 5 ∧
        1 ≤ x 3 + x 4 + x 5 ∧
        0 ≤ x 0 ∧
        0 ≤ x 1 ∧
        0 ≤ x 2 ∧
        0 ≤ x 3 ∧
        0 ≤ x 4 ∧
        0 ≤ x 5 := by
  rw [mem_rational_matrix_polyhedron, exercise_4_24_constraint_mulVec]
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 0)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 1)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 2)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 3)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 4)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 5)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 6)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 7)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 8)
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg (hx 9)
  · rintro ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
    intro r
    fin_cases r
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg h013
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg h024
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg h125
    · simpa [exercise_4_24_constraint_rhs] using neg_le_neg h345
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr h0
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr h1
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr h2
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr h3
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr h4
    · simpa [exercise_4_24_constraint_rhs] using neg_nonpos.mpr h5

/-- Helper for Exercise 4.24: every point is the midpoint of its symmetric perturbation pair. -/
private lemma exercise_4_24_mem_openSegment_of_symmetric_perturbation
    (x r : Fin 6 → ℝ) :
    x ∈ openSegment ℝ (x - r) (x + r) := by
  -- The midpoint identity records the geometric contradiction used in every nonvertex branch.
  simpa [sub_eq_add_neg] using (mem_openSegment_sub_add (𝕜 := ℝ) x r)

/-- Helper for Exercise 4.24: a nonzero symmetric perturbation inside the same polyhedron rules
out extremeness. -/
private lemma exercise_4_24_notExtreme_of_twoSidedPerturbation
    {x r : Fin 6 → ℝ}
    (hminus :
      x - r ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs)
    (hplus :
      x + r ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs)
    (hr : r ≠ 0) :
    x ∉ (rational_matrix_polyhedron
      exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ := by
  intro hx
  -- Route correction: work directly on the owner polyhedron instead of the old active-system
  -- classifier, so the contradiction is just the midpoint criterion for extreme points.
  have hminus_eq : x - r = x :=
    (mem_extremePoints_iff_left.mp hx).2
      (x - r) hminus (x + r) hplus
      (exercise_4_24_mem_openSegment_of_symmetric_perturbation x r)
  have hr_zero : r = 0 := by
    ext j
    exact sub_eq_self.mp (congrArg (fun p ↦ p j) hminus_eq)
  exact hr hr_zero

/-- Helper for Exercise 4.24: the square rational active subsystem cut out by a chosen active-row
injection `I`. -/
private def exercise_4_24_activeMatrixQ (I : Fin 6 ↪ Fin 10) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j ↦ exercise_4_24_constraint_matrix (I i) j

/-- Helper for Exercise 4.24: the same active subsystem after coercing the coefficients to `ℝ`. -/
private def exercise_4_24_activeMatrixR (I : Fin 6 ↪ Fin 10) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j ↦ (exercise_4_24_constraint_matrix (I i) j : ℝ)

/-- Helper for Exercise 4.24: the right-hand side of the rational active subsystem selected by
`I`. -/
private def exercise_4_24_activeRhsQ (I : Fin 6 ↪ Fin 10) : Fin 6 → ℚ :=
  fun i ↦ exercise_4_24_constraint_rhs (I i)

/-- Helper for Exercise 4.24: the real right-hand side of the active subsystem selected by `I`. -/
private def exercise_4_24_activeRhsR (I : Fin 6 ↪ Fin 10) : Fin 6 → ℝ :=
  fun i ↦ (exercise_4_24_constraint_rhs (I i) : ℝ)

/-- Helper for Exercise 4.24: the rational Cramer solution of the active subsystem selected by
`I`. -/
private def exercise_4_24_activeSystemSolutionQ (I : Fin 6 ↪ Fin 10) : Fin 6 → ℚ :=
  ((exercise_4_24_activeMatrixQ I).det)⁻¹ •
    (exercise_4_24_activeMatrixQ I).cramer (exercise_4_24_activeRhsQ I)

/-- Helper for Exercise 4.24: the square rational subsystem cut out by an arbitrary row-selection
function on `Fin 6`. This proof-free spelling is used only for the finite classifier. -/
private def exercise_4_24_activeMatrixQOfFun (f : Fin 6 → Fin 10) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j ↦ exercise_4_24_constraint_matrix (f i) j

/-- Helper for Exercise 4.24: the right-hand side of the proof-free active subsystem used in the
finite classifier. -/
private def exercise_4_24_activeRhsQOfFun (f : Fin 6 → Fin 10) : Fin 6 → ℚ :=
  fun i ↦ exercise_4_24_constraint_rhs (f i)

/-- Helper for Exercise 4.24: the rational Cramer solution attached to the proof-free active
subsystem used in the finite classifier. -/
private def exercise_4_24_activeSystemSolutionQOfFun (f : Fin 6 → Fin 10) : Fin 6 → ℚ :=
  ((exercise_4_24_activeMatrixQOfFun f).det)⁻¹ •
    (exercise_4_24_activeMatrixQOfFun f).cramer (exercise_4_24_activeRhsQOfFun f)

/-- Helper for Exercise 4.24: row independence of the real active subsystem forces the
corresponding rational determinant to be nonzero. -/
private lemma exercise_4_24_activeMatrixQ_det_ne_zero
    (I : Fin 6 ↪ Fin 10)
    (hLinInd :
      LinearIndependent ℝ (fun i : Fin 6 ↦ exercise_4_24_activeMatrixR I i)) :
    (exercise_4_24_activeMatrixQ I).det ≠ 0 := by
  -- Convert the row-independence witness into a matrix unit over `ℝ`, then descend nonvanishing
  -- of the determinant along the rational-to-real coefficient map.
  have hUnitR : IsUnit (exercise_4_24_activeMatrixR I) :=
    (Matrix.linearIndependent_rows_iff_isUnit).mp
      (by simpa [exercise_4_24_activeMatrixR] using hLinInd)
  have hDetUnitR : IsUnit (exercise_4_24_activeMatrixR I).det :=
    (Matrix.isUnit_iff_isUnit_det (exercise_4_24_activeMatrixR I)).mp hUnitR
  intro hDetQ
  have hMap :
      ((exercise_4_24_activeMatrixQ I).det : ℝ) =
        (exercise_4_24_activeMatrixR I).det := by
    simpa [exercise_4_24_activeMatrixQ, exercise_4_24_activeMatrixR] using
      RingHom.map_det (Rat.castHom ℝ) (exercise_4_24_activeMatrixQ I)
  have hDetR : (exercise_4_24_activeMatrixR I).det = 0 := by
    rw [← hMap, hDetQ]
    norm_num
  exact hDetUnitR.ne_zero hDetR

/-- Helper for Exercise 4.24: a rational solution of the active subsystem remains a solution after
coercing every coefficient to `ℝ`. -/
private lemma exercise_4_24_activeSolution_cast
    (I : Fin 6 ↪ Fin 10) {v : Fin 6 → ℚ}
    (hv :
      exercise_4_24_activeMatrixQ I *ᵥ v = exercise_4_24_activeRhsQ I) :
    exercise_4_24_activeMatrixR I *ᵥ (fun j ↦ (v j : ℝ)) =
      exercise_4_24_activeRhsR I := by
  -- Map the whole matrix-vector equality through the rational-to-real ring homomorphism.
  ext i
  have hmap := RingHom.map_mulVec (Rat.castHom ℝ) (exercise_4_24_activeMatrixQ I) v i
  rw [hv] at hmap
  simpa [exercise_4_24_activeMatrixQ, exercise_4_24_activeMatrixR,
    exercise_4_24_activeRhsQ, exercise_4_24_activeRhsR] using hmap.symm

/-- Helper for Exercise 4.24: the active equalities and row independence identify a vertex with
the real cast of the rational Cramer solution of the same active subsystem. -/
private lemma exercise_4_24_activeSystemSolution_eq_vertex
    (I : Fin 6 ↪ Fin 10) {x : Fin 6 → ℝ}
    (hActive :
      ∀ i : Fin 6,
        ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ x) (I i) =
          (exercise_4_24_constraint_rhs (I i) : ℝ))
    (hLinInd :
      LinearIndependent ℝ (fun i : Fin 6 ↦ exercise_4_24_activeMatrixR I i)) :
    x = fun j ↦ (exercise_4_24_activeSystemSolutionQ I j : ℝ) := by
  have hDetQ :
      (exercise_4_24_activeMatrixQ I).det ≠ 0 :=
    exercise_4_24_activeMatrixQ_det_ne_zero I hLinInd
  have hActiveVec :
      exercise_4_24_activeMatrixR I *ᵥ x = exercise_4_24_activeRhsR I := by
    -- The active equalities show that `x` solves the real subsystem cut out by `I`.
    ext i
    simpa [exercise_4_24_activeMatrixR, exercise_4_24_activeRhsR] using hActive i
  have hUnitR : IsUnit (exercise_4_24_activeMatrixR I) :=
    (Matrix.linearIndependent_rows_iff_isUnit).mp
      (by simpa [exercise_4_24_activeMatrixR] using hLinInd)
  have hInj :
      Function.Injective (exercise_4_24_activeMatrixR I).mulVec :=
    Matrix.mulVec_injective_of_isUnit hUnitR
  have hCandidate :
      exercise_4_24_activeMatrixQ I *ᵥ exercise_4_24_activeSystemSolutionQ I =
        exercise_4_24_activeRhsQ I := by
    -- Cramer's rule computes the unique rational solution of the nonsingular active subsystem.
    calc
      exercise_4_24_activeMatrixQ I *ᵥ exercise_4_24_activeSystemSolutionQ I =
          exercise_4_24_activeMatrixQ I *ᵥ
            (((exercise_4_24_activeMatrixQ I).det)⁻¹ •
              (exercise_4_24_activeMatrixQ I).cramer (exercise_4_24_activeRhsQ I)) := by
        rfl
      _ = ((exercise_4_24_activeMatrixQ I).det)⁻¹ •
            (exercise_4_24_activeMatrixQ I *ᵥ
              (exercise_4_24_activeMatrixQ I).cramer (exercise_4_24_activeRhsQ I)) := by
        rw [Matrix.mulVec_smul]
      _ = ((exercise_4_24_activeMatrixQ I).det)⁻¹ •
            ((exercise_4_24_activeMatrixQ I).det • exercise_4_24_activeRhsQ I) := by
        rw [Matrix.mulVec_cramer]
      _ = exercise_4_24_activeRhsQ I := by
        ext i
        simp [Pi.smul_apply, hDetQ]
  have hCandidateR :
      exercise_4_24_activeMatrixR I *ᵥ
          (fun j ↦ (exercise_4_24_activeSystemSolutionQ I j : ℝ)) =
        exercise_4_24_activeRhsR I :=
    exercise_4_24_activeSolution_cast I hCandidate
  exact hInj (hActiveVec.trans hCandidateR.symm)

/-- Helper for Exercise 4.24: feasibility of a real point transfers back to a rational vector
once the real point is identified with the coordinatewise cast of that vector. -/
private lemma exercise_4_24_rationalFeasible_of_realCast
    {x : Fin 6 → ℝ} {v : Fin 6 → ℚ}
    (hx :
      x ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs)
    (hxv : x = fun j ↦ (v j : ℝ)) :
    ∀ r, (exercise_4_24_constraint_matrix *ᵥ v) r ≤
      exercise_4_24_constraint_rhs r := by
  rw [mem_rational_matrix_polyhedron] at hx
  intro r
  have hxLeReal :
      ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ
        (fun j ↦ (v j : ℝ))) r ≤
        (exercise_4_24_constraint_rhs r : ℝ) := by
    simpa [hxv] using hx r
  have hmap :
      ((exercise_4_24_constraint_matrix.map (Rat.castHom ℝ)) *ᵥ
        (fun j ↦ (v j : ℝ))) r =
        ((exercise_4_24_constraint_matrix *ᵥ v) r : ℝ) := by
    simpa [Function.comp] using
      (RingHom.map_mulVec (Rat.castHom ℝ) exercise_4_24_constraint_matrix v r).symm
  rw [hmap] at hxLeReal
  exact_mod_cast hxLeReal

/-- Helper for Exercise 4.24: each of the seven explicit `0,1` edge-cover vectors already belongs
to `integerVectors 6`. -/
private lemma exercise_4_24_explicitCoverVector_mem_integerVectors
    {x : Fin 6 → ℝ}
    (hx :
      x = ![(1 : ℝ), 0, 0, 0, 0, 1] ∨
        x = ![(0 : ℝ), 1, 0, 0, 1, 0] ∨
        x = ![(0 : ℝ), 0, 1, 1, 0, 0] ∨
        x = ![(1 : ℝ), 1, 0, 1, 0, 0] ∨
        x = ![(1 : ℝ), 0, 1, 0, 1, 0] ∨
        x = ![(0 : ℝ), 1, 1, 0, 0, 1] ∨
        x = ![(0 : ℝ), 0, 0, 1, 1, 1]) :
    x ∈ integerVectors 6 := by
  -- Package the explicit `0,1` vectors as casts of integer incidence vectors.
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(1 : ℤ), 0, 0, 0, 0, 1], ?_⟩
    ext j
    fin_cases j <;> norm_num
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(0 : ℤ), 1, 0, 0, 1, 0], ?_⟩
    ext j
    fin_cases j <;> norm_num
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(0 : ℤ), 0, 1, 1, 0, 0], ?_⟩
    ext j
    fin_cases j <;> norm_num
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(1 : ℤ), 1, 0, 1, 0, 0], ?_⟩
    ext j
    fin_cases j <;> norm_num
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(1 : ℤ), 0, 1, 0, 1, 0], ?_⟩
    ext j
    fin_cases j <;> norm_num
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(0 : ℤ), 1, 1, 0, 0, 1], ?_⟩
    ext j
    fin_cases j <;> norm_num
  · refine (mem_integerVectors_iff).2 ?_
    refine ⟨![(0 : ℤ), 0, 0, 1, 1, 1], ?_⟩
    ext j
    fin_cases j <;> norm_num

/-- Helper for Exercise 4.24: every coordinate of an ambient extreme point is at most `1`,
because a coordinate strictly larger than `1` admits a symmetric one-coordinate perturbation. -/
private lemma exercise_4_24_coordinate_le_one_of_extremePoint
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ)
    (k : Fin 6) :
    x k ≤ 1 := by
  have hxP :=
    (exercise_4_24_mem_rational_matrix_polyhedron_iff).1 (extremePoints_subset hx)
  rcases hxP with ⟨_h013, _h024, _h125, _h345, h0, h1, h2, h3, h4, h5⟩
  fin_cases k
  · by_contra hk
    have hk' : 1 < x 0 := lt_of_not_ge hk
    let ε : ℝ := (x 0 - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let r : Fin 6 → ℝ := ![(ε : ℝ), 0, 0, 0, 0, 0]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Decrease only the first coordinate; it stays above `1`, so both incident cover sums remain
      -- feasible.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h1, h3, hk']
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h2, h4, hk']
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg]
        linarith
      · simpa [r] using h1
      · simpa [r] using h2
      · simpa [r] using h3
      · simpa [r] using h4
      · simpa [r] using h5
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Increasing one coordinate preserves every inequality immediately.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h1, h3]
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h2, h4]
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simpa [r] using h1
      · simpa [r] using h2
      · simpa [r] using h3
      · simpa [r] using h4
      · simpa [r] using h5
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 0) hr0
      exact hε.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
  · by_contra hk
    have hk' : 1 < x 1 := lt_of_not_ge hk
    let ε : ℝ := (x 1 - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let r : Fin 6 → ℝ := ![(0 : ℝ), ε, 0, 0, 0, 0]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Decrease only the second coordinate; it stays above `1`, so both incident cover sums
      -- remain feasible.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h0, h3, hk']
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h2, h5, hk']
      · simp [r]
        linarith
      · simpa [r] using h0
      · simp [r, ε, sub_eq_add_neg]
        linarith
      · simpa [r] using h2
      · simpa [r] using h3
      · simpa [r] using h4
      · simpa [r] using h5
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Increasing one coordinate preserves every inequality immediately.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h0, h3]
      · simp [r]
        linarith
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h2, h5]
      · simp [r]
        linarith
      · simpa [r] using h0
      · simp [r]
        linarith
      · simpa [r] using h2
      · simpa [r] using h3
      · simpa [r] using h4
      · simpa [r] using h5
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 1) hr0
      exact hε.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
  · by_contra hk
    have hk' : 1 < x 2 := lt_of_not_ge hk
    let ε : ℝ := (x 2 - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let r : Fin 6 → ℝ := ![(0 : ℝ), 0, ε, 0, 0, 0]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Decrease only the third coordinate; it stays above `1`, so both incident cover sums remain
      -- feasible.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h0, h4, hk']
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h1, h5, hk']
      · simp [r]
        linarith
      · simpa [r] using h0
      · simpa [r] using h1
      · simp [r, ε, sub_eq_add_neg]
        linarith
      · simpa [r] using h3
      · simpa [r] using h4
      · simpa [r] using h5
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Increasing one coordinate preserves every inequality immediately.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r]
        linarith
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h0, h4]
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h1, h5]
      · simp [r]
        linarith
      · simpa [r] using h0
      · simpa [r] using h1
      · simp [r]
        linarith
      · simpa [r] using h3
      · simpa [r] using h4
      · simpa [r] using h5
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 2) hr0
      exact hε.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
  · by_contra hk
    have hk' : 1 < x 3 := lt_of_not_ge hk
    let ε : ℝ := (x 3 - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, ε, 0, 0]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Decrease only the fourth coordinate; it stays above `1`, so both incident cover sums
      -- remain feasible.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h0, h1, hk']
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h4, h5, hk']
      · simpa [r] using h0
      · simpa [r] using h1
      · simpa [r] using h2
      · simp [r, ε, sub_eq_add_neg]
        linarith
      · simpa [r] using h4
      · simpa [r] using h5
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Increasing one coordinate preserves every inequality immediately.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h0, h1]
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h4, h5]
      · simpa [r] using h0
      · simpa [r] using h1
      · simpa [r] using h2
      · simp [r]
        linarith
      · simpa [r] using h4
      · simpa [r] using h5
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 3) hr0
      exact hε.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
  · by_contra hk
    have hk' : 1 < x 4 := lt_of_not_ge hk
    let ε : ℝ := (x 4 - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, 0, ε, 0]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Decrease only the fifth coordinate; it stays above `1`, so both incident cover sums remain
      -- feasible.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h0, h2, hk']
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h3, h5, hk']
      · simpa [r] using h0
      · simpa [r] using h1
      · simpa [r] using h2
      · simpa [r] using h3
      · simp [r, ε, sub_eq_add_neg]
        linarith
      · simpa [r] using h5
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Increasing one coordinate preserves every inequality immediately.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r]
        linarith
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h0, h2]
      · simp [r]
        linarith
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h3, h5]
      · simpa [r] using h0
      · simpa [r] using h1
      · simpa [r] using h2
      · simpa [r] using h3
      · simp [r]
        linarith
      · simpa [r] using h5
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 4) hr0
      exact hε.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
  · by_contra hk
    have hk' : 1 < x 5 := lt_of_not_ge hk
    let ε : ℝ := (x 5 - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, 0, 0, ε]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Decrease only the last coordinate; it stays above `1`, so both incident cover sums remain
      -- feasible.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h1, h2, hk']
      · simp [r, ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [h3, h4, hk']
      · simpa [r] using h0
      · simpa [r] using h1
      · simpa [r] using h2
      · simpa [r] using h3
      · simpa [r] using h4
      · simp [r, ε, sub_eq_add_neg]
        linarith
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Increasing one coordinate preserves every inequality immediately.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [r]
        linarith
      · simp [r]
        linarith
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h1, h2]
      · simp [r, add_assoc, add_left_comm, add_comm]
        linarith [h3, h4]
      · simpa [r] using h0
      · simpa [r] using h1
      · simpa [r] using h2
      · simpa [r] using h3
      · simpa [r] using h4
      · simp [r]
        linarith
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 5) hr0
      exact hε.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx

/-- Helper for Exercise 4.24: if coordinates `0` and `1` vanish at an ambient extreme point, then
the remaining edge incident to that common vertex is forced to be `1`. -/
private lemma exercise_4_24_adjacentPair01_x3_eq_one
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    x 3 = 1 := by
  -- Normalize feasibility once, then row `013` and the global coordinate bound squeeze `x 3`.
  rcases
      (exercise_4_24_mem_rational_matrix_polyhedron_iff.1 (extremePoints_subset hx)) with
    ⟨h013, _h024, _h125, _h345, _h0, _h1, _h2, _h3, _h4, _h5⟩
  have hx3_ge : 1 ≤ x 3 := by
    linarith [h013]
  have hx3_le : x 3 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 3
  linarith

/-- Helper for Exercise 4.24: the adjacent zero pair `(0,1)` cuts out exactly the two endpoint
edge covers on that fork face. -/
private lemma exercise_4_24_adjacentPair01_cases
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ)
    (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    x = ![(0 : ℝ), 0, 1, 1, 0, 0] ∨
      x = ![(0 : ℝ), 0, 0, 1, 1, 1] := by
  rcases
      (exercise_4_24_mem_rational_matrix_polyhedron_iff.1 (extremePoints_subset hx)) with
    ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
  have hx3_eq : x 3 = 1 := exercise_4_24_adjacentPair01_x3_eq_one hx hx0 hx1
  have hx2_cases : x 2 = 0 ∨ x 2 = 1 := by
    by_contra hx2_not
    have hx2_ne_zero : x 2 ≠ 0 := by
      intro hx2_eq
      exact hx2_not (Or.inl hx2_eq)
    have hx2_ne_one : x 2 ≠ 1 := by
      intro hx2_eq
      exact hx2_not (Or.inr hx2_eq)
    have hx2_pos : 0 < x 2 := by
      exact lt_of_le_of_ne h2 (by simpa [eq_comm] using hx2_ne_zero)
    have hx2_lt_one : x 2 < 1 := by
      exact lt_of_le_of_ne (exercise_4_24_coordinate_le_one_of_extremePoint hx 2) hx2_ne_one
    have hx4_pos : 0 < x 4 := by
      linarith
    have hx5_pos : 0 < x 5 := by
      linarith
    let ε : ℝ := min (x 2) (min (x 4) (x 5)) / 2
    have hε_pos : 0 < ε := by
      -- Choose a positive perturbation radius smaller than the three positive free coordinates.
      dsimp [ε]
      have hmin_pos : 0 < min (x 2) (min (x 4) (x 5)) := by
        exact lt_min hx2_pos (lt_min hx4_pos hx5_pos)
      linarith
    have hε_le_x2 : ε ≤ x 2 := by
      dsimp [ε]
      have hmin_le : min (x 2) (min (x 4) (x 5)) ≤ x 2 := min_le_left _ _
      linarith
    have hε_le_x4 : ε ≤ x 4 := by
      dsimp [ε]
      have hmin_le : min (x 2) (min (x 4) (x 5)) ≤ min (x 4) (x 5) := min_le_right _ _
      have hmin_le' : min (x 4) (x 5) ≤ x 4 := min_le_left _ _
      linarith
    have hε_le_x5 : ε ≤ x 5 := by
      dsimp [ε]
      have hmin_le : min (x 2) (min (x 4) (x 5)) ≤ min (x 4) (x 5) := min_le_right _ _
      have hmin_le' : min (x 4) (x 5) ≤ x 5 := min_le_right _ _
      linarith
    let r : Fin 6 → ℝ := ![(0 : ℝ), 0, ε, 0, -ε, -ε]
    have hminus :
        x - r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- Move mass from coordinate `2` into `4` and `5`; the two active cover sums stay fixed.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h013
      · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h024
      · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h125
      · simp [r, hx3_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        linarith [hε_le_x4, hε_le_x5, h4, h5]
      · simpa [r, sub_eq_add_neg] using h0
      · simpa [r, sub_eq_add_neg] using h1
      · simp [r, sub_eq_add_neg]
        linarith
      · simpa [r, hx3_eq, sub_eq_add_neg] using h3
      · simp [r, sub_eq_add_neg]
        linarith
      · simp [r, sub_eq_add_neg]
        linarith
    have hplus :
        x + r ∈ rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
      -- The opposite perturbation keeps the same two active sums fixed and preserves
      -- nonnegativity because `ε` is below `x 4` and `x 5`.
      refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [r, add_assoc, add_left_comm, add_comm] using h013
      · simpa [r, add_assoc, add_left_comm, add_comm] using h024
      · simpa [r, add_assoc, add_left_comm, add_comm] using h125
      · simp [r, hx3_eq, add_assoc, add_left_comm, add_comm]
        linarith [hε_le_x4, hε_le_x5, h4, h5]
      · simpa [r] using h0
      · simpa [r] using h1
      · simp [r]
        linarith
      · simpa [r, hx3_eq] using h3
      · simp [r]
        linarith
      · simp [r]
        linarith
    have hr : r ≠ 0 := by
      intro hr0
      have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 2) hr0
      exact hε_pos.ne' (by simpa [r] using hcoord)
    exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
  rcases hx2_cases with hx2_eq | hx2_eq
  · -- At the endpoint `x 2 = 0`, the remaining two cover inequalities force `x 4 = x 5 = 1`.
    have hx4_eq : x 4 = 1 := by
      have hx4_ge : 1 ≤ x 4 := by
        linarith
      have hx4_le : x 4 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 4
      linarith
    have hx5_eq : x 5 = 1 := by
      have hx5_ge : 1 ≤ x 5 := by
        linarith
      have hx5_le : x 5 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 5
      linarith
    right
    ext k
    fin_cases k <;> simp [hx0, hx1, hx2_eq, hx3_eq, hx4_eq, hx5_eq]
  · have hx4_zero : x 4 = 0 := by
      by_contra hx4_ne
      have hx4_pos : 0 < x 4 := by
        exact lt_of_le_of_ne h4 (by simpa [eq_comm] using hx4_ne)
      let ε : ℝ := x 4 / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hε_le_x4 : ε ≤ x 4 := by
        dsimp [ε]
        linarith
      let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, 0, ε, 0]
      have hminus :
          x - r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        -- Once `x 2 = x 3 = 1`, coordinate `4` is pure slack and cannot stay positive at a vertex.
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h013
        · simp [r, hx2_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h125
        · simp [r, hx3_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith [h5]
        · simpa [r, sub_eq_add_neg] using h0
        · simpa [r, sub_eq_add_neg] using h1
        · simpa [r, hx2_eq, sub_eq_add_neg] using h2
        · simpa [r, hx3_eq, sub_eq_add_neg] using h3
        · simp [r, sub_eq_add_neg]
          linarith
        · simpa [r, sub_eq_add_neg] using h5
      have hplus :
          x + r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        -- Increasing the slack coordinate preserves every inequality immediately.
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, add_assoc, add_left_comm, add_comm] using h013
        · simp [r, hx2_eq, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, add_assoc, add_left_comm, add_comm] using h125
        · simp [r, hx3_eq, add_assoc, add_left_comm, add_comm]
          linarith [h5]
        · simpa [r] using h0
        · simpa [r] using h1
        · simpa [r, hx2_eq] using h2
        · simpa [r, hx3_eq] using h3
        · simp [r]
          linarith
        · simpa [r] using h5
      have hr : r ≠ 0 := by
        intro hr0
        have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 4) hr0
        exact hε_pos.ne' (by simpa [r] using hcoord)
      exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
    have hx5_zero : x 5 = 0 := by
      by_contra hx5_ne
      have hx5_pos : 0 < x 5 := by
        exact lt_of_le_of_ne h5 (by simpa [eq_comm] using hx5_ne)
      let ε : ℝ := x 5 / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hε_le_x5 : ε ≤ x 5 := by
        dsimp [ε]
        linarith
      let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, 0, 0, ε]
      have hminus :
          x - r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        -- The same slack-coordinate contradiction kills coordinate `5`.
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h013
        · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h024
        · simp [r, hx2_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simp [r, hx3_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith [hx4_zero]
        · simpa [r, sub_eq_add_neg] using h0
        · simpa [r, sub_eq_add_neg] using h1
        · simpa [r, hx2_eq, sub_eq_add_neg] using h2
        · simpa [r, hx3_eq, sub_eq_add_neg] using h3
        · simpa [r, hx4_zero, sub_eq_add_neg] using h4
        · simp [r, sub_eq_add_neg]
          linarith
      have hplus :
          x + r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, add_assoc, add_left_comm, add_comm] using h013
        · simpa [r, add_assoc, add_left_comm, add_comm] using h024
        · simp [r, hx2_eq, add_assoc, add_left_comm, add_comm]
          linarith
        · simp [r, hx3_eq, add_assoc, add_left_comm, add_comm]
          linarith [hx4_zero]
        · simpa [r] using h0
        · simpa [r] using h1
        · simpa [r, hx2_eq] using h2
        · simpa [r, hx3_eq] using h3
        · simpa [r, hx4_zero] using h4
        · simp [r]
          linarith
      have hr : r ≠ 0 := by
        intro hr0
        have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 5) hr0
        exact hε_pos.ne' (by simpa [r] using hcoord)
      exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
    left
    ext k
    fin_cases k <;> simp [hx0, hx1, hx2_eq, hx3_eq, hx4_zero, hx5_zero]

/-- Helper for Exercise 4.24: if coordinates `0` and `5` vanish, then the remaining four-cycle
cannot stay strictly positive at an ambient extreme point. -/
private lemma exercise_4_24_oppositePair05_hasThirdZero
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ)
    (hx0 : x 0 = 0) (hx5 : x 5 = 0) :
    x 1 = 0 ∨ x 2 = 0 ∨ x 3 = 0 ∨ x 4 = 0 := by
  rcases
      (exercise_4_24_mem_rational_matrix_polyhedron_iff.1 (extremePoints_subset hx)) with
    ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
  by_contra hnone
  have hx1_ne : x 1 ≠ 0 := by
    intro hx1_eq
    exact hnone (Or.inl hx1_eq)
  have hx2_ne : x 2 ≠ 0 := by
    intro hx2_eq
    exact hnone (Or.inr (Or.inl hx2_eq))
  have hx3_ne : x 3 ≠ 0 := by
    intro hx3_eq
    exact hnone (Or.inr (Or.inr (Or.inl hx3_eq)))
  have hx4_ne : x 4 ≠ 0 := by
    intro hx4_eq
    exact hnone (Or.inr (Or.inr (Or.inr hx4_eq)))
  have hx1_pos : 0 < x 1 := by
    exact lt_of_le_of_ne h1 (by simpa [eq_comm] using hx1_ne)
  have hx2_pos : 0 < x 2 := by
    exact lt_of_le_of_ne h2 (by simpa [eq_comm] using hx2_ne)
  have hx3_pos : 0 < x 3 := by
    exact lt_of_le_of_ne h3 (by simpa [eq_comm] using hx3_ne)
  have hx4_pos : 0 < x 4 := by
    exact lt_of_le_of_ne h4 (by simpa [eq_comm] using hx4_ne)
  let ε : ℝ := min (x 1) (min (x 2) (min (x 3) (x 4))) / 2
  have hε_pos : 0 < ε := by
    -- The four-cycle perturbation radius is chosen below every positive coordinate.
    dsimp [ε]
    have hmin_pos : 0 < min (x 1) (min (x 2) (min (x 3) (x 4))) := by
      exact lt_min hx1_pos (lt_min hx2_pos (lt_min hx3_pos hx4_pos))
    linarith
  have hε_le_x1 : ε ≤ x 1 := by
    dsimp [ε]
    have hmin_le : min (x 1) (min (x 2) (min (x 3) (x 4))) ≤ x 1 := min_le_left _ _
    linarith
  have hε_le_x2 : ε ≤ x 2 := by
    dsimp [ε]
    have hmin_le : min (x 1) (min (x 2) (min (x 3) (x 4))) ≤ min (x 2) (min (x 3) (x 4)) :=
      min_le_right _ _
    have hmin_le' : min (x 2) (min (x 3) (x 4)) ≤ x 2 := min_le_left _ _
    linarith
  have hε_le_x3 : ε ≤ x 3 := by
    dsimp [ε]
    have hmin_le : min (x 1) (min (x 2) (min (x 3) (x 4))) ≤ min (x 2) (min (x 3) (x 4)) :=
      min_le_right _ _
    have hmin_le' : min (x 2) (min (x 3) (x 4)) ≤ min (x 3) (x 4) := min_le_right _ _
    have hmin_le'' : min (x 3) (x 4) ≤ x 3 := min_le_left _ _
    linarith
  have hε_le_x4 : ε ≤ x 4 := by
    dsimp [ε]
    have hmin_le : min (x 1) (min (x 2) (min (x 3) (x 4))) ≤ min (x 2) (min (x 3) (x 4)) :=
      min_le_right _ _
    have hmin_le' : min (x 2) (min (x 3) (x 4)) ≤ min (x 3) (x 4) := min_le_right _ _
    have hmin_le'' : min (x 3) (x 4) ≤ x 4 := min_le_right _ _
    linarith
  let r : Fin 6 → ℝ := ![(0 : ℝ), ε, -ε, -ε, ε, 0]
  have hminus :
      x - r ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
    -- The cycle direction preserves all four covering sums exactly.
    refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h013
    · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h024
    · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h125
    · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h345
    · simpa [r, sub_eq_add_neg] using h0
    · simp [r, sub_eq_add_neg]
      linarith
    · simp [r, sub_eq_add_neg]
      linarith
    · simp [r, sub_eq_add_neg]
      linarith
    · simp [r, sub_eq_add_neg]
      linarith
    · simpa [r, sub_eq_add_neg] using h5
  have hplus :
      x + r ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
    refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [r, add_assoc, add_left_comm, add_comm] using h013
    · simpa [r, add_assoc, add_left_comm, add_comm] using h024
    · simpa [r, add_assoc, add_left_comm, add_comm] using h125
    · simpa [r, add_assoc, add_left_comm, add_comm] using h345
    · simpa [r] using h0
    · simp [r]
      linarith
    · simp [r]
      linarith
    · simp [r]
      linarith
    · simp [r]
      linarith
    · simpa [r] using h5
  have hr : r ≠ 0 := by
    intro hr0
    have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 1) hr0
    exact hε_pos.ne' (by simpa [r] using hcoord)
  exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx

/-- Helper for Exercise 4.24: the opposite zero pair `(0,5)` leaves only the two perfect-matching
edge covers. -/
private lemma exercise_4_24_oppositePair05_cases
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ)
    (hx0 : x 0 = 0) (hx5 : x 5 = 0) :
    x = ![(0 : ℝ), 1, 0, 0, 1, 0] ∨
      x = ![(0 : ℝ), 0, 1, 1, 0, 0] := by
  rcases
      (exercise_4_24_mem_rational_matrix_polyhedron_iff.1 (extremePoints_subset hx)) with
    ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
  rcases exercise_4_24_oppositePair05_hasThirdZero hx hx0 hx5 with
    hx1_eq | hx2_eq | hx3_eq | hx4_eq
  · -- If `x 1 = 0`, then `x 2 = x 3 = 1` and the remaining slack coordinate must vanish.
    have hx3_one : x 3 = 1 := by
      have hx3_ge : 1 ≤ x 3 := by
        linarith
      have hx3_le : x 3 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 3
      linarith
    have hx2_one : x 2 = 1 := by
      have hx2_ge : 1 ≤ x 2 := by
        linarith
      have hx2_le : x 2 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 2
      linarith
    have hx4_zero : x 4 = 0 := by
      by_contra hx4_ne
      have hx4_pos : 0 < x 4 := by
        exact lt_of_le_of_ne h4 (by simpa [eq_comm] using hx4_ne)
      let ε : ℝ := x 4 / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hε_le_x4 : ε ≤ x 4 := by
        dsimp [ε]
        linarith
      let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, 0, ε, 0]
      have hminus :
          x - r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h013
        · simp [r, hx2_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx1_eq, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h125
        · simp [r, hx3_one, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, sub_eq_add_neg] using h0
        · simpa [r, hx1_eq, sub_eq_add_neg] using h1
        · simpa [r, hx2_one, sub_eq_add_neg] using h2
        · simpa [r, hx3_one, sub_eq_add_neg] using h3
        · simp [r, sub_eq_add_neg]
          linarith
        · simpa [r, hx5, sub_eq_add_neg] using h5
      have hplus :
          x + r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, add_assoc, add_left_comm, add_comm] using h013
        · simp [r, hx2_one, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx1_eq, hx5, add_assoc, add_left_comm, add_comm] using h125
        · simp [r, hx3_one, hx5, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r] using h0
        · simpa [r, hx1_eq] using h1
        · simpa [r, hx2_one] using h2
        · simpa [r, hx3_one] using h3
        · simp [r]
          linarith
        · simpa [r, hx5] using h5
      have hr : r ≠ 0 := by
        intro hr0
        have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 4) hr0
        exact hε_pos.ne' (by simpa [r] using hcoord)
      exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
    right
    ext k
    fin_cases k <;> simp [hx0, hx1_eq, hx2_one, hx3_one, hx4_zero, hx5]
  · have hx4_one : x 4 = 1 := by
      have hx4_ge : 1 ≤ x 4 := by
        linarith
      have hx4_le : x 4 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 4
      linarith
    have hx1_one : x 1 = 1 := by
      have hx1_ge : 1 ≤ x 1 := by
        linarith
      have hx1_le : x 1 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 1
      linarith
    have hx3_zero : x 3 = 0 := by
      by_contra hx3_ne
      have hx3_pos : 0 < x 3 := by
        exact lt_of_le_of_ne h3 (by simpa [eq_comm] using hx3_ne)
      let ε : ℝ := x 3 / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hε_le_x3 : ε ≤ x 3 := by
        dsimp [ε]
        linarith
      let r : Fin 6 → ℝ := ![(0 : ℝ), 0, 0, ε, 0, 0]
      have hminus :
          x - r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [r, hx1_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx2_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h024
        · simpa [r, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h125
        · simp [r, hx4_one, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, sub_eq_add_neg] using h0
        · simpa [r, hx1_one, sub_eq_add_neg] using h1
        · simpa [r, hx2_eq, sub_eq_add_neg] using h2
        · simp [r, sub_eq_add_neg]
          linarith
        · simpa [r, hx4_one, sub_eq_add_neg] using h4
        · simpa [r, hx5, sub_eq_add_neg] using h5
      have hplus :
          x + r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [r, hx1_one, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx2_eq, add_assoc, add_left_comm, add_comm] using h024
        · simpa [r, hx5, add_assoc, add_left_comm, add_comm] using h125
        · simp [r, hx4_one, hx5, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r] using h0
        · simpa [r, hx1_one] using h1
        · simpa [r, hx2_eq] using h2
        · simp [r]
          linarith
        · simpa [r, hx4_one] using h4
        · simpa [r, hx5] using h5
      have hr : r ≠ 0 := by
        intro hr0
        have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 3) hr0
        exact hε_pos.ne' (by simpa [r] using hcoord)
      exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
    left
    ext k
    fin_cases k <;> simp [hx0, hx1_one, hx2_eq, hx3_zero, hx4_one, hx5]
  · have hx1_one : x 1 = 1 := by
      have hx1_ge : 1 ≤ x 1 := by
        linarith
      have hx1_le : x 1 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 1
      linarith
    have hx4_one : x 4 = 1 := by
      have hx4_ge : 1 ≤ x 4 := by
        linarith
      have hx4_le : x 4 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 4
      linarith
    have hx2_zero : x 2 = 0 := by
      by_contra hx2_ne
      have hx2_pos : 0 < x 2 := by
        exact lt_of_le_of_ne h2 (by simpa [eq_comm] using hx2_ne)
      let ε : ℝ := x 2 / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hε_le_x2 : ε ≤ x 2 := by
        dsimp [ε]
        linarith
      let r : Fin 6 → ℝ := ![(0 : ℝ), 0, ε, 0, 0, 0]
      have hminus :
          x - r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, hx1_one, hx3_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h013
        · simp [r, hx4_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simp [r, hx1_one, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx3_eq, hx4_one, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            using h345
        · simpa [r, sub_eq_add_neg] using h0
        · simpa [r, hx1_one, sub_eq_add_neg] using h1
        · simp [r, sub_eq_add_neg]
          linarith
        · simpa [r, hx3_eq, sub_eq_add_neg] using h3
        · simpa [r, hx4_one, sub_eq_add_neg] using h4
        · simpa [r, hx5, sub_eq_add_neg] using h5
      have hplus :
          x + r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [r, hx1_one, hx3_eq, add_assoc, add_left_comm, add_comm] using h013
        · simp [r, hx4_one, add_assoc, add_left_comm, add_comm]
          linarith
        · simp [r, hx1_one, hx5, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx3_eq, hx4_one, hx5, add_assoc, add_left_comm, add_comm] using h345
        · simpa [r] using h0
        · simpa [r, hx1_one] using h1
        · simp [r]
          linarith
        · simpa [r, hx3_eq] using h3
        · simpa [r, hx4_one] using h4
        · simpa [r, hx5] using h5
      have hr : r ≠ 0 := by
        intro hr0
        have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 2) hr0
        exact hε_pos.ne' (by simpa [r] using hcoord)
      exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
    left
    ext k
    fin_cases k <;> simp [hx0, hx1_one, hx2_zero, hx3_eq, hx4_one, hx5]
  · have hx2_one : x 2 = 1 := by
      have hx2_ge : 1 ≤ x 2 := by
        linarith
      have hx2_le : x 2 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 2
      linarith
    have hx3_one : x 3 = 1 := by
      have hx3_ge : 1 ≤ x 3 := by
        linarith
      have hx3_le : x 3 ≤ 1 := exercise_4_24_coordinate_le_one_of_extremePoint hx 3
      linarith
    have hx1_zero : x 1 = 0 := by
      by_contra hx1_ne
      have hx1_pos : 0 < x 1 := by
        exact lt_of_le_of_ne h1 (by simpa [eq_comm] using hx1_ne)
      let ε : ℝ := x 1 / 2
      have hε_pos : 0 < ε := by
        dsimp [ε]
        linarith
      have hε_le_x1 : ε ≤ x 1 := by
        dsimp [ε]
        linarith
      let r : Fin 6 → ℝ := ![(0 : ℝ), ε, 0, 0, 0, 0]
      have hminus :
          x - r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [r, hx3_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx2_one, hx4_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h024
        · simp [r, hx2_one, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx3_one, hx4_eq, hx5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            using h345
        · simpa [r, sub_eq_add_neg] using h0
        · simp [r, sub_eq_add_neg]
          linarith
        · simpa [r, hx2_one, sub_eq_add_neg] using h2
        · simpa [r, hx3_one, sub_eq_add_neg] using h3
        · simpa [r, hx4_eq, sub_eq_add_neg] using h4
        · simpa [r, hx5, sub_eq_add_neg] using h5
      have hplus :
          x + r ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [r, hx3_one, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx2_one, hx4_eq, add_assoc, add_left_comm, add_comm] using h024
        · simp [r, hx2_one, hx5, add_assoc, add_left_comm, add_comm]
          linarith
        · simpa [r, hx3_one, hx4_eq, hx5, add_assoc, add_left_comm, add_comm] using h345
        · simpa [r] using h0
        · simp [r]
          linarith
        · simpa [r, hx2_one] using h2
        · simpa [r, hx3_one] using h3
        · simpa [r, hx4_eq] using h4
        · simpa [r, hx5] using h5
      have hr : r ≠ 0 := by
        intro hr0
        have hcoord := congrArg (fun v : Fin 6 → ℝ ↦ v 1) hr0
        exact hε_pos.ne' (by simpa [r] using hcoord)
      exact (exercise_4_24_notExtreme_of_twoSidedPerturbation hminus hplus hr) hx
    right
    ext k
    fin_cases k <;> simp [hx0, hx1_zero, hx2_one, hx3_one, hx4_eq, hx5]


/-- Helper for Exercise 4.24: relabel the six edge coordinates by a permutation of `Fin 6`. -/
private abbrev exercise_4_24_relabel (σ : Equiv.Perm (Fin 6)) :
    (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ σ

/-- Helper for Exercise 4.24: evaluating the relabeled vector amounts to precomposing by the
chosen permutation. -/
@[simp] private lemma exercise_4_24_relabel_apply
    (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ℝ) (k : Fin 6) :
    exercise_4_24_relabel σ x k = x (σ k) := by
  rfl

/-- Helper for Exercise 4.24: package the seven explicit `0,1` edge covers as a set for transport
through coordinate relabelings. -/
private def exercise_4_24_explicitCoverSet : Set (Fin 6 → ℝ) :=
  {x |
    x = ![(1 : ℝ), 0, 0, 0, 0, 1] ∨
      x = ![(0 : ℝ), 1, 0, 0, 1, 0] ∨
      x = ![(0 : ℝ), 0, 1, 1, 0, 0] ∨
      x = ![(1 : ℝ), 1, 0, 1, 0, 0] ∨
      x = ![(1 : ℝ), 0, 1, 0, 1, 0] ∨
      x = ![(0 : ℝ), 1, 1, 0, 0, 1] ∨
      x = ![(0 : ℝ), 0, 0, 1, 1, 1]}

/-- Helper for Exercise 4.24: membership in `exercise_4_24_explicitCoverSet` is exactly the
original seven-way disjunction of explicit covers. -/
private lemma exercise_4_24_memExplicitCoverSet_iff
    {x : Fin 6 → ℝ} :
    x ∈ exercise_4_24_explicitCoverSet ↔
      x = ![(1 : ℝ), 0, 0, 0, 0, 1] ∨
        x = ![(0 : ℝ), 1, 0, 0, 1, 0] ∨
        x = ![(0 : ℝ), 0, 1, 1, 0, 0] ∨
        x = ![(1 : ℝ), 1, 0, 1, 0, 0] ∨
        x = ![(1 : ℝ), 0, 1, 0, 1, 0] ∨
        x = ![(0 : ℝ), 1, 1, 0, 0, 1] ∨
        x = ![(0 : ℝ), 0, 0, 1, 1, 1] :=
  Iff.rfl

/-- Helper for Exercise 4.24: the coordinate map `[0,2,1,4,3,5]` is injective. -/
private lemma exercise_4_24_permA_injective :
    Function.Injective (fun i : Fin 6 ↦ ![(0 : Fin 6), 2, 1, 4, 3, 5] i) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simpa using hij

/-- Helper for Exercise 4.24: the edge relabeling induced by swapping vertices `2` and `3` acts on
edge coordinates by `(1 2)(3 4)`. -/
private noncomputable def exercise_4_24_permA : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (fun i : Fin 6 ↦ ![(0 : Fin 6), 2, 1, 4, 3, 5] i)
    (Finite.injective_iff_bijective.1 exercise_4_24_permA_injective)

/-- Helper for Exercise 4.24: the coordinate map `[1,0,2,3,5,4]` is injective. -/
private lemma exercise_4_24_permB_injective :
    Function.Injective (fun i : Fin 6 ↦ ![(1 : Fin 6), 0, 2, 3, 5, 4] i) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simpa using hij

/-- Helper for Exercise 4.24: the edge relabeling induced by swapping vertices `1` and `2` acts on
edge coordinates by `(0 1)(4 5)`. -/
private noncomputable def exercise_4_24_permB : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (fun i : Fin 6 ↦ ![(1 : Fin 6), 0, 2, 3, 5, 4] i)
    (Finite.injective_iff_bijective.1 exercise_4_24_permB_injective)

/-- Helper for Exercise 4.24: the coordinate map `[0,3,4,1,2,5]` is injective. -/
private lemma exercise_4_24_permC_injective :
    Function.Injective (fun i : Fin 6 ↦ ![(0 : Fin 6), 3, 4, 1, 2, 5] i) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simpa using hij

/-- Helper for Exercise 4.24: the edge relabeling induced by swapping vertices `2` and `4` acts on
edge coordinates by `(1 3)(2 4)`. -/
private noncomputable def exercise_4_24_permC : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective
    (fun i : Fin 6 ↦ ![(0 : Fin 6), 3, 4, 1, 2, 5] i)
    (Finite.injective_iff_bijective.1 exercise_4_24_permC_injective)

/-- Helper for Exercise 4.24: a good relabeling preserves both the exercise polyhedron and the set
of explicit `0,1` covers. -/
private def exercise_4_24_goodRelabel (σ : Equiv.Perm (Fin 6)) : Prop :=
  exercise_4_24_relabel σ ''
      rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs =
    rational_matrix_polyhedron
      exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs ∧
  exercise_4_24_relabel σ '' exercise_4_24_explicitCoverSet =
    exercise_4_24_explicitCoverSet

/-- Helper for Exercise 4.24: the identity relabeling is good. -/
private lemma exercise_4_24_goodRelabel_refl :
    exercise_4_24_goodRelabel (Equiv.refl (Fin 6)) := by
  simp [exercise_4_24_goodRelabel, exercise_4_24_relabel]

/-- Helper for Exercise 4.24: the generator `(1 2)(3 4)` preserves the exercise polyhedron and
the explicit-cover set. -/
private lemma exercise_4_24_goodRelabel_permA :
    exercise_4_24_goodRelabel exercise_4_24_permA := by
  have hpoly :
      ∀ {x : Fin 6 → ℝ},
        x ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs →
          exercise_4_24_relabel exercise_4_24_permA x ∈
            rational_matrix_polyhedron
              exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
    intro x hx
    -- The generator only swaps the first two covering rows and the coordinates `(1,2)`, `(3,4)`.
    rcases (exercise_4_24_mem_rational_matrix_polyhedron_iff).1 hx with
      ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
    refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [exercise_4_24_permA, add_assoc, add_left_comm, add_comm] using h024
    · simpa [exercise_4_24_permA, add_assoc, add_left_comm, add_comm] using h013
    · simpa [exercise_4_24_permA, add_assoc, add_left_comm, add_comm] using h125
    · simpa [exercise_4_24_permA, add_assoc, add_left_comm, add_comm] using h345
    · simpa [exercise_4_24_permA] using h0
    · simpa [exercise_4_24_permA] using h2
    · simpa [exercise_4_24_permA] using h1
    · simpa [exercise_4_24_permA] using h4
    · simpa [exercise_4_24_permA] using h3
    · simpa [exercise_4_24_permA] using h5
  have hcover :
      ∀ {x : Fin 6 → ℝ}, x ∈ exercise_4_24_explicitCoverSet →
        exercise_4_24_relabel exercise_4_24_permA x ∈ exercise_4_24_explicitCoverSet := by
    intro x hx
    -- Each explicit cover is sent to another explicit cover in the same seven-element list.
    rw [exercise_4_24_memExplicitCoverSet_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by ext k <;> fin_cases k <;> rfl)
    · exact Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl)))
    · exact Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ext k <;> fin_cases k <;> rfl))))))
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hpoly hx
    · intro hy
      refine ⟨exercise_4_24_relabel exercise_4_24_permA y, hpoly hy, ?_⟩
      -- Applying the involution twice restores the original coordinate vector.
      ext k
      fin_cases k <;> simp [exercise_4_24_relabel, exercise_4_24_permA]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hcover hx
    · intro hy
      refine ⟨exercise_4_24_relabel exercise_4_24_permA y, hcover hy, ?_⟩
      -- The same involution argument brings the explicit vector back unchanged.
      ext k
      fin_cases k <;> simp [exercise_4_24_relabel, exercise_4_24_permA]

/-- Helper for Exercise 4.24: the generator `(0 1)(4 5)` preserves the exercise polyhedron and
the explicit-cover set. -/
private lemma exercise_4_24_goodRelabel_permB :
    exercise_4_24_goodRelabel exercise_4_24_permB := by
  have hpoly :
      ∀ {x : Fin 6 → ℝ},
        x ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs →
          exercise_4_24_relabel exercise_4_24_permB x ∈
            rational_matrix_polyhedron
              exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
    intro x hx
    -- This generator swaps the two edges at one endpoint and the opposite two edges.
    rcases (exercise_4_24_mem_rational_matrix_polyhedron_iff).1 hx with
      ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
    refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [exercise_4_24_permB, add_assoc, add_left_comm, add_comm] using h013
    · simpa [exercise_4_24_permB, add_assoc, add_left_comm, add_comm] using h125
    · simpa [exercise_4_24_permB, add_assoc, add_left_comm, add_comm] using h024
    · simpa [exercise_4_24_permB, add_assoc, add_left_comm, add_comm] using h345
    · simpa [exercise_4_24_permB] using h1
    · simpa [exercise_4_24_permB] using h0
    · simpa [exercise_4_24_permB] using h2
    · simpa [exercise_4_24_permB] using h3
    · simpa [exercise_4_24_permB] using h5
    · simpa [exercise_4_24_permB] using h4
  have hcover :
      ∀ {x : Fin 6 → ℝ}, x ∈ exercise_4_24_explicitCoverSet →
        exercise_4_24_relabel exercise_4_24_permB x ∈ exercise_4_24_explicitCoverSet := by
    intro x hx
    -- The seven explicit covers are stable under this edge relabeling as well.
    rw [exercise_4_24_memExplicitCoverSet_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))
    · exact Or.inl (by ext k <;> fin_cases k <;> rfl)
    · exact Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ext k <;> fin_cases k <;> rfl))))))
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hpoly hx
    · intro hy
      refine ⟨exercise_4_24_relabel exercise_4_24_permB y, hpoly hy, ?_⟩
      -- The generator is an involution on coordinates.
      ext k
      fin_cases k <;> simp [exercise_4_24_relabel, exercise_4_24_permB]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hcover hx
    · intro hy
      refine ⟨exercise_4_24_relabel exercise_4_24_permB y, hcover hy, ?_⟩
      -- The same involution transports explicit covers back to their original coordinates.
      ext k
      fin_cases k <;> simp [exercise_4_24_relabel, exercise_4_24_permB]

/-- Helper for Exercise 4.24: the generator `(1 3)(2 4)` preserves the exercise polyhedron and
the explicit-cover set. -/
private lemma exercise_4_24_goodRelabel_permC :
    exercise_4_24_goodRelabel exercise_4_24_permC := by
  have hpoly :
      ∀ {x : Fin 6 → ℝ},
        x ∈ rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs →
          exercise_4_24_relabel exercise_4_24_permC x ∈
            rational_matrix_polyhedron
              exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
    intro x hx
    -- This generator fixes the first two cover rows and swaps the last two.
    rcases (exercise_4_24_mem_rational_matrix_polyhedron_iff).1 hx with
      ⟨h013, h024, h125, h345, h0, h1, h2, h3, h4, h5⟩
    refine (exercise_4_24_mem_rational_matrix_polyhedron_iff).2 ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [exercise_4_24_permC, add_assoc, add_left_comm, add_comm] using h013
    · simpa [exercise_4_24_permC, add_assoc, add_left_comm, add_comm] using h024
    · simpa [exercise_4_24_permC, add_assoc, add_left_comm, add_comm] using h345
    · simpa [exercise_4_24_permC, add_assoc, add_left_comm, add_comm] using h125
    · simpa [exercise_4_24_permC] using h0
    · simpa [exercise_4_24_permC] using h3
    · simpa [exercise_4_24_permC] using h4
    · simpa [exercise_4_24_permC] using h1
    · simpa [exercise_4_24_permC] using h2
    · simpa [exercise_4_24_permC] using h5
  have hcover :
      ∀ {x : Fin 6 → ℝ}, x ∈ exercise_4_24_explicitCoverSet →
        exercise_4_24_relabel exercise_4_24_permC x ∈ exercise_4_24_explicitCoverSet := by
    intro x hx
    -- The explicit list is again closed because the generator comes from a vertex swap of `K₄`.
    rw [exercise_4_24_memExplicitCoverSet_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by ext k <;> fin_cases k <;> rfl)
    · exact Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl)))
    · exact Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ext k <;> fin_cases k <;> rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ext k <;> fin_cases k <;> rfl))))))
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hpoly hx
    · intro hy
      refine ⟨exercise_4_24_relabel exercise_4_24_permC y, hpoly hy, ?_⟩
      -- The coordinate relabeling is involutive.
      ext k
      fin_cases k <;> simp [exercise_4_24_relabel, exercise_4_24_permC]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hcover hx
    · intro hy
      refine ⟨exercise_4_24_relabel exercise_4_24_permC y, hcover hy, ?_⟩
      -- Explicit covers return unchanged after relabeling twice.
      ext k
      fin_cases k <;> simp [exercise_4_24_relabel, exercise_4_24_permC]

/-- Helper for Exercise 4.24: relabeling by a product of two permutations is the same as relabeling
by the second permutation and then by the first. -/
private lemma exercise_4_24_relabel_trans_image
    (σ τ : Equiv.Perm (Fin 6)) (S : Set (Fin 6 → ℝ)) :
    exercise_4_24_relabel (σ.trans τ) '' S =
      exercise_4_24_relabel σ '' (exercise_4_24_relabel τ '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Expand the composed relabeling once so the image witness is explicit.
    refine ⟨exercise_4_24_relabel τ x, ⟨x, hx, rfl⟩, ?_⟩
    ext k
    simp [exercise_4_24_relabel, Equiv.trans_apply]
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    -- Collapse the nested image witness back to the single composed relabeling.
    refine ⟨x, hx, ?_⟩
    ext k
    simp [exercise_4_24_relabel, Equiv.trans_apply]

/-- Helper for Exercise 4.24: good relabelings are closed under composition. -/
private lemma exercise_4_24_goodRelabel_trans
    {σ τ : Equiv.Perm (Fin 6)}
    (hσ : exercise_4_24_goodRelabel σ)
    (hτ : exercise_4_24_goodRelabel τ) :
    exercise_4_24_goodRelabel (σ.trans τ) := by
  constructor
  · -- Compose the two image equalities through the relabeling identity above.
    calc
      exercise_4_24_relabel (σ.trans τ) ''
          rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs =
        exercise_4_24_relabel σ ''
          (exercise_4_24_relabel τ ''
            rational_matrix_polyhedron
              exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs) := by
        simpa using
          exercise_4_24_relabel_trans_image σ τ
            (rational_matrix_polyhedron
              exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs)
      _ =
        exercise_4_24_relabel σ ''
          rational_matrix_polyhedron
            exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
        rw [hτ.1]
      _ =
        rational_matrix_polyhedron
          exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := hσ.1
  · -- The same image calculation transports the explicit cover set.
    calc
      exercise_4_24_relabel (σ.trans τ) '' exercise_4_24_explicitCoverSet =
        exercise_4_24_relabel σ '' (exercise_4_24_relabel τ '' exercise_4_24_explicitCoverSet) := by
        simpa using exercise_4_24_relabel_trans_image σ τ exercise_4_24_explicitCoverSet
      _ = exercise_4_24_relabel σ '' exercise_4_24_explicitCoverSet := by
        rw [hτ.2]
      _ = exercise_4_24_explicitCoverSet := hσ.2

/-- Helper for Exercise 4.24: every ordered pair of distinct coordinates can be relabeled to one of
the representative zero pairs `(0,1)` or `(0,5)`. -/
private lemma exercise_4_24_zeroPairRepresentativePermutation
    {i j : Fin 6} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 6), exercise_4_24_goodRelabel σ ∧
      ((σ 0 = i ∧ σ 1 = j) ∨ (σ 0 = i ∧ σ 5 = j)) := by
  -- The only remaining combinatorics is the finite table of ordered edge pairs of `K₄`.
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · refine ⟨(Equiv.refl (Fin 6)), exercise_4_24_goodRelabel_refl, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨exercise_4_24_permA, exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨exercise_4_24_permC, exercise_4_24_goodRelabel_permC, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(exercise_4_24_permA).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
        exercise_4_24_goodRelabel_permC, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨exercise_4_24_permA, exercise_4_24_goodRelabel_permA, ?_⟩
    right
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨exercise_4_24_permB, exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · exact (hij rfl).elim
  · refine ⟨(exercise_4_24_permA).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permC
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨exercise_4_24_permB, exercise_4_24_goodRelabel_permB, ?_⟩
    right
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((exercise_4_24_permA).trans exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
          exercise_4_24_goodRelabel_permC)
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((exercise_4_24_permA).trans exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · exact (hij rfl).elim
  · refine ⟨(exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
        exercise_4_24_goodRelabel_permA, ?_⟩
    right
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((exercise_4_24_permC).trans exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permC
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((exercise_4_24_permA).trans exercise_4_24_permC).trans
        exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
            exercise_4_24_goodRelabel_permC)
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(exercise_4_24_permB).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
        exercise_4_24_goodRelabel_permC, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((exercise_4_24_permB).trans exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
          exercise_4_24_goodRelabel_permC)
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(exercise_4_24_permB).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
        exercise_4_24_goodRelabel_permC, ?_⟩
    right
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · exact (hij rfl).elim
  · refine ⟨((exercise_4_24_permA).trans exercise_4_24_permB).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permC, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((exercise_4_24_permA).trans exercise_4_24_permB).trans
        exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
            exercise_4_24_goodRelabel_permB)
          exercise_4_24_goodRelabel_permC)
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((exercise_4_24_permB).trans exercise_4_24_permA).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
          exercise_4_24_goodRelabel_permA)
        exercise_4_24_goodRelabel_permC, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((exercise_4_24_permB).trans exercise_4_24_permA).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
          exercise_4_24_goodRelabel_permA)
        exercise_4_24_goodRelabel_permC, ?_⟩
    right
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((exercise_4_24_permB).trans exercise_4_24_permC).trans
        exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
            exercise_4_24_goodRelabel_permC)
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((exercise_4_24_permA).trans exercise_4_24_permB).trans
        exercise_4_24_permA).trans exercise_4_24_permC,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
            exercise_4_24_goodRelabel_permB)
          exercise_4_24_goodRelabel_permA)
        exercise_4_24_goodRelabel_permC, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · exact (hij rfl).elim
  · refine ⟨((((exercise_4_24_permA).trans exercise_4_24_permB).trans
        exercise_4_24_permC).trans exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans
            (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
              exercise_4_24_goodRelabel_permB)
            exercise_4_24_goodRelabel_permC)
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((exercise_4_24_permB).trans exercise_4_24_permA).trans
        exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
            exercise_4_24_goodRelabel_permA)
          exercise_4_24_goodRelabel_permC)
        exercise_4_24_goodRelabel_permB, ?_⟩
    right
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((exercise_4_24_permB).trans exercise_4_24_permA).trans
        exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
            exercise_4_24_goodRelabel_permA)
          exercise_4_24_goodRelabel_permC)
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((((exercise_4_24_permB).trans exercise_4_24_permA).trans
        exercise_4_24_permC).trans exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans
            (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permB
              exercise_4_24_goodRelabel_permA)
            exercise_4_24_goodRelabel_permC)
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨((((exercise_4_24_permA).trans exercise_4_24_permB).trans
        exercise_4_24_permA).trans exercise_4_24_permC).trans exercise_4_24_permB,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans
            (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
              exercise_4_24_goodRelabel_permB)
            exercise_4_24_goodRelabel_permA)
          exercise_4_24_goodRelabel_permC)
        exercise_4_24_goodRelabel_permB, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · refine ⟨(((((exercise_4_24_permA).trans exercise_4_24_permB).trans
        exercise_4_24_permA).trans exercise_4_24_permC).trans
        exercise_4_24_permB).trans exercise_4_24_permA,
      exercise_4_24_goodRelabel_trans
        (exercise_4_24_goodRelabel_trans
          (exercise_4_24_goodRelabel_trans
            (exercise_4_24_goodRelabel_trans
              (exercise_4_24_goodRelabel_trans exercise_4_24_goodRelabel_permA
                exercise_4_24_goodRelabel_permB)
              exercise_4_24_goodRelabel_permA)
            exercise_4_24_goodRelabel_permC)
          exercise_4_24_goodRelabel_permB)
        exercise_4_24_goodRelabel_permA, ?_⟩
    left
    constructor
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
    · simp [Equiv.trans_apply, exercise_4_24_permA, exercise_4_24_permB, exercise_4_24_permC]
  · exact (hij rfl).elim

/-- Helper for Exercise 4.24: once two zero coordinates are fixed, the ambient extreme point must
be one of the seven explicit `0,1` edge covers. -/
private lemma exercise_4_24_explicitCoverVector_of_twoZeroCoordinates
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ)
    {i j : Fin 6} (hij : i ≠ j) (hi : x i = 0) (hj : x j = 0) :
    x = ![(1 : ℝ), 0, 0, 0, 0, 1] ∨
      x = ![(0 : ℝ), 1, 0, 0, 1, 0] ∨
      x = ![(0 : ℝ), 0, 1, 1, 0, 0] ∨
      x = ![(1 : ℝ), 1, 0, 1, 0, 0] ∨
      x = ![(1 : ℝ), 0, 1, 0, 1, 0] ∨
      x = ![(0 : ℝ), 1, 1, 0, 0, 1] ∨
      x = ![(0 : ℝ), 0, 0, 1, 1, 1] := by
  -- Route correction: replace the dead active-system classifier with a relabeling reduction to the
  -- two representative zero pairs `(0,1)` and `(0,5)`.
  obtain ⟨σ, hσ, hrep⟩ := exercise_4_24_zeroPairRepresentativePermutation hij
  let y : Fin 6 → ℝ := exercise_4_24_relabel σ x
  have hyImage :
      y ∈ exercise_4_24_relabel σ ''
        (rational_matrix_polyhedron
          exercise_4_24_constraint_matrix
          exercise_4_24_constraint_rhs).extremePoints ℝ := by
    exact ⟨x, hx, rfl⟩
  have hyExtreme :
      y ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ := by
    -- Transport the vertex fact along the good relabeling.
    rw [image_extremePoints, hσ.1] at hyImage
    exact hyImage
  have hyExplicit : y ∈ exercise_4_24_explicitCoverSet := by
    rw [exercise_4_24_memExplicitCoverSet_iff]
    rcases hrep with ⟨hσ0, hσ1⟩ | ⟨hσ0, hσ5⟩
    · -- The adjacent representative `(0,1)` is already classified.
      have hy0 : y 0 = 0 := by
        simpa [y, exercise_4_24_relabel, hσ0] using hi
      have hy1 : y 1 = 0 := by
        simpa [y, exercise_4_24_relabel, hσ1] using hj
      rcases exercise_4_24_adjacentPair01_cases hyExtreme hy0 hy1 with hy3 | hy7
      · exact Or.inr (Or.inr (Or.inl hy3))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hy7)))))
    · -- The opposite representative `(0,5)` is handled by the second branch lemma.
      have hy0 : y 0 = 0 := by
        simpa [y, exercise_4_24_relabel, hσ0] using hi
      have hy5 : y 5 = 0 := by
        simpa [y, exercise_4_24_relabel, hσ5] using hj
      rcases exercise_4_24_oppositePair05_cases hyExtreme hy0 hy5 with hy2 | hy3
      · exact Or.inr (Or.inl hy2)
      · exact Or.inr (Or.inr (Or.inl hy3))
  have hyImageCover :
      y ∈ exercise_4_24_relabel σ '' exercise_4_24_explicitCoverSet := by
    -- Rewrite the explicit-cover membership through the preserved image.
    rw [hσ.2]
    exact hyExplicit
  rcases hyImageCover with ⟨z, hz, hzEq⟩
  have hzx : z = x := by
    -- Injectivity of the relabeling map transports the representative cover back to `x`.
    apply (exercise_4_24_relabel σ).injective
    simpa [y] using hzEq
  rw [hzx] at hz
  exact (exercise_4_24_memExplicitCoverSet_iff).1 hz

/-- Helper for Exercise 4.24: once a minimal face collapses to a singleton, the remaining task is
to classify the ambient vertex among the seven `0,1` edge covers of `K₄`. -/
private lemma exercise_4_24_rationalVertex_mem_integerVectors
    {x : Fin 6 → ℝ}
    (hx :
      x ∈ (rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs).extremePoints ℝ) :
    x ∈ integerVectors 6 := by
  -- Route correction: classify the ambient vertex directly from its zero pair instead of pushing
  -- through the broken active-system transport.
  obtain ⟨i, j, hij, hix, hjx⟩ :=
    exercise_4_24_extremePoint_has_two_zero_coordinates hx
  exact exercise_4_24_explicitCoverVector_mem_integerVectors
    (exercise_4_24_explicitCoverVector_of_twoZeroCoordinates hx hij hix hjx)

/-- Exercise 4.24 (1): the polyhedron `P = {x ≥ 0 : A x ≥ 1}` defined by the displayed matrix is
integral. -/
theorem exercise_4_24_polyhedron_integral :
    is_integral exercise_4_24_polyhedron := by
  -- Route correction: avoid the broken minimal-face import chain and instead pass through the
  -- exposed maximizer face from Theorem 4.1(2).
  rw [exercise_4_24_polyhedron_eq_rational_matrix_polyhedron]
  refine
    (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
      (P := rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs)
      (hP := by
        refine ⟨4 + 6, exercise_4_24_constraint_matrix, exercise_4_24_constraint_rhs, ?_⟩
        rfl)).2 ?_
  intro c z hGreatest
  rcases hGreatest.1 with ⟨x0, hx0P, hx0_obj⟩
  let P :=
    rational_matrix_polyhedron
      exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs
  let F := face_set P c z
  have hP_eq :
      P = nonnegative_matrix_polyhedron (-exercise_4_24_matrix) (-exercise_4_24_rhs) := by
    calc
      P = exercise_4_24_polyhedron := by
        simpa [P] using exercise_4_24_polyhedron_eq_rational_matrix_polyhedron.symm
      _ = nonnegative_matrix_polyhedron (-exercise_4_24_matrix) (-exercise_4_24_rhs) :=
        exercise_4_24_polyhedron_eq_nonnegative_matrix_polyhedron
  have hF_polyhedron : is_polyhedron F := by
    simpa [F, hP_eq] using
      face_set_nonnegative_matrix_polyhedron_is_polyhedron
        (-exercise_4_24_matrix) (-exercise_4_24_rhs) c z
  have hvalid : is_valid_inequality P c z := by
    intro y hyP
    exact hGreatest.2 ⟨y, hyP, rfl⟩
  have hx0F : x0 ∈ F := by
    rw [mem_face_set_iff]
    exact ⟨hx0P, hx0_obj⟩
  have hF_nonempty : F.Nonempty := ⟨x0, hx0F⟩
  have hF_exposed : IsExposed ℝ P F := by
    simpa [F] using isExposed_face_set_of_valid_inequality hvalid
  have hF_lineality : linealitySpace F = ({0} : Set (Fin 6 → ℝ)) := by
    ext r
    constructor
    · intro hr
      have hr_zero :
          r = 0 := by
        exact
          eq_zero_of_mem_linealitySpace_of_subset_exercise_4_24_polyhedron
            (F := F)
            (hF_subset := by
              intro y hy
              simpa [P, exercise_4_24_polyhedron_eq_rational_matrix_polyhedron] using
                (mem_face_set_iff.mp hy).1)
            hr
            hx0F
      simpa [hr_zero]
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      exact zero_mem_linealitySpace
  have hF_extreme_nonempty :
      (F.extremePoints ℝ).Nonempty := by
    exact
      (polyhedron_extremePoints_nonempty_iff_linealitySpace_eq_zero
        hF_polyhedron hF_nonempty).2 hF_lineality
  rcases hF_extreme_nonempty with ⟨x, hx_extreme_F⟩
  have hx_extreme_P : x ∈ P.extremePoints ℝ := by
    exact hF_exposed.isExtreme.extremePoints_subset_extremePoints hx_extreme_F
  have hx_int : x ∈ integerVectors 6 :=
    exercise_4_24_rationalVertex_mem_integerVectors hx_extreme_P
  have hxF : x ∈ F := extremePoints_subset hx_extreme_F
  rw [mem_face_set_iff] at hxF
  exact ⟨x, ⟨hxF.1, hx_int⟩, hxF.2⟩

/-- Helper for Exercise 4.24: every integral feasible dual point for the objective `c = -𝟙`
has dual value at least `-1`. This is the arithmetic contradiction against the fractional witness
with value `-2`. -/
lemma exercise_4_24_integral_dual_objective_ge_negOne
    {y : Fin 10 → ℝ}
    (hy : y ∈ rational_dual_feasible_region
      exercise_4_24_constraint_matrix exercise_4_24_negOnesObjective)
    (hyInt : y ∈ integerVectors 10) :
    y ⬝ᵥ (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ)) ≥ -1 := by
  -- Convert the integral feasible point to integer coordinates and let Presburger arithmetic
  -- prove the source contradiction `y₀ + y₁ + y₂ + y₃ ≤ 1`.
  rw [mem_exercise_4_24_dual_feasible_region_negOnes_iff] at hy
  rcases hy with ⟨hyNonneg, h01, h02, h12, h03, h13, h23⟩
  rcases mem_integerVectors_iff.mp hyInt with ⟨z, rfl⟩
  have hzNonneg : ∀ i : Fin 10, 0 ≤ z i := by
    intro i
    have hi : (0 : ℝ) ≤ z i := by simpa using hyNonneg i
    exact_mod_cast hi
  have hz01 : z 0 + z 1 + z 4 = 1 := by
    have h01' : ((z 0 : ℝ) + z 1 + z 4) = 1 := by simpa using h01
    exact_mod_cast h01'
  have hz02 : z 0 + z 2 + z 5 = 1 := by
    have h02' : ((z 0 : ℝ) + z 2 + z 5) = 1 := by simpa using h02
    exact_mod_cast h02'
  have hz12 : z 1 + z 2 + z 6 = 1 := by
    have h12' : ((z 1 : ℝ) + z 2 + z 6) = 1 := by simpa using h12
    exact_mod_cast h12'
  have hz03 : z 0 + z 3 + z 7 = 1 := by
    have h03' : ((z 0 : ℝ) + z 3 + z 7) = 1 := by simpa using h03
    exact_mod_cast h03'
  have hz13 : z 1 + z 3 + z 8 = 1 := by
    have h13' : ((z 1 : ℝ) + z 3 + z 8) = 1 := by simpa using h13
    exact_mod_cast h13'
  have hz23 : z 2 + z 3 + z 9 = 1 := by
    have h23' : ((z 2 : ℝ) + z 3 + z 9) = 1 := by simpa using h23
    exact_mod_cast h23'
  have h01le : z 0 + z 1 ≤ 1 := by linarith [hz01, hzNonneg 4]
  have h02le : z 0 + z 2 ≤ 1 := by linarith [hz02, hzNonneg 5]
  have h12le : z 1 + z 2 ≤ 1 := by linarith [hz12, hzNonneg 6]
  have h03le : z 0 + z 3 ≤ 1 := by linarith [hz03, hzNonneg 7]
  have h13le : z 1 + z 3 ≤ 1 := by linarith [hz13, hzNonneg 8]
  have h23le : z 2 + z 3 ≤ 1 := by linarith [hz23, hzNonneg 9]
  have hzsum : z 0 + z 1 + z 2 + z 3 ≤ 1 := by
    omega
  -- The rhs normalizer turns the objective into the negative of that four-term sum.
  rw [exercise_4_24_rhs_dot]
  have hsum_real : ((z 0 : ℝ) + z 1 + z 2 + z 3) ≤ 1 := by
    exact_mod_cast hzsum
  have hneg : -((z 0 : ℝ) + z 1 + z 2 + z 3) ≥ -1 := by
    linarith
  simpa using hneg

/-- Second claim of Exercise 4.24: the canonical `≤`-presentation of the system `x ≥ 0`,
`A x ≥ 1` defined by the displayed matrix is not totally dual integral. -/
theorem exercise_4_24_system_not_tdi :
    ¬ totally_dual_integral exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
  -- Use the integral objective `c = -𝟙`, a primal optimum of value `-2`, and a fractional dual
  -- feasible point of value `-2` to contradict the existence of an integral optimal dual witness.
  rw [totally_dual_integral_iff]
  intro hTDI
  let xStar : Fin 6 → ℝ := ![(1 : ℝ), 0, 0, 0, 0, 1]
  have hxStar_mem :
      xStar ∈ rational_matrix_polyhedron
        exercise_4_24_constraint_matrix exercise_4_24_constraint_rhs := by
    rw [← exercise_4_24_polyhedron_eq_rational_matrix_polyhedron]
    rw [mem_exercise_4_24_polyhedron_iff, exercise_4_24_matrix_mulVec]
    constructor
    · intro i
      fin_cases i <;> simp [xStar, exercise_4_24_rhs]
    · intro i
      fin_cases i <;> simp [xStar]
  have hxStar_value :
      ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ xStar) = -2 := by
    calc
      ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ xStar) =
          -(xStar 0 + xStar 1 + xStar 2 + xStar 3 + xStar 4 + xStar 5) := by
        simp [exercise_4_24_negOnesObjective, dotProduct, Fin.sum_univ_six,
          add_assoc, add_comm]
      _ = -2 := by
        change -((1 : ℝ) + 0 + 0 + 0 + 0 + 1) = (-2 : ℝ)
        norm_num
  have hPrimalFinite :
      rational_primal_has_finite_optimum
        exercise_4_24_constraint_matrix
        exercise_4_24_constraint_rhs
        exercise_4_24_negOnesObjective := by
    rw [rational_primal_has_finite_optimum_iff]
    refine ⟨xStar, hxStar_mem, ?_⟩
    constructor
    · refine ⟨xStar, hxStar_mem, ?_⟩
      rfl
    · intro w hw
      rcases hw with ⟨x, hx, rfl⟩
      have hx_le : ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ x) ≤ -2 :=
        exercise_4_24_primal_objective_le_negTwo hx
      calc
        ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ x) ≤ -2 := hx_le
        _ = ((Int.cast ∘ exercise_4_24_negOnesObjective) ⬝ᵥ xStar) := by
          symm
          exact hxStar_value
  have hDual :=
    hTDI exercise_4_24_negOnesObjective hPrimalFinite
  rw [rational_dual_has_integral_optimal_solution_iff] at hDual
  rcases hDual with ⟨yStar, hyStar, hyStarInt, hyStarLeast⟩
  let yFrac : Fin 10 → ℝ := ![(1 / 2 : ℝ), 1 / 2, 1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0]
  have hyFrac_mem :
      yFrac ∈ rational_dual_feasible_region
        exercise_4_24_constraint_matrix exercise_4_24_negOnesObjective := by
    rw [mem_exercise_4_24_dual_feasible_region_negOnes_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [yFrac]
    · change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num
    · change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num
    · change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num
    · change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num
    · change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num
    · change (1 / 2 : ℝ) + 1 / 2 + 0 = 1
      norm_num
  have hyFrac_value :
      yFrac ⬝ᵥ (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ)) = -2 := by
    calc
      yFrac ⬝ᵥ (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ)) =
          -(yFrac 0 + yFrac 1 + yFrac 2 + yFrac 3) := by
        rw [exercise_4_24_rhs_dot]
      _ = -2 := by
        change -((1 / 2 : ℝ) + 1 / 2 + 1 / 2 + 1 / 2) = (-2 : ℝ)
        norm_num
  have hyStar_le_negTwo :
      yStar ⬝ᵥ (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ)) ≤ -2 := by
    exact hyStarLeast.2 ⟨yFrac, hyFrac_mem, hyFrac_value⟩
  have hyStar_ge_negOne :
      -1 ≤ yStar ⬝ᵥ (fun i ↦ (exercise_4_24_constraint_rhs i : ℝ)) :=
    exercise_4_24_integral_dual_objective_ge_negOne hyStar hyStarInt
  linarith
