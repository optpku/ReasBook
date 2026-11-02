import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this session, so this file uses a self-contained formulation of the Example 8.14
-- block patterns and Dantzig-Wolfe aggregation maps.

section Example814

/-- The real `0,1` value corresponding to a Boolean entry. -/
def bool_entry (b : Bool) : ℝ :=
  if b then 1 else 0

/-- `bool_entry false` is `0`. -/
@[simp] theorem bool_entry_false : bool_entry false = 0 := by
  simp [bool_entry]

/-- `bool_entry true` is `1`. -/
@[simp] theorem bool_entry_true : bool_entry true = 1 := by
  simp [bool_entry]

/-- `bool_entry` only takes the values `0` and `1`. -/
theorem bool_entry_eq_zero_or_one (b : Bool) : bool_entry b = 0 ∨ bool_entry b = 1 := by
  cases b <;> simp

/-- `bool_entry` is nonnegative. -/
theorem bool_entry_nonneg (b : Bool) : 0 ≤ bool_entry b := by
  cases b <;> simp

/-- `bool_entry` is bounded above by `1`. -/
theorem bool_entry_le_one (b : Bool) : bool_entry b ≤ 1 := by
  cases b <;> simp

/-- The block pattern family `Q_j` from the generalized assignment problem of Example 8.14,
viewed as the finite family of binary vectors satisfying the `j`th knapsack inequality. -/
noncomputable def generalized_assignment_block_patterns {m n : ℕ}
    (t : Fin m → Fin n → ℝ) (T : Fin n → ℝ) (j : Fin n) : Finset (Fin m → Bool) :=
  Finset.univ.filter (fun v ↦ ∑ i, t i j * bool_entry (v i) ≤ T j)

/-- Membership in `generalized_assignment_block_patterns t T j` is exactly the displayed
`0,1` knapsack inequality for the `j`th block. -/
theorem mem_generalized_assignment_block_patterns_iff {m n : ℕ}
    {t : Fin m → Fin n → ℝ} {T : Fin n → ℝ} {j : Fin n} {v : Fin m → Bool} :
    v ∈ generalized_assignment_block_patterns t T j ↔
      ∑ i, t i j * bool_entry (v i) ≤ T j := by
  simp [generalized_assignment_block_patterns]

/-- The original linear-programming relaxation of the generalized assignment problem:
each block satisfies its capacity inequality, each assignment variable lies in `[0,1]`,
and the assignment constraints `∑_j x_ij ≤ 1` hold. -/
def generalized_assignment_lp_feasible {m n : ℕ}
    (t : Fin m → Fin n → ℝ) (T : Fin n → ℝ) (x : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧
    (∀ j, ∑ i, t i j * x i j ≤ T j) ∧
    (∀ i, ∑ j, x i j ≤ 1)

/-- `generalized_assignment_lp_feasible` unfolds to the three displayed families of inequalities
for the original LP relaxation. -/
theorem generalized_assignment_lp_feasible_iff {m n : ℕ}
    {t : Fin m → Fin n → ℝ} {T : Fin n → ℝ} {x : Fin m → Fin n → ℝ} :
    generalized_assignment_lp_feasible t T x ↔
      (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧
        (∀ j, ∑ i, t i j * x i j ≤ T j) ∧
        (∀ i, ∑ j, x i j ≤ 1) :=
  Iff.rfl

/-- The point `x` in the original variables induced by a Dantzig-Wolfe family
`λ^j_v` over the block pattern sets `Q_j`. -/
def generalized_assignment_dw_point {m n : ℕ}
    (Q : Fin n → Finset (Fin m → Bool))
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ Finset.sum (Q j) (fun v ↦ bool_entry (v i) * lam j v)

/-- `generalized_assignment_dw_point` evaluates to the expected convex-combination formula
`x_ij = ∑_{v ∈ Q_j} v_i λ^j_v`. -/
@[simp] theorem generalized_assignment_dw_point_apply {m n : ℕ}
    (Q : Fin n → Finset (Fin m → Bool))
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ) (i : Fin m) (j : Fin n) :
    generalized_assignment_dw_point Q lam i j =
      Finset.sum (Q j) (fun v ↦ bool_entry (v i) * lam j v) := rfl

/-- Feasibility for a Dantzig-Wolfe master problem indexed by a family of binary-pattern sets
`Q_j`: coefficients are nonnegative on the chosen columns, the convexity equations
`∑_{v ∈ Q_j} λ^j_v = 1` hold for each block, and the linking inequalities
`∑_j x_ij ≤ 1` hold for the projected point. -/
def generalized_assignment_master_feasible_on {m n : ℕ}
    (Q : Fin n → Finset (Fin m → Bool))
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ) : Prop :=
  (∀ j v, v ∈ Q j → 0 ≤ lam j v) ∧
    (∀ i, ∑ j, generalized_assignment_dw_point Q lam i j ≤ 1) ∧
    (∀ j, ∑ v ∈ Q j, lam j v = 1)

/-- `generalized_assignment_master_feasible_on Q lam` unfolds to nonnegativity on the selected
columns, the linking inequalities, and the block convexity equations. -/
theorem generalized_assignment_master_feasible_on_iff {m n : ℕ}
    {Q : Fin n → Finset (Fin m → Bool)} {lam : (j : Fin n) → (Fin m → Bool) → ℝ} :
    generalized_assignment_master_feasible_on Q lam ↔
      (∀ j v, v ∈ Q j → 0 ≤ lam j v) ∧
        (∀ i, ∑ j, generalized_assignment_dw_point Q lam i j ≤ 1) ∧
        (∀ j, ∑ v ∈ Q j, lam j v = 1) :=
  Iff.rfl

/-- Helper for Example 8.14: nonnegative master weights give a nonnegative projected
assignment coordinate. -/
lemma generalized_assignment_dw_point_nonneg {m n : ℕ}
    (Q : Fin n → Finset (Fin m → Bool))
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ)
    (h_nonneg : ∀ j v, v ∈ Q j → 0 ≤ lam j v) (i : Fin m) (j : Fin n) :
    0 ≤ generalized_assignment_dw_point Q lam i j := by
  -- Each selected block pattern contributes a nonnegative weighted Boolean entry.
  simp only [generalized_assignment_dw_point]
  refine Finset.sum_nonneg ?_
  intro v hv
  exact mul_nonneg (bool_entry_nonneg (v i)) (h_nonneg j v hv)

/-- Helper for Example 8.14: each projected coordinate is bounded by the total mass assigned
to its block. -/
lemma generalized_assignment_dw_point_le_block_mass {m n : ℕ}
    (Q : Fin n → Finset (Fin m → Bool))
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ)
    (h_nonneg : ∀ j v, v ∈ Q j → 0 ≤ lam j v) (i : Fin m) (j : Fin n) :
    generalized_assignment_dw_point Q lam i j ≤ Finset.sum (Q j) (fun v ↦ lam j v) := by
  -- Bound each Boolean coefficient by `1` before summing the selected columns.
  simp only [generalized_assignment_dw_point]
  refine Finset.sum_le_sum ?_
  intro v hv
  calc
    bool_entry (v i) * lam j v ≤ 1 * lam j v := by
      exact mul_le_mul_of_nonneg_right (bool_entry_le_one (v i)) (h_nonneg j v hv)
    _ = lam j v := by ring

/-- Helper for Example 8.14: a convex combination of feasible block patterns satisfies the
corresponding block-capacity inequality. -/
lemma generalized_assignment_dw_block_capacity {m n : ℕ}
    (t : Fin m → Fin n → ℝ) (T : Fin n → ℝ)
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ) (j : Fin n)
    (h_nonneg :
      ∀ v, v ∈ generalized_assignment_block_patterns t T j → 0 ≤ lam j v)
    (h_convex :
      Finset.sum (generalized_assignment_block_patterns t T j) (fun v ↦ lam j v) = 1) :
    ∑ i, t i j *
        generalized_assignment_dw_point (generalized_assignment_block_patterns t T) lam i j ≤
      T j := by
  -- First commute the double sum so the proof can use the block inequalities pattern by pattern.
  have hswap :
      Finset.sum Finset.univ
        (fun i ↦ Finset.sum (generalized_assignment_block_patterns t T j)
          (fun v ↦ t i j * (bool_entry (v i) * lam j v))) =
        Finset.sum (generalized_assignment_block_patterns t T j)
          (fun v ↦ Finset.sum Finset.univ
            (fun i ↦ t i j * (bool_entry (v i) * lam j v))) := by
    simpa using
      ((Finset.sum_comm :
        Finset.sum (generalized_assignment_block_patterns t T j)
          (fun v ↦ Finset.sum (Finset.univ : Finset (Fin m))
            (fun i ↦ t i j * (bool_entry (v i) * lam j v))) =
          Finset.sum (Finset.univ : Finset (Fin m))
            (fun i ↦ Finset.sum (generalized_assignment_block_patterns t T j)
              (fun v ↦ t i j * (bool_entry (v i) * lam j v)))).symm)
  calc
    ∑ i, t i j *
        generalized_assignment_dw_point (generalized_assignment_block_patterns t T) lam i j
      = Finset.sum Finset.univ
          (fun i ↦ Finset.sum (generalized_assignment_block_patterns t T j)
            (fun v ↦ t i j * (bool_entry (v i) * lam j v))) := by
            -- Expand the projection map and distribute the block coefficient across the sum.
            simp only [generalized_assignment_dw_point]
            simp_rw [Finset.mul_sum]
    _ = Finset.sum (generalized_assignment_block_patterns t T j)
          (fun v ↦ Finset.sum Finset.univ
            (fun i ↦ t i j * (bool_entry (v i) * lam j v))) := hswap
    _ = Finset.sum (generalized_assignment_block_patterns t T j)
          (fun v ↦ lam j v * (∑ i, t i j * bool_entry (v i))) := by
            -- Normalize each inner load so the weight `lam j v` factors out cleanly.
            refine Finset.sum_congr rfl ?_
            intro v hv
            calc
              ∑ i, t i j * (bool_entry (v i) * lam j v)
                = ∑ i, lam j v * (t i j * bool_entry (v i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
              _ = lam j v * (∑ i, t i j * bool_entry (v i)) := by
                    exact
                      (Finset.mul_sum Finset.univ
                        (fun i ↦ t i j * bool_entry (v i)) (lam j v)).symm
    _ ≤ Finset.sum (generalized_assignment_block_patterns t T j) (fun v ↦ lam j v * T j) := by
          -- Apply the knapsack inequality to each feasible pattern and preserve it by the
          -- nonnegative weight `lam j v`.
          refine Finset.sum_le_sum ?_
          intro v hv
          exact mul_le_mul_of_nonneg_left
            ((mem_generalized_assignment_block_patterns_iff).mp hv) (h_nonneg v hv)
    _ =
        (Finset.sum (generalized_assignment_block_patterns t T j) (fun v ↦ lam j v)) * T j := by
          rw [← Finset.sum_mul]
    _ = T j := by
          simp [h_convex]

/-- The aggregated variables `λ_v := ∑_j λ^j_v` used in the identical-block special case of
Example 8.14. -/
def identical_block_aggregate_lambda {m p : ℕ}
    (lam : Fin p → (Fin m → Bool) → ℝ) : (Fin m → Bool) → ℝ :=
  fun v ↦ ∑ j, lam j v

/-- `identical_block_aggregate_lambda` is computed by summing the block variables indexed by the
same binary pattern. -/
@[simp] theorem identical_block_aggregate_lambda_apply {m p : ℕ}
    (lam : Fin p → (Fin m → Bool) → ℝ) (v : Fin m → Bool) :
    identical_block_aggregate_lambda lam v = ∑ j, lam j v := rfl

/-- The `j`th block family `Q_j` in Example 8.14 is exactly the finite `0,1` knapsack family
defined by the inequality `∑_i t_ij v_i ≤ T_j`. -/
theorem example_8_14_block_patterns_are_knapsack {m n : ℕ}
    (t : Fin m → Fin n → ℝ) (T : Fin n → ℝ) (j : Fin n) {v : Fin m → Bool} :
    v ∈ generalized_assignment_block_patterns t T j ↔
      ∑ i, t i j * bool_entry (v i) ≤ T j := by
  simpa using
    (mem_generalized_assignment_block_patterns_iff :
      v ∈ generalized_assignment_block_patterns t T j ↔
        ∑ i, t i j * bool_entry (v i) ≤ T j)

/-- Example 8.14 (2). A Dantzig-Wolfe feasible family `λ^j_v` for the generalized assignment
blocks projects to a feasible point of the original linear-programming relaxation. -/
theorem example_8_14_dw_projects_to_lp_relaxation {m n : ℕ}
    (t : Fin m → Fin n → ℝ) (T : Fin n → ℝ)
    (lam : (j : Fin n) → (Fin m → Bool) → ℝ)
    (hmaster :
      generalized_assignment_master_feasible_on
        (generalized_assignment_block_patterns t T) lam) :
    generalized_assignment_lp_feasible t T
      (generalized_assignment_dw_point (generalized_assignment_block_patterns t T) lam) := by
  -- Unpack the master problem feasibility into the three ingredients used by the LP proof.
  rcases (generalized_assignment_master_feasible_on_iff.mp hmaster) with
    ⟨h_nonneg, h_link, h_convex⟩
  refine (generalized_assignment_lp_feasible_iff).2 ?_
  constructor
  · intro i j
    constructor
    · -- The projected coordinate is a sum of nonnegative weighted Boolean entries.
      exact
        generalized_assignment_dw_point_nonneg
          (generalized_assignment_block_patterns t T) lam h_nonneg i j
    · -- The projected coordinate is at most the block mass, and each block mass is `1`.
      simpa [h_convex j] using
        generalized_assignment_dw_point_le_block_mass
          (generalized_assignment_block_patterns t T) lam h_nonneg i j
  constructor
  · intro j
    -- Each block load is a convex combination of feasible pattern loads.
    exact generalized_assignment_dw_block_capacity t T lam j (h_nonneg j) (h_convex j)
  · -- The linking inequalities are already part of the master feasibility data.
    exact h_link

/-- In Example 8.14, when all blocks are identical and `λ_v = ∑_j λ^j_v`, the objective
`∑_j ∑_{v ∈ Q} (cv) λ^j_v` simplifies to `∑_{v ∈ Q} (cv) λ_v`. -/
theorem example_8_14_identical_blocks_objective {m p : ℕ}
    (Q : Finset (Fin m → Bool)) (c : Fin m → ℝ)
    (lam : Fin p → (Fin m → Bool) → ℝ) :
    Finset.sum Finset.univ
      (fun j ↦ Finset.sum Q (fun v ↦ (∑ i, c i * bool_entry (v i)) * lam j v)) =
      Finset.sum Q
        (fun v ↦ (∑ i, c i * bool_entry (v i)) * identical_block_aggregate_lambda lam v) := by
  simp only [identical_block_aggregate_lambda, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- In Example 8.14, under identical blocks, the coupling constraints
`∑_j ∑_{v ∈ Q} (Dv) λ^j_v ≤ d` are equivalent to
`∑_{v ∈ Q} (Dv) λ_v ≤ d` after aggregation. -/
theorem example_8_14_identical_blocks_constraints {m p q : ℕ}
    (Q : Finset (Fin m → Bool)) (D : Matrix (Fin q) (Fin m) ℝ) (d : Fin q → ℝ)
    (lam : Fin p → (Fin m → Bool) → ℝ) :
    (∀ k, Finset.sum Finset.univ
      (fun j ↦ Finset.sum Q (fun v ↦ (∑ i, D k i * bool_entry (v i)) * lam j v)) ≤ d k) ↔
      ∀ k, Finset.sum Q
        (fun v ↦ (∑ i, D k i * bool_entry (v i)) * identical_block_aggregate_lambda lam v) ≤
          d k := by
  constructor
  · intro h k
    rw [← example_8_14_identical_blocks_objective Q (fun i ↦ D k i) lam]
    exact h k
  · intro h k
    rw [example_8_14_identical_blocks_objective Q (fun i ↦ D k i) lam]
    exact h k

/-- In Example 8.14, if each block satisfies `∑_{v ∈ Q} λ^j_v = 1`, then the aggregated
variables satisfy `∑_{v ∈ Q} λ_v = p`. -/
theorem example_8_14_identical_blocks_total_mass {m p : ℕ}
    (Q : Finset (Fin m → Bool)) (lam : Fin p → (Fin m → Bool) → ℝ)
    (h_block_sum : ∀ j, Finset.sum Q (fun v ↦ lam j v) = 1) :
    Finset.sum Q (fun v ↦ identical_block_aggregate_lambda lam v) = (p : ℝ) := by
  simp only [identical_block_aggregate_lambda]
  rw [Finset.sum_comm]
  simp [h_block_sum]

end Example814
