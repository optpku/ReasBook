/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Notation
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_proposition_8_1

open scoped IntegerVectorNotation Matrix

section Exercise84

/-- The continuous base set `{(x₁, x₂) ∈ ℝ₊² : -x₁ + x₂ ≤ -1}` underlying Exercise 8.4. -/
def exercise_8_4_base_set : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ -x 0 + x 1 ≤ (-1 : ℝ)}

/-- Membership in `exercise_8_4_base_set` means nonnegativity together with
`-x₁ + x₂ ≤ -1`. -/
theorem mem_exercise_8_4_base_set_iff
    (x : Fin 2 → ℝ) :
    x ∈ exercise_8_4_base_set ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ -x 0 + x 1 ≤ (-1 : ℝ) :=
  Iff.rfl

/-- The source set `Q = {(x₁, x₂) ∈ ℤ₊² : -x₁ + x₂ ≤ -1}` used for the Exercise 8.4 Lagrangian
relaxation, expressed through the canonical Chapter 4 lattice owner `ℤ^2`. -/
def exercise_8_4_Q : Set (Fin 2 → ℝ) :=
  exercise_8_4_base_set ∩ ℤ^2

/-- Membership in `exercise_8_4_Q` means satisfying the continuous base inequalities and the
canonical Chapter 4 integrality condition `x ∈ ℤ^2`. -/
theorem mem_exercise_8_4_Q_iff
    (x : Fin 2 → ℝ) :
    x ∈ exercise_8_4_Q ↔
      x ∈ exercise_8_4_base_set ∧ x ∈ ℤ^2 :=
  Iff.rfl

/-- The objective coefficients `c = (1, 1)` for Exercise 8.4. -/
def exercise_8_4_objective_coeffs : Fin 2 → ℝ :=
  ![(1 : ℝ), 1]

/-- The single relaxed constraint row `A₁ = [1, -1]`. -/
def exercise_8_4_constraint_matrix : Matrix (Fin 1) (Fin 2) ℝ :=
  !![(1 : ℝ), -1]

/-- The right-hand side `b¹ = (-1)`. -/
def exercise_8_4_constraint_rhs : Fin 1 → ℝ :=
  ![(-1 : ℝ)]

/-- The Exercise 8.4 Lagrangian-relaxation value `z_LR(λ)`, expressed as the canonical one-row
specialization of Proposition 8.1's `lagrangian_relaxation_value`. The codomain `EReal` records
both infeasibility and unbounded-above behavior, although only `⊤` occurs in this exercise. -/
noncomputable abbrev exercise_8_4_lagrangian_relaxation_value (lam : ℝ) : EReal :=
  lagrangian_relaxation_value exercise_8_4_constraint_matrix exercise_8_4_constraint_rhs
    exercise_8_4_objective_coeffs exercise_8_4_Q ![lam]

/-- `exercise_8_4_lagrangian_relaxation_value lam` unfolds to the supremum of the penalized
objective over `exercise_8_4_Q`. -/
theorem exercise_8_4_lagrangian_relaxation_value_eq_sSup
    (lam : ℝ) :
    exercise_8_4_lagrangian_relaxation_value lam =
      sSup
        ((fun x : Fin 2 → ℝ ↦
            ((exercise_8_4_objective_coeffs ⬝ᵥ x +
                ![lam] ⬝ᵥ
                  (exercise_8_4_constraint_rhs - exercise_8_4_constraint_matrix *ᵥ x) : ℝ) :
              EReal)) '' exercise_8_4_Q) :=
  rfl

/-- The Exercise 8.4 Lagrangian dual bound `z_LD = inf_{λ ≥ 0} z_LR(λ)`. -/
noncomputable def exercise_8_4_lagrangian_dual_value : EReal :=
  sInf
    ((fun lam : ℝ ↦ exercise_8_4_lagrangian_relaxation_value lam) '' Set.Ici (0 : ℝ))

/-- `exercise_8_4_lagrangian_dual_value` unfolds to the infimum of the Exercise 8.4
Lagrangian-relaxation values over all nonnegative scalars `λ`. -/
theorem exercise_8_4_lagrangian_dual_value_eq_sInf :
    exercise_8_4_lagrangian_dual_value =
      sInf
        ((fun lam : ℝ ↦ exercise_8_4_lagrangian_relaxation_value lam) ''
          Set.Ici (0 : ℝ)) :=
  rfl

/-- Helper for Exercise 8.4: the ray point `![(N + 1 : ℝ), N]` lies in `Q`. -/
private lemma exercise_8_4_rayPoint_mem_Q
    (N : ℕ) :
    ![(N + 1 : ℝ), N] ∈ exercise_8_4_Q := by
  -- Check the continuous inequalities and the Chapter 4 integrality condition separately.
  rw [mem_exercise_8_4_Q_iff]
  constructor
  · rw [mem_exercise_8_4_base_set_iff]
    constructor
    · have hN : (0 : ℝ) ≤ N := by
        exact_mod_cast Nat.zero_le N
      simpa using (show (0 : ℝ) ≤ (N : ℝ) + 1 by linarith)
    constructor
    · simp
    · norm_num
  · refine (mem_integerVectors_iff (n := 2) (x := ![(N + 1 : ℝ), N])).2 ?_
    refine ⟨![(N + 1 : ℤ), N], ?_⟩
    ext i
    fin_cases i <;> simp

/-- Helper for Exercise 8.4: the penalized objective on the explicit ray point is
`(2 * N + 1 : ℝ) - 2 * lam`. -/
private lemma exercise_8_4_penalizedObjective_rayPoint
    (lam : ℝ) (N : ℕ) :
    exercise_8_4_objective_coeffs ⬝ᵥ ![(N + 1 : ℝ), N] +
      ![lam] ⬝ᵥ
        (exercise_8_4_constraint_rhs -
          exercise_8_4_constraint_matrix *ᵥ ![(N + 1 : ℝ), N]) =
      (2 * N + 1 : ℝ) - 2 * lam := by
  -- Expand the one-row data and evaluate the dot products explicitly.
  norm_num [exercise_8_4_objective_coeffs, exercise_8_4_constraint_rhs,
    exercise_8_4_constraint_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf

/-- Helper for Exercise 8.4: every point of `convexHull ℝ exercise_8_4_Q` satisfies the reverse
halfspace inequality `x 1 - x 0 ≤ -1`. -/
private lemma exercise_8_4_convexHull_Q_subset_reverseHalfspace :
    convexHull ℝ exercise_8_4_Q ⊆
      {x : Fin 2 → ℝ | x 1 - x 0 ≤ (-1 : ℝ)} := by
  -- First place the original set `Q` inside the target halfspace.
  refine convexHull_min ?_ ?_
  · intro x hx
    rw [mem_exercise_8_4_Q_iff] at hx
    rw [mem_exercise_8_4_base_set_iff] at hx
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx.1.2.2
  · let π₀ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
    let π₁ : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
    let L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := π₁ - π₀
    -- The target set is a linear halfspace, hence convex.
    simpa [L, π₀, π₁, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      convex_halfSpace_le L.isLinear (-1 : ℝ)

/-- Helper for Exercise 8.4: the comparison problem over `convexHull ℝ exercise_8_4_Q` has empty
feasible set. -/
private lemma exercise_8_4_comparisonFeasibleSet_eq_empty :
    lagrangian_integer_feasible_set exercise_8_4_constraint_matrix exercise_8_4_constraint_rhs
      (convexHull ℝ exercise_8_4_Q) = ∅ := by
  -- Any feasible point would satisfy both opposite inequalities, which is impossible.
  ext x
  constructor
  · intro hx
    rw [mem_lagrangian_integer_feasible_set_iff] at hx
    have hReverse : x 1 - x 0 ≤ (-1 : ℝ) :=
      exercise_8_4_convexHull_Q_subset_reverseHalfspace hx.1
    have hForward : x 0 - x 1 ≤ (-1 : ℝ) := by
      have hrow := hx.2 0
      simpa [exercise_8_4_constraint_matrix, exercise_8_4_constraint_rhs, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, sub_eq_add_neg] using hrow
    linarith
  · intro hx
    cases hx

/-- Exercise 8.4 (1). For every multiplier `λ`, the Lagrangian-relaxation subproblem over `Q` is
unbounded above, so `z_LR(λ) = +∞`. -/
theorem exercise_8_4_lagrangian_relaxation_value_eq_top
    (lam : ℝ) :
    exercise_8_4_lagrangian_relaxation_value lam = ⊤ := by
  -- Route correction: prove unboundedness through the explicit integral ray in `Q`.
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt (y + 2 * lam)
  have hRay :
      ((((2 * N + 1 : ℝ) - 2 * lam : ℝ) : EReal)) ≤
        exercise_8_4_lagrangian_relaxation_value lam := by
    -- Insert the ray point into the relaxation supremum and normalize its value.
    have hRaw :=
      lagrangian_objective_le_lagrangian_relaxation_value
        exercise_8_4_constraint_matrix exercise_8_4_constraint_rhs
        exercise_8_4_objective_coeffs exercise_8_4_Q ![lam]
        (x := ![(N + 1 : ℝ), N])
        (exercise_8_4_rayPoint_mem_Q N)
    have hvalue :
        ((exercise_8_4_objective_coeffs ⬝ᵥ ![(N + 1 : ℝ), N] +
            ![lam] ⬝ᵥ
              (exercise_8_4_constraint_rhs -
                exercise_8_4_constraint_matrix *ᵥ ![(N + 1 : ℝ), N]) : ℝ) :
          EReal) =
          ((((2 * N + 1 : ℝ) - 2 * lam : ℝ) : EReal)) := by
      exact_mod_cast exercise_8_4_penalizedObjective_rayPoint lam N
    rw [hvalue] at hRaw
    simpa [exercise_8_4_lagrangian_relaxation_value] using hRaw
  have hyReal : y < ((2 * N + 1 : ℝ) - 2 * lam : ℝ) := by
    linarith
  have hyEReal :
      ((y : ℝ) : EReal) <
        ((((2 * N + 1 : ℝ) - 2 * lam : ℝ) : EReal)) := by
    exact_mod_cast hyReal
  exact lt_of_lt_of_le hyEReal hRay

/-- Exercise 8.4 (2). The Lagrangian dual bound is `z_LD = +∞`. -/
theorem exercise_8_4_lagrangian_dual_value_eq_top :
    exercise_8_4_lagrangian_dual_value = ⊤ := by
  -- Rewrite the dual as an infimum over a constant singleton image.
  rw [exercise_8_4_lagrangian_dual_value_eq_sInf]
  have hnonempty : Set.Nonempty (Set.Ici (0 : ℝ)) := by
    exact ⟨0, by simp⟩
  have himage :
      (fun lam : ℝ ↦ exercise_8_4_lagrangian_relaxation_value lam) '' Set.Ici (0 : ℝ) = {⊤} := by
    have hconst :
        (fun lam : ℝ ↦ exercise_8_4_lagrangian_relaxation_value lam) =
          fun _ : ℝ ↦ (⊤ : EReal) := by
      funext lam
      simp [exercise_8_4_lagrangian_relaxation_value_eq_top]
    rw [hconst]
    exact Set.Nonempty.image_const hnonempty (⊤ : EReal)
  simp [himage]

/-- Exercise 8.4 (3). The comparison problem
`max {x₁ + x₂ : x₁ - x₂ ≤ -1, x ∈ conv(Q)}` is infeasible, so its canonical `EReal` value is
`⊥`. -/
  theorem exercise_8_4_convex_hull_comparison_value_eq_bot :
    integer_program_value exercise_8_4_constraint_matrix exercise_8_4_constraint_rhs
      exercise_8_4_objective_coeffs (convexHull ℝ exercise_8_4_Q) = ⊥ := by
  -- Reduce the value to a supremum over the empty feasible set.
  rw [integer_program_value_eq_sSup]
  simp [exercise_8_4_comparisonFeasibleSet_eq_empty]

end Exercise84
