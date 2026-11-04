/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_1.ch10_sec10_1_theorem_10_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix
open scoped MatrixOrder

-- Semantic search note: the policy-requested Lean semantic search tool `lean_leansearch` was
-- unavailable in this session (`tool_search` returned no matching deferred tool), so this file
-- follows the Chapter 10.1 semidefinite-programming matrix surface already present in the repo.

section Exercise101

variable {m n : ℕ}

private def max_cut_sdp_constraint_matrix (n : ℕ) : Fin n → Matrix (Fin n) (Fin n) ℝ :=
  fun i ↦ Matrix.diagonal (Pi.single i 1)

private def max_cut_sdp_constraint_rhs (n : ℕ) : Fin n → ℝ :=
  fun _ ↦ 1

/-- The objective values of the primal semidefinite relaxation
`max {(1 / 4) Tr (L X) | X is positive semidefinite, X_ii = 1}` of max cut. -/
def max_cut_sdp_primal_objective_values
    (L : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  sdp_primal_objective_values
    (max_cut_sdp_constraint_matrix n)
    (max_cut_sdp_constraint_rhs n)
    ((1 / 4 : ℝ) • L)

/-- Exercise 10.1 (2). The dual of the semidefinite relaxation
`max {(1 / 4) Tr (L X) | X is positive semidefinite, X_ii = 1}` of max cut is the minimization
problem whose objective values are attained by vectors `y` with
`Matrix.diagonal y - (1 / 4) • L` positive semidefinite and objective `sum_i y i`. -/
def max_cut_sdp_dual_objective_values
    (L : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  sdp_dual_objective_values
    (max_cut_sdp_constraint_matrix n)
    (max_cut_sdp_constraint_rhs n)
    ((1 / 4 : ℝ) • L)

/-- The max-cut SDP primal problem is strictly feasible when one feasible matrix is positive
definite. -/
def max_cut_sdp_primal_strictly_feasible (n : ℕ) : Prop :=
  sdp_primal_strictly_feasible
    (max_cut_sdp_constraint_matrix n)
    (max_cut_sdp_constraint_rhs n)

/-- The max-cut SDP dual problem is strictly feasible when one dual slack matrix is positive
definite. -/
def max_cut_sdp_dual_strictly_feasible
    (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  sdp_dual_strictly_feasible
    (max_cut_sdp_constraint_matrix n)
    ((1 / 4 : ℝ) • L)

/-- Helper for Exercise 10.1: tracing a max-cut singleton constraint matrix against `X` recovers
the diagonal entry `X i i`. -/
lemma trace_max_cut_constraint_matrix_mul
    (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Matrix.trace (max_cut_sdp_constraint_matrix n i * X) = X i i := by
  -- The constraint matrix is diagonal with a single `1` in the `i`th position.
  simp [max_cut_sdp_constraint_matrix, Matrix.trace, Pi.single_apply]

/-- Helper for Exercise 10.1: the weighted sum of the max-cut singleton constraint matrices is the
diagonal matrix with those weights on the diagonal. -/
lemma sum_smul_max_cut_constraint_matrix
    (y : Fin n → ℝ) :
    (∑ i, y i • max_cut_sdp_constraint_matrix n i) = Matrix.diagonal y := by
  -- Compare entries directly, splitting into diagonal and off-diagonal cases.
  ext i j
  by_cases hij : i = j
  · subst hij
    -- On the diagonal only the `i`th singleton constraint contributes.
    rw [Matrix.diagonal_apply_eq]
    calc
      (∑ x, y x • max_cut_sdp_constraint_matrix n x) i i
          = ∑ x, (y x • max_cut_sdp_constraint_matrix n x) i i := by
              rw [Matrix.sum_apply]
      _ = ∑ x, y x * max_cut_sdp_constraint_matrix n x i i := by
            simp [Matrix.smul_apply]
      _ = ∑ x, y x * if x = i then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [max_cut_sdp_constraint_matrix, Pi.single_apply, eq_comm]
      _ = y i := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro x hx hxi
              simp [hxi]
            · simp
  · -- Off the diagonal every singleton constraint matrix vanishes.
    rw [Matrix.diagonal_apply_ne _ hij]
    calc
      (∑ x, y x • max_cut_sdp_constraint_matrix n x) i j
          = ∑ x, (y x • max_cut_sdp_constraint_matrix n x) i j := by
              rw [Matrix.sum_apply]
      _ = ∑ x, y x * max_cut_sdp_constraint_matrix n x i j := by
            simp [Matrix.smul_apply]
      _ = ∑ x, 0 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [max_cut_sdp_constraint_matrix, Matrix.diagonal_apply_ne _ hij]
      _ = 0 := by
            simp

/-- Helper for Exercise 10.1: subtracting a symmetric matrix from the diagonal matrix of its row
absolute sums produces a positive-semidefinite matrix. -/
lemma row_abs_sum_slack_posSemidef
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsSymm) :
    (Matrix.diagonal (fun i ↦ ∑ j, |L i j|) - L).PosSemidef := by
  let rowAbs : Fin n → ℝ := fun i ↦ ∑ j, |L i j|
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Over `ℝ`, symmetry is the same as Hermitian symmetry.
    exact (Matrix.isSymm_diagonal rowAbs).sub hL
  · intro x
    let quadratic : ℝ := ∑ i, ∑ j, x i * L i j * x j
    let bound : ℝ := ∑ i, rowAbs i * x i ^ 2
    have hpair :
        ∀ i j, 2 * |x i * L i j * x j| ≤ |L i j| * x i ^ 2 + |L i j| * x j ^ 2 := by
      intro i j
      have hab : 2 * |x i| * |x j| ≤ |x i| ^ 2 + |x j| ^ 2 := by
        simpa [sq, mul_assoc] using two_mul_le_add_sq (|x i|) (|x j|)
      have hmul :
          |L i j| * (2 * |x i| * |x j|) ≤ |L i j| * (|x i| ^ 2 + |x j| ^ 2) :=
        mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      calc
        2 * |x i * L i j * x j|
            = |L i j| * (2 * |x i| * |x j|) := by
                rw [abs_mul, abs_mul]
                ring
        _ ≤ |L i j| * (|x i| ^ 2 + |x j| ^ 2) := hmul
        _ = |L i j| * x i ^ 2 + |L i j| * x j ^ 2 := by
              rw [mul_add, sq_abs, sq_abs]
    have hleft :
        ∑ i, ∑ j, 2 * |x i * L i j * x j| = 2 * ∑ i, ∑ j, |x i * L i j * x j| := by
      simp [two_mul, Finset.mul_sum]
    have hrow :
        ∑ i, ∑ j, |L i j| * x i ^ 2 = bound := by
      unfold bound rowAbs
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [← Finset.sum_mul]
    have hcol :
        ∑ i, ∑ j, |L i j| * x j ^ 2 = bound := by
      unfold bound rowAbs
      calc
        ∑ i, ∑ j, |L i j| * x j ^ 2
            = ∑ j, ∑ i, |L i j| * x j ^ 2 := by
                rw [Finset.sum_comm]
        _ = ∑ j, (∑ i, |L i j|) * x j ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [← Finset.sum_mul]
        _ = ∑ j, (∑ i, |L j i|) * x j ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact congrArg abs (hL.apply j i)
        _ = bound := by
              rfl
    have habs_bound : |quadratic| ≤ bound := by
      have habs_sum :
          |quadratic| ≤ ∑ i, ∑ j, |x i * L i j * x j| := by
        unfold quadratic
        calc
          |∑ i, ∑ j, x i * L i j * x j| ≤ ∑ i, |∑ j, x i * L i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, |x i * L i j * x j| := by
              exact Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
      have hpair_sum :
          2 * ∑ i, ∑ j, |x i * L i j * x j| ≤ 2 * bound := by
        have hpair_sum' :
            ∑ i, ∑ j, 2 * |x i * L i j * x j| ≤
              ∑ i, ∑ j, (|L i j| * x i ^ 2 + |L i j| * x j ^ 2) := by
          exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i j
        have hright :
            ∑ i, ∑ j, (|L i j| * x i ^ 2 + |L i j| * x j ^ 2) = 2 * bound := by
          calc
            ∑ i, ∑ j, (|L i j| * x i ^ 2 + |L i j| * x j ^ 2)
                = (∑ i, ∑ j, |L i j| * x i ^ 2) + (∑ i, ∑ j, |L i j| * x j ^ 2) := by
                    simp [Finset.sum_add_distrib]
            _ = bound + bound := by
                  rw [hrow, hcol]
            _ = 2 * bound := by
                  ring
        rw [hleft, hright] at hpair_sum'
        exact hpair_sum'
      have habs_terms : ∑ i, ∑ j, |x i * L i j * x j| ≤ bound := by
        linarith
      exact habs_sum.trans habs_terms
    have hquadratic_le : quadratic ≤ bound := by
      exact le_trans (le_abs_self quadratic) habs_bound
    have hdiag :
        star x ⬝ᵥ (Matrix.diagonal rowAbs *ᵥ x) = bound := by
      unfold bound rowAbs
      calc
        star x ⬝ᵥ (Matrix.diagonal (fun i ↦ ∑ j, |L i j|) *ᵥ x)
            = ∑ i, x i * ((∑ j, |L i j|) * x i) := by
                simp [dotProduct, Matrix.mulVec_diagonal]
        _ = ∑ i, (∑ j, |L i j|) * x i ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
    have hoff :
        star x ⬝ᵥ (L *ᵥ x) = quadratic := by
      unfold quadratic
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    have hquad :
        star x ⬝ᵥ ((Matrix.diagonal rowAbs - L) *ᵥ x) = bound - quadratic := by
      rw [Matrix.sub_mulVec, dotProduct_sub, hdiag, hoff]
    rw [hquad]
    linarith

/-- Helper for Exercise 10.1: the standard diagonally dominant dual witness for the max-cut SDP is
positive definite. -/
lemma max_cut_dual_certificate_posDef
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsSymm) :
    let y : Fin n → ℝ := fun i ↦ 1 + (1 / 4 : ℝ) * ∑ j, |L i j|
    (Matrix.diagonal y - (1 / 4 : ℝ) • L).PosDef := by
  dsimp
  let rowAbs : Fin n → ℝ := fun i ↦ ∑ j, |L i j|
  -- Decompose the certificate into the identity plus a PSD diagonally dominant correction.
  have hslack : (Matrix.diagonal rowAbs - L).PosSemidef :=
    row_abs_sum_slack_posSemidef L hL
  have hscaled : ((1 / 4 : ℝ) • (Matrix.diagonal rowAbs - L)).PosSemidef :=
    Matrix.PosSemidef.smul hslack (by norm_num)
  have hdecomp :
      Matrix.diagonal (fun i ↦ 1 + (1 / 4 : ℝ) * rowAbs i) - (1 / 4 : ℝ) • L =
        (1 : Matrix (Fin n) (Fin n) ℝ) + (1 / 4 : ℝ) • (Matrix.diagonal rowAbs - L) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [rowAbs]
      ring
    · simp [rowAbs, hij]
  rw [hdecomp]
  -- The identity supplies the strict positivity; the correction term is only semidefinite.
  exact Matrix.PosDef.one.add_posSemidef hscaled

/-- Membership in `max_cut_sdp_primal_objective_values L` is exactly the existence of a
positive-semidefinite matrix with diagonal `1` and the prescribed primal objective value. -/
theorem mem_max_cut_sdp_primal_objective_values_iff
    (L : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    r ∈ max_cut_sdp_primal_objective_values L ↔
      ∃ X : Matrix (Fin n) (Fin n) ℝ,
        X.PosSemidef ∧
          (∀ i, X i i = 1) ∧
            (1 / 4 : ℝ) * Matrix.trace (L * X) = r := by
  -- Unpack the generic SDP feasible-value characterization into the max-cut diagonal constraints.
  constructor
  · rintro ⟨X, hX, hobjective⟩
    rcases hX with ⟨hXpsd, hconstraints⟩
    refine ⟨X, hXpsd, ?_, ?_⟩
    · -- Each singleton trace constraint is exactly one diagonal entry of `X`.
      intro i
      simpa [max_cut_sdp_constraint_rhs, trace_max_cut_constraint_matrix_mul] using hconstraints i
    · -- The generic trace objective becomes `(1 / 4) * Tr (L X)`.
      simpa [sdp_primal_objective, smul_mul_assoc] using hobjective
  · rintro ⟨X, hXpsd, hdiag, hobjective⟩
    refine ⟨X, ?_, ?_⟩
    · -- Repackage the diagonal equations as the generic SDP trace constraints.
      refine ⟨hXpsd, ?_⟩
      intro i
      simpa [max_cut_sdp_constraint_rhs, trace_max_cut_constraint_matrix_mul] using hdiag i
    · -- The objective is the same trace after pulling out the scalar factor.
      simpa [sdp_primal_objective, smul_mul_assoc] using hobjective

/-- Membership in `max_cut_sdp_dual_objective_values L` is exactly the existence of a dual vector
with positive-semidefinite slack and the prescribed dual objective value. -/
theorem mem_max_cut_sdp_dual_objective_values_iff
    (L : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    r ∈ max_cut_sdp_dual_objective_values L ↔
      ∃ y : Fin n → ℝ,
        (Matrix.diagonal y - (1 / 4 : ℝ) • L).PosSemidef ∧
          (∑ i, y i) = r := by
  -- Unpack the generic dual feasible-value characterization into the max-cut slack matrix.
  constructor
  · rintro ⟨y, hy, hobjective⟩
    refine ⟨y, ?_, ?_⟩
    · -- Summing the singleton constraint matrices gives the diagonal dual slack.
      simpa [sdp_dual_feasible_region, sdp_dual_slack, sum_smul_max_cut_constraint_matrix] using hy
    · -- The generic dual objective is just the sum of the dual coordinates.
      simpa [sdp_dual_objective, max_cut_sdp_constraint_rhs] using hobjective
  · rintro ⟨y, hy, hobjective⟩
    refine ⟨y, ?_, ?_⟩
    · -- Repackage the max-cut dual slack as the generic SDP slack.
      simpa [sdp_dual_feasible_region, sdp_dual_slack, sum_smul_max_cut_constraint_matrix] using hy
    · -- The right-hand side of every max-cut constraint is `1`.
      simpa [sdp_dual_objective, max_cut_sdp_constraint_rhs] using hobjective

/-- Exercise 10.1 (1). Any feasible solution of the primal semidefinite problem (10.1) has
objective value at most the objective value of any feasible solution of the dual problem (10.2). -/
theorem exercise_10_1_sdp_weak_duality
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ)
    (hX : X.PosSemidef)
    (hprimal : ∀ i, Matrix.trace (A i * X) = b i)
    (hdual : (sdp_dual_slack A C y).PosSemidef) :
    sdp_primal_objective C X ≤ sdp_dual_objective b y := by
  have hdualTrace :
      Matrix.trace ((∑ i, y i • A i) * X) = sdp_dual_objective b y := by
    -- Expand the trace term and substitute the primal equalities `Tr (Aᵢ X) = bᵢ`.
    calc
      Matrix.trace ((∑ i, y i • A i) * X)
          = Matrix.trace (∑ i, (y i • A i) * X) := by
              rw [Finset.sum_mul]
      _ = ∑ i, Matrix.trace ((y i • A i) * X) := by
            rw [Matrix.trace_sum]
      _ = ∑ i, y i * Matrix.trace (A i * X) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [smul_mul_assoc, Matrix.trace_smul]
            ring
      _ = ∑ i, y i * b i := by
            simp [hprimal]
      _ = sdp_dual_objective b y := rfl
  have hslackTrace :
      Matrix.trace ((sdp_dual_slack A C y) * X) =
        sdp_dual_objective b y - sdp_primal_objective C X := by
    -- Rewrite the dual slack as `(∑ᵢ yᵢ Aᵢ) - C` and separate the trace.
    calc
      Matrix.trace ((sdp_dual_slack A C y) * X)
          = Matrix.trace ((((∑ i, y i • A i) - C) * X)) := by
              rfl
      _ = Matrix.trace (((∑ i, y i • A i) * X) - C * X) := by
            rw [sub_mul]
      _ = Matrix.trace (((∑ i, y i • A i) * X)) - Matrix.trace (C * X) := by
            rw [Matrix.trace_sub]
      _ = sdp_dual_objective b y - sdp_primal_objective C X := by
            rw [hdualTrace, sdp_primal_objective]
  have hnonneg : 0 ≤ Matrix.trace ((sdp_dual_slack A C y) * X) :=
    Matrix.PosSemidef.trace_mul_nonneg hdual hX
  -- Nonnegativity of the slack trace is exactly the weak-duality inequality.
  have hgap : 0 ≤ sdp_dual_objective b y - sdp_primal_objective C X := by
    simpa [hslackTrace] using hnonneg
  exact sub_nonneg.mp hgap

/-- Exercise 10.1 (3). The primal semidefinite relaxation of max cut is strictly feasible. -/
theorem exercise_10_1_max_cut_primal_strictly_feasible :
    max_cut_sdp_primal_strictly_feasible n := by
  refine ⟨(1 : Matrix (Fin n) (Fin n) ℝ), Matrix.PosDef.one, ?_⟩
  -- The identity matrix is positive definite and satisfies the diagonal-equals-`1` constraints.
  intro i
  simpa [max_cut_sdp_constraint_rhs] using
    (trace_max_cut_constraint_matrix_mul (n := n) (X := (1 : Matrix (Fin n) (Fin n) ℝ)) i)

/-- Exercise 10.1 (4). If `L` is the symmetric Laplacian matrix of the graph, then the dual of the
max-cut semidefinite relaxation is strictly feasible. -/
theorem exercise_10_1_max_cut_dual_strictly_feasible
    (L : Matrix (Fin n) (Fin n) ℝ) (hL : L.IsSymm) :
    max_cut_sdp_dual_strictly_feasible L := by
  let y : Fin n → ℝ := fun i ↦ 1 + (1 / 4 : ℝ) * ∑ j, |L i j|
  refine ⟨y, ?_⟩
  -- Use the diagonally dominant positive-definite certificate from the helper lemma.
  simpa [sdp_dual_slack, sum_smul_max_cut_constraint_matrix, y] using
    (max_cut_dual_certificate_posDef (n := n) L hL)

end Exercise101
