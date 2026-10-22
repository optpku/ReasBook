/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_1
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix

noncomputable section

-- Primary domain: CDT trust-region subproblems and Hermitian-eigenvalue signatures.
-- Core/canonical owner sampled upstream in this chapter: `cdtObjective`, `cdtConstraintResidual`,
-- `cdtFeasibleSet`, `IsCdtSolution`, `cdtShiftedHessian`, and `IsCdtOptimalityPair` from
-- `Theorem_13_5_1`, together with `cdtShiftedHessian_isSymm`,
-- `cdtShiftedHessian_isHermitian`, and `Matrix.HasAtMostOneNegativeEigenvalue`.
-- Source-facing layer here: only the concrete Exercise 13.3 data and its conclusions.

section

local notation "StepVector" => EuclideanSpace ℝ (Fin 2)
local notation "Matrix2" => Matrix (Fin 2) (Fin 2) ℝ

/-- The linear term `g = (2, 0)ᵀ` in Chapter 13 Exercise 13.3. -/
def chapter13Exercise133g : StepVector :=
  WithLp.toLp 2 ![(2 : ℝ), 0]

/-- The Hessian matrix `B = [[-2, 0], [0, 2]]` in Chapter 13 Exercise 13.3. -/
def chapter13Exercise133B : Matrix2 :=
  !![(-2 : ℝ), 0; 0, 2]

/-- The linearized-constraint matrix `A = I₂` in Chapter 13 Exercise 13.3. -/
def chapter13Exercise133A : Matrix2 :=
  1

/-- The affine residual vector `c = (-2, 0)ᵀ` in Chapter 13 Exercise 13.3. -/
def chapter13Exercise133c : StepVector :=
  WithLp.toLp 2 ![(-2 : ℝ), 0]

/-- The trust-region radius `Δ = 2` in Chapter 13 Exercise 13.3. -/
def chapter13Exercise133Delta : ℝ :=
  2

/-- The linearized-constraint radius `ξ = 1` in Chapter 13 Exercise 13.3. -/
def chapter13Exercise133Xi : ℝ :=
  1

/-- The explicit solution candidate `d* = (2, 0)ᵀ` for the CDT subproblem in Exercise 13.3. -/
def chapter13Exercise133Solution : StepVector :=
  WithLp.toLp 2 ![(2 : ℝ), 0]

/-- The explicit multiplier `λ = 1` used for the trust-region constraint in Exercise 13.3. -/
def chapter13Exercise133Lambda : ℝ :=
  1

/-- The explicit multiplier `μ = 0` used for the linearized-constraint bound in Exercise 13.3. -/
def chapter13Exercise133Mu : ℝ :=
  0

/-- The matrix `chapter13Exercise133B` is symmetric. -/
theorem chapter13Exercise133BIsSymm :
    chapter13Exercise133B.IsSymm := by
  -- Entrywise inspection of the concrete `2 × 2` matrix shows symmetry immediately.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chapter13Exercise133B]

/-- The multiplier-shifted Hessian for the concrete data in Exercise 13.3 is the diagonal matrix
`diag(-1, 3)`. -/
theorem chapter13Exercise133ShiftedHessian_eq :
    cdtShiftedHessian
        chapter13Exercise133B
        chapter13Exercise133A
        chapter13Exercise133Lambda
        chapter13Exercise133Mu =
      !![(-1 : ℝ), 0; 0, 3] := by
  -- Unfold the concrete data and compute the diagonal shift entrywise.
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cdtShiftedHessian, chapter13Exercise133B, chapter13Exercise133A,
      chapter13Exercise133Lambda, chapter13Exercise133Mu]

/-- Helper for Chapter13 Exercise 13.3: the shifted Hessian is the diagonal matrix
`Matrix.diagonal ![(-1 : ℝ), 3]`. -/
theorem chapter13Exercise133ShiftedHessian_eq_diagonal :
    cdtShiftedHessian
        chapter13Exercise133B
        chapter13Exercise133A
        chapter13Exercise133Lambda
        chapter13Exercise133Mu =
      Matrix.diagonal ![(-1 : ℝ), 3] := by
  -- The concrete shifted Hessian has only the two diagonal entries `-1` and `3`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cdtShiftedHessian, chapter13Exercise133B, chapter13Exercise133A,
      chapter13Exercise133Lambda, chapter13Exercise133Mu]

/-- The shifted Hessian of Exercise 13.3 is symmetric. -/
theorem chapter13Exercise133ShiftedHessianIsSymm :
    (cdtShiftedHessian
      chapter13Exercise133B
      chapter13Exercise133A
      chapter13Exercise133Lambda
      chapter13Exercise133Mu).IsSymm := by
  -- Reuse the general CDT symmetry lemma for the concrete matrix data.
  exact cdtShiftedHessian_isSymm
    chapter13Exercise133BIsSymm
    chapter13Exercise133A
    chapter13Exercise133Lambda
    chapter13Exercise133Mu

/-- The shifted Hessian of Exercise 13.3 is Hermitian, so the canonical matrix-eigenvalue API
applies directly. -/
theorem chapter13Exercise133ShiftedHessianIsHermitian :
    (cdtShiftedHessian
      chapter13Exercise133B
      chapter13Exercise133A
      chapter13Exercise133Lambda
      chapter13Exercise133Mu).IsHermitian :=
  cdtShiftedHessian_isHermitian
    chapter13Exercise133BIsSymm
    chapter13Exercise133A
    chapter13Exercise133Lambda
    chapter13Exercise133Mu

#print axioms chapter13Exercise133g
#print axioms chapter13Exercise133B
#print axioms chapter13Exercise133A
#print axioms chapter13Exercise133c
#print axioms chapter13Exercise133Delta
#print axioms chapter13Exercise133Xi
#print axioms chapter13Exercise133Solution
#print axioms chapter13Exercise133Lambda
#print axioms chapter13Exercise133Mu
#print axioms cdtObjective
#print axioms cdtConstraintResidual
#print axioms cdtFeasibleSet
#print axioms cdtShiftedHessian

/-- Helper for Chapter13 Exercise 13.3: the trust-region norm square is the sum of the two
coordinate squares. -/
lemma chapter13Exercise133NormSq_eq (d : StepVector) :
    ‖d‖ ^ 2 = d 0 ^ 2 + d 1 ^ 2 := by
  -- The Euclidean `ℓ2` norm on `Fin 2 → ℝ` expands to the two coordinate squares.
  simpa [Fin.sum_univ_two] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℝ) d)

/-- Helper for Chapter13 Exercise 13.3: the affine residual is the vector `(d 0 - 2, d 1)`. -/
lemma chapter13Exercise133Residual_eq (d : StepVector) :
    cdtConstraintResidual chapter13Exercise133c chapter13Exercise133A d =
      WithLp.toLp 2 ![d 0 - 2, d 1] := by
  -- The matrix `A = I₂` leaves the step unchanged, so adding `c = (-2, 0)` shifts only the
  -- first coordinate.
  ext i
  fin_cases i <;> simp [cdtConstraintResidual, chapter13Exercise133c, chapter13Exercise133A,
    Matrix.toEuclideanLin]
  ring

/-- Helper for Chapter13 Exercise 13.3: the residual norm square is
`(d 0 - 2)^2 + d 1^2`. -/
lemma chapter13Exercise133ResidualNormSq_eq (d : StepVector) :
    ‖cdtConstraintResidual chapter13Exercise133c chapter13Exercise133A d‖ ^ 2 =
      (d 0 - 2) ^ 2 + d 1 ^ 2 := by
  -- Rewrite the residual to coordinates and expand the Euclidean `ℓ2` norm square.
  rw [chapter13Exercise133Residual_eq]
  simpa [Fin.sum_univ_two] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℝ) (WithLp.toLp 2 ![d 0 - 2, d 1]))

/-- Helper for Chapter13 Exercise 13.3: the CDT objective reduces to
`d 0 * (2 - d 0) + d 1^2`. -/
lemma chapter13Exercise133Objective_eq (d : StepVector) :
    cdtObjective chapter13Exercise133B chapter13Exercise133g d =
      d 0 * (2 - d 0) + d 1 ^ 2 := by
  -- Expanding the quadratic model with the concrete `g` and diagonal `B` leaves a simple scalar
  -- expression in the two coordinates.
  simp [cdtObjective, chapter13Exercise133B, chapter13Exercise133g, PiLp.inner_apply,
    dotProduct, Matrix.toEuclideanLin, Fin.sum_univ_two]
  ring

/-- Helper for Chapter13 Exercise 13.3: the residual at the candidate step is exactly zero. -/
lemma chapter13Exercise133SolutionResidual_eq_zero :
    cdtConstraintResidual
        chapter13Exercise133c
        chapter13Exercise133A
        chapter13Exercise133Solution =
      0 := by
  -- Substituting `d* = (2, 0)` cancels the affine residual `c + Aᵀ d*`.
  rw [chapter13Exercise133Residual_eq]
  ext i
  fin_cases i <;> norm_num [chapter13Exercise133Solution]

/-- Helper for Chapter13 Exercise 13.3: the candidate step `(2, 0)` is feasible. -/
lemma chapter13Exercise133SolutionFeasible :
    chapter13Exercise133Solution ∈
      cdtFeasibleSet
        chapter13Exercise133Delta
        chapter13Exercise133Xi
        chapter13Exercise133c
        chapter13Exercise133A := by
  -- Verify the trust-region bound by squaring the norm, then use the zero residual.
  rw [mem_cdtFeasibleSet_iff]
  constructor
  · have hSq : ‖chapter13Exercise133Solution‖ ^ 2 = chapter13Exercise133Delta ^ 2 := by
      rw [chapter13Exercise133NormSq_eq]
      norm_num [chapter13Exercise133Solution, chapter13Exercise133Delta]
    have hNonneg : 0 ≤ ‖chapter13Exercise133Solution‖ := norm_nonneg _
    norm_num [chapter13Exercise133Delta] at hSq
    have hNorm : ‖chapter13Exercise133Solution‖ = 2 := by
      nlinarith
    simpa [chapter13Exercise133Delta] using hNorm.le
  · rw [chapter13Exercise133SolutionResidual_eq_zero]
    norm_num [chapter13Exercise133Xi]

/-- Helper for Chapter13 Exercise 13.3: every feasible step has first coordinate in `[1, 2]`. -/
lemma chapter13Exercise133FirstCoordinate_bounds
    {d : StepVector}
    (hd :
      d ∈ cdtFeasibleSet
        chapter13Exercise133Delta
        chapter13Exercise133Xi
        chapter13Exercise133c
        chapter13Exercise133A) :
    1 ≤ d 0 ∧ d 0 ≤ 2 := by
  -- The residual bound controls `|d 0 - 2|`, and the trust-region bound then forces `d 0 ≤ 2`.
  rw [mem_cdtFeasibleSet_iff] at hd
  have hResidualSq :
      ‖cdtConstraintResidual chapter13Exercise133c chapter13Exercise133A d‖ ^ 2 ≤
        chapter13Exercise133Xi ^ 2 := by
    have hNonneg :
        0 ≤ ‖cdtConstraintResidual chapter13Exercise133c chapter13Exercise133A d‖ :=
      norm_nonneg _
    nlinarith [hd.2]
  rw [chapter13Exercise133ResidualNormSq_eq] at hResidualSq
  have hySq : 0 ≤ d 1 ^ 2 := sq_nonneg _
  norm_num [chapter13Exercise133Xi] at hResidualSq
  have hLower : 1 ≤ d 0 := by
    nlinarith [hResidualSq, hySq]
  have hTrustSq : ‖d‖ ^ 2 ≤ chapter13Exercise133Delta ^ 2 := by
    have hNonneg : 0 ≤ ‖d‖ := norm_nonneg _
    nlinarith [hd.1]
  rw [chapter13Exercise133NormSq_eq] at hTrustSq
  norm_num [chapter13Exercise133Delta] at hTrustSq
  have hUpper : d 0 ≤ 2 := by
    nlinarith [hTrustSq, hySq, hLower]
  exact ⟨hLower, hUpper⟩

/-- Helper for Chapter13 Exercise 13.3: every feasible step has nonnegative CDT objective value.
-/
lemma chapter13Exercise133Objective_nonneg_of_feasible
    (d : StepVector)
    (hd :
      d ∈ cdtFeasibleSet
        chapter13Exercise133Delta
        chapter13Exercise133Xi
        chapter13Exercise133c
        chapter13Exercise133A) :
    0 ≤ cdtObjective chapter13Exercise133B chapter13Exercise133g d := by
  -- Once feasibility gives `1 ≤ d 0 ≤ 2`, both terms in the scalar objective formula are
  -- nonnegative.
  rcases chapter13Exercise133FirstCoordinate_bounds hd with ⟨hLower, hUpper⟩
  rw [chapter13Exercise133Objective_eq]
  have hSecond : 0 ≤ d 1 ^ 2 := sq_nonneg _
  have hFirst : 0 ≤ d 0 * (2 - d 0) := by
    nlinarith
  nlinarith

/-- Helper for Chapter13 Exercise 13.3: the explicit step
`chapter13Exercise133Solution = (2, 0)ᵀ` solves the CDT subproblem with
`g = chapter13Exercise133g = (2, 0)ᵀ`, `B = chapter13Exercise133B = [[-2, 0], [0, 2]]`,
`A = chapter13Exercise133A = I₂`, `c = chapter13Exercise133c = (-2, 0)ᵀ`,
`Δ = chapter13Exercise133Delta = 2`, and `ξ = chapter13Exercise133Xi = 1`. -/
theorem chapter13Exercise133IsCdtSolution :
    IsCdtSolution
      chapter13Exercise133B
      chapter13Exercise133g
      chapter13Exercise133A
      chapter13Exercise133c
      chapter13Exercise133Delta
      chapter13Exercise133Xi
      chapter13Exercise133Solution := by
  -- Package the explicit feasible point together with the objective lower bound on all feasible
  -- steps.
  rw [isCdtSolution_iff_mem_cdtFeasibleSet_and_isMinOn]
  refine ⟨chapter13Exercise133SolutionFeasible, ?_⟩
  rw [isMinOn_iff]
  intro d hd
  have hNonneg : 0 ≤ cdtObjective chapter13Exercise133B chapter13Exercise133g d :=
    chapter13Exercise133Objective_nonneg_of_feasible d hd
  have hValue :
      cdtObjective
          chapter13Exercise133B
          chapter13Exercise133g
          chapter13Exercise133Solution =
        0 := by
    rw [chapter13Exercise133Objective_eq]
    norm_num [chapter13Exercise133Solution]
  nlinarith

/-- Helper for Chapter13 Exercise 13.3: at the solution
`chapter13Exercise133Solution = (2, 0)ᵀ`, the
trust-region constraint is active while the linearized-constraint bound is inactive:
`‖chapter13Exercise133Solution‖ = chapter13Exercise133Delta` and
`‖cdtConstraintResidual chapter13Exercise133c chapter13Exercise133A
chapter13Exercise133Solution‖ < chapter13Exercise133Xi`. -/
theorem chapter13Exercise133OnlyTrustRegionConstraintActive :
    ‖chapter13Exercise133Solution‖ = chapter13Exercise133Delta ∧
      ‖cdtConstraintResidual
          chapter13Exercise133c
          chapter13Exercise133A
          chapter13Exercise133Solution‖ <
        chapter13Exercise133Xi := by
  -- Compute the trust-region norm from its square and read strict inactivity from the zero
  -- residual.
  constructor
  · have hSq : ‖chapter13Exercise133Solution‖ ^ 2 = chapter13Exercise133Delta ^ 2 := by
      rw [chapter13Exercise133NormSq_eq]
      norm_num [chapter13Exercise133Solution, chapter13Exercise133Delta]
    have hNonneg : 0 ≤ ‖chapter13Exercise133Solution‖ := norm_nonneg _
    norm_num [chapter13Exercise133Delta] at hSq
    have hNorm : ‖chapter13Exercise133Solution‖ = 2 := by
      nlinarith
    simpa [chapter13Exercise133Delta] using hNorm
  · rw [chapter13Exercise133SolutionResidual_eq_zero]
    norm_num [chapter13Exercise133Xi]

/-- The multiplier pair `(chapter13Exercise133Lambda, chapter13Exercise133Mu) = (1, 0)`
satisfies the CDT stationarity and complementarity conditions at
`chapter13Exercise133Solution`. -/
theorem chapter13Exercise133IsOptimalityPair :
    IsCdtOptimalityPair
      chapter13Exercise133B
      chapter13Exercise133g
      chapter13Exercise133A
      chapter13Exercise133c
      chapter13Exercise133Delta
      chapter13Exercise133Xi
      chapter13Exercise133Solution
      chapter13Exercise133Lambda
      chapter13Exercise133Mu := by
  -- Verify the KKT conditions directly for the concrete multipliers `(1, 0)`.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [chapter13Exercise133Lambda]
  · norm_num [chapter13Exercise133Mu]
  · -- The shifted Hessian sends `(2, 0)` to `(-2, 0)`, which is exactly `-g`.
    rw [chapter13Exercise133ShiftedHessian_eq]
    ext i
    fin_cases i <;>
      norm_num [chapter13Exercise133Solution,
        chapter13Exercise133g, chapter13Exercise133Mu, chapter13Exercise133c,
        chapter13Exercise133A, Matrix.toEuclideanLin]
  · -- The trust-region multiplier is active because `‖d*‖ = Δ`.
    have hActive := chapter13Exercise133OnlyTrustRegionConstraintActive
    simp [chapter13Exercise133Lambda, hActive.1]
  · -- The residual multiplier vanishes because `μ = 0`.
    simp [chapter13Exercise133Mu]

/-- Chapter13 Exercise 13.3 (3): for the solution `chapter13Exercise133Solution = (2, 0)ᵀ` and
the multiplier pair `(chapter13Exercise133Lambda, chapter13Exercise133Mu) = (1, 0)`, the
Lagrangian Hessian
`cdtShiftedHessian chapter13Exercise133B chapter13Exercise133A chapter13Exercise133Lambda
chapter13Exercise133Mu` has one negative eigenvalue. -/
theorem chapter13Exercise133HasOneNegativeEigenvalue :
    ∃ i j : Fin 2,
      i ≠ j ∧
        chapter13Exercise133ShiftedHessianIsHermitian.eigenvalues i < 0 ∧
        0 < chapter13Exercise133ShiftedHessianIsHermitian.eigenvalues j := by
  -- Move the concrete diagonal spectral points `-1` and `3` into the Hermitian eigenvalue range.
  have hNegSpec :
      (-1 : ℝ) ∈
        spectrum ℝ
          (cdtShiftedHessian
            chapter13Exercise133B
            chapter13Exercise133A
            chapter13Exercise133Lambda
            chapter13Exercise133Mu) := by
    rw [chapter13Exercise133ShiftedHessian_eq_diagonal, spectrum_diagonal]
    exact ⟨0, by simp⟩
  have hPosSpec :
      (3 : ℝ) ∈
        spectrum ℝ
          (cdtShiftedHessian
            chapter13Exercise133B
            chapter13Exercise133A
            chapter13Exercise133Lambda
            chapter13Exercise133Mu) := by
    rw [chapter13Exercise133ShiftedHessian_eq_diagonal, spectrum_diagonal]
    exact ⟨1, by simp⟩
  have hNegRange :
      (-1 : ℝ) ∈ Set.range chapter13Exercise133ShiftedHessianIsHermitian.eigenvalues := by
    simpa [chapter13Exercise133ShiftedHessianIsHermitian.spectrum_real_eq_range_eigenvalues] using
      hNegSpec
  have hPosRange :
      (3 : ℝ) ∈ Set.range chapter13Exercise133ShiftedHessianIsHermitian.eigenvalues := by
    simpa [chapter13Exercise133ShiftedHessianIsHermitian.spectrum_real_eq_range_eigenvalues] using
      hPosSpec
  rcases hNegRange with ⟨i, hi⟩
  rcases hPosRange with ⟨j, hj⟩
  refine ⟨i, j, ?_, ?_, ?_⟩
  · -- A single eigenvalue cannot be both `-1` and `3`.
    intro hij
    subst hij
    linarith [hi, hj]
  · linarith
  · linarith

end
