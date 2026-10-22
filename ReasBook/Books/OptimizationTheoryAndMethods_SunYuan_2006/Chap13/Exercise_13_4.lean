/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_1

open Matrix

noncomputable section

-- Primary domain: Chapter 13 CDT trust-region subproblems and Hermitian eigenvalues.
-- Core/canonical owner: `cdtObjective`, `cdtConstraintResidual`, `cdtFeasibleSet`,
-- `cdtShiftedHessian`, and `IsCdtOptimalityPair` from `Theorem_13_5_1`.
-- Source-facing layer here: only the explicit `2 × 2` exercise data and its conclusions.

section

local notation "StepVector" => EuclideanSpace ℝ (Fin 2)
local notation "Matrix2" => Matrix (Fin 2) (Fin 2) ℝ

/-- The example Hessian matrix is `-I₂`. -/
def chapter13Exercise134B : Matrix2 :=
  (-1 : ℝ) • (1 : Matrix2)

/-- The example linear term is the zero vector. -/
def chapter13Exercise134g : StepVector :=
  0

/-- The example linearized-constraint matrix is `I₂`. -/
def chapter13Exercise134A : Matrix2 :=
  1

/-- The example residual vector is `0`, so the linearized constraint is `Aᵀ d = 0`. -/
def chapter13Exercise134c : StepVector :=
  0

/-- The example trust-region radius is `1`. -/
def chapter13Exercise134Delta : ℝ :=
  1

/-- The example linearized-constraint bound is `0`. -/
def chapter13Exercise134Xi : ℝ :=
  0

/-- The explicit solution candidate for the example CDT subproblem is the zero step. -/
def chapter13Exercise134Solution : StepVector :=
  0

/-- The example uses the multiplier `λ = 0`. -/
def chapter13Exercise134Lambda : ℝ :=
  0

/-- The example uses the multiplier `μ = 0`. -/
def chapter13Exercise134Mu : ℝ :=
  0

/-- The matrix `chapter13Exercise134B = -I₂` is symmetric. -/
theorem chapter13Exercise134BIsSymm :
    chapter13Exercise134B.IsSymm := by
  -- The example matrix is a real scalar multiple of the identity.
  simpa [chapter13Exercise134B] using
    (Matrix.isSymm_one : (1 : Matrix2).IsSymm).smul (-1 : ℝ)

/-- The example feasible set is the singleton `{0}` because `A = I₂`, `c = 0`, and `ξ = 0`
force `d = 0`, while `Δ = 1` leaves the trust-region bound compatible with that point. -/
theorem chapter13Exercise134FeasibleSet_eq_singleton :
    cdtFeasibleSet
        chapter13Exercise134Delta
        chapter13Exercise134Xi
        chapter13Exercise134c
        chapter13Exercise134A =
      ({chapter13Exercise134Solution} : Set StepVector) := by
  ext d
  constructor
  · intro hd
    -- The residual constraint reduces to `‖d‖ ≤ 0`, so feasibility forces `d = 0`.
    rcases (mem_cdtFeasibleSet_iff _ _ _ _ _).1 hd with ⟨_, hResidual⟩
    have hNormLe : ‖d‖ ≤ 0 := by
      simpa [chapter13Exercise134Xi, chapter13Exercise134c, chapter13Exercise134A,
        cdtConstraintResidual] using hResidual
    have hNorm : ‖d‖ = 0 := le_antisymm hNormLe (norm_nonneg d)
    have hdZero : d = 0 := norm_eq_zero.mp hNorm
    simpa [chapter13Exercise134Solution, Set.mem_singleton_iff] using hdZero
  · intro hd
    -- Conversely, the zero step satisfies both norm bounds by direct simplification.
    have hdZero : d = 0 := by
      simpa [chapter13Exercise134Solution, Set.mem_singleton_iff] using hd
    subst d
    simp [chapter13Exercise134Delta, chapter13Exercise134Xi, mem_cdtFeasibleSet_iff,
      chapter13Exercise134c, chapter13Exercise134A, cdtConstraintResidual,
      chapter13Exercise134Solution]

/-- The explicit step `chapter13Exercise134Solution = 0` globally solves the example CDT
subproblem because the feasible set is the singleton `{0}`. -/
theorem chapter13Exercise134IsMinOn :
    IsMinOn
      (cdtObjective chapter13Exercise134B chapter13Exercise134g)
      (cdtFeasibleSet
        chapter13Exercise134Delta
        chapter13Exercise134Xi
        chapter13Exercise134c
        chapter13Exercise134A)
      chapter13Exercise134Solution := by
  refine isMinOn_iff.mpr ?_
  intro x hx
  -- Once the feasible set is `{0}`, every feasible comparison point coincides with the solution.
  have hxSingleton : x ∈ ({chapter13Exercise134Solution} : Set StepVector) := by
    simpa [chapter13Exercise134FeasibleSet_eq_singleton] using hx
  have hxEq : x = chapter13Exercise134Solution := by
    simpa [Set.mem_singleton_iff] using hxSingleton
  subst x
  simp

/-- The multiplier pair `(chapter13Exercise134Lambda, chapter13Exercise134Mu) = (0, 0)` satisfies
the example CDT stationarity and complementarity conditions at
`chapter13Exercise134Solution`. -/
theorem chapter13Exercise134OptimalityPair :
    IsCdtOptimalityPair
      chapter13Exercise134B
      chapter13Exercise134g
      chapter13Exercise134A
      chapter13Exercise134c
      chapter13Exercise134Delta
      chapter13Exercise134Xi
      chapter13Exercise134Solution
      chapter13Exercise134Lambda
      chapter13Exercise134Mu := by
  refine ⟨by simp [chapter13Exercise134Lambda], by simp [chapter13Exercise134Mu], ?_, ?_, ?_⟩
  · -- Stationarity collapses to the zero vector identity for the explicit data.
    simp [cdtShiftedHessian, chapter13Exercise134B, chapter13Exercise134g,
      chapter13Exercise134A, chapter13Exercise134c, chapter13Exercise134Solution,
      chapter13Exercise134Lambda, chapter13Exercise134Mu]
  · -- The trust-region complementarity factor is `0 * (...)`.
    simp [chapter13Exercise134Lambda, chapter13Exercise134Delta,
      chapter13Exercise134Solution]
  · -- The residual complementarity factor is also `0 * (...)`.
    simp [chapter13Exercise134Mu, chapter13Exercise134Xi, chapter13Exercise134c,
      chapter13Exercise134A, chapter13Exercise134Solution, cdtConstraintResidual]

/-- For the chosen multipliers `(0, 0)`, the example shifted Hessian is just `-I₂`. -/
theorem chapter13Exercise134ShiftedHessian_eq :
    cdtShiftedHessian
        chapter13Exercise134B
        chapter13Exercise134A
        chapter13Exercise134Lambda
        chapter13Exercise134Mu =
      chapter13Exercise134B := by
  simp [cdtShiftedHessian, chapter13Exercise134A, chapter13Exercise134Lambda,
    chapter13Exercise134Mu]

/-- The example shifted Hessian is symmetric. -/
theorem chapter13Exercise134ShiftedHessianIsSymm :
    (cdtShiftedHessian
      chapter13Exercise134B
      chapter13Exercise134A
      chapter13Exercise134Lambda
      chapter13Exercise134Mu).IsSymm :=
  cdtShiftedHessian_isSymm
    chapter13Exercise134BIsSymm
    chapter13Exercise134A
    chapter13Exercise134Lambda
    chapter13Exercise134Mu

/-- The example shifted Hessian is Hermitian, so the canonical matrix-eigenvalue API applies. -/
theorem chapter13Exercise134ShiftedHessianIsHermitian :
    (cdtShiftedHessian
      chapter13Exercise134B
      chapter13Exercise134A
      chapter13Exercise134Lambda
      chapter13Exercise134Mu).IsHermitian :=
  (Matrix.isHermitian_iff_isSymm).2 chapter13Exercise134ShiftedHessianIsSymm

/-- Helper for Chapter13 Exercise 13.4: every Hermitian eigenvalue of the example shifted
Hessian equals `-1` because the matrix is exactly `-I₂`. -/
lemma chapter13Exercise134Eigenvalue_eq_negOne (i : Fin 2) :
    chapter13Exercise134ShiftedHessianIsHermitian.eigenvalues i = -1 := by
  let e : StepVector := chapter13Exercise134ShiftedHessianIsHermitian.eigenvectorBasis i
  -- Normalize the chosen eigenvector basis vector to convert the Rayleigh quotient to `-1`.
  have he_sq : dotProduct e e = ‖e‖ ^ (2 : ℕ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [e, pow_two]
  have he_norm : dotProduct e e = 1 := by
    have he_normOne : ‖e‖ = 1 := by
      simpa [e] using chapter13Exercise134ShiftedHessianIsHermitian.eigenvectorBasis.norm_eq_one i
    nlinarith [he_sq, he_normOne]
  have hNormCoords : e 0 * e 0 + e 1 * e 1 = 1 := by
    simpa [e, dotProduct] using he_norm
  have hMul : chapter13Exercise134B *ᵥ e = (-1 : ℝ) • e := by
    -- Multiplying by `-I₂` is the same as scalar multiplication by `-1`.
    simpa [chapter13Exercise134B] using (smul_mulVec (-1 : ℝ) (1 : Matrix2) e)
  calc
    chapter13Exercise134ShiftedHessianIsHermitian.eigenvalues i
        = RCLike.re
            (dotProduct
              (star ⇑(chapter13Exercise134ShiftedHessianIsHermitian.eigenvectorBasis i))
              ((cdtShiftedHessian
                chapter13Exercise134B
                chapter13Exercise134A
                chapter13Exercise134Lambda
                chapter13Exercise134Mu) *ᵥ
                ⇑(chapter13Exercise134ShiftedHessianIsHermitian.eigenvectorBasis i))) := by
          simpa using chapter13Exercise134ShiftedHessianIsHermitian.eigenvalues_eq i
    _ = RCLike.re (dotProduct (star e) (chapter13Exercise134B *ᵥ e)) := by
          simp [e, chapter13Exercise134ShiftedHessian_eq]
    _ = RCLike.re (dotProduct (star e) ((-1 : ℝ) • e)) := by
          rw [hMul]
    _ = -1 := by
          simp [e]
          nlinarith [hNormCoords]

#print axioms chapter13Exercise134B
#print axioms chapter13Exercise134g
#print axioms chapter13Exercise134A
#print axioms chapter13Exercise134c
#print axioms chapter13Exercise134Delta
#print axioms chapter13Exercise134Xi
#print axioms chapter13Exercise134Solution
#print axioms chapter13Exercise134Lambda
#print axioms chapter13Exercise134Mu

/-- Chapter13 Exercise 13.4: the explicit CDT subproblem with data
`B = chapter13Exercise134B = -I₂`, `g = 0`, `A = chapter13Exercise134A = I₂`,
`c = 0`, `Δ = 1`, and `ξ = 0` has the solution `chapter13Exercise134Solution = 0`; for the
multiplier pair `(chapter13Exercise134Lambda, chapter13Exercise134Mu) = (0, 0)`, the
Lagrangian Hessian
`cdtShiftedHessian chapter13Exercise134B chapter13Exercise134A chapter13Exercise134Lambda
chapter13Exercise134Mu` has two negative eigenvalues. -/
theorem chapter13Exercise134HasTwoNegativeEigenvalues :
    ∃ i j : Fin 2,
      i ≠ j ∧
        chapter13Exercise134ShiftedHessianIsHermitian.eigenvalues i < 0 ∧
        chapter13Exercise134ShiftedHessianIsHermitian.eigenvalues j < 0 := by
  -- The two explicit coordinates of `Fin 2` both carry the eigenvalue `-1`.
  refine ⟨0, 1, by decide, ?_, ?_⟩ <;> norm_num [chapter13Exercise134Eigenvalue_eq_negOne]

end
