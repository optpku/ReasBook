/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

section

variable {n : ℕ}

local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin 1)

-- Domain sampling:
-- * primary domain: Chapter 10 penalty functions for `StandardPenaltyProblem`
-- * inspected owner/canonical declarations:
--   `StandardPenaltyProblem.constraintViolation` in `Definition_10_1_extra_1`,
--   `PenaltyFunction` in `Definition_10_1_extra_1`,
--   `PenaltyFunction.nonsmoothExact` in `Definition_10_6_extra_1`,
--   `Real.exp_zero` in mathlib as the canonical normalization fact for the scalar kernel
-- * best owner abstraction: `PenaltyFunction`; this file should reuse that owner rather than
--   re-declaring problem and penalty structures
-- * primitive data vs. derived API:
--   primitive Chapter 10 data are the imported problem fields and `PenaltyFunction.penaltyTerm`;
--   the exponential kernel `c ↦ exp (c 0)` is only a local bridge used to negate the
--   normalization axiom `penaltyTerm_zero`

/-- Chapter10 Exercise 10.6: in the Definition 10.1 penalty-function surface `(10.1.10)`, the
choice `h(c) = exp c` is not an admissible penalty term, since its one-dimensional Chapter 10
bridge does not satisfy the required normalization at `0`. -/
theorem chapter10Exercise106_exponentialScalar_not_admissiblePenaltyTerm
    (problem : StandardPenaltyProblem n 1) :
    ¬ ∃ P : PenaltyFunction problem,
        P.penaltyTerm = (fun c : ConstraintPoint ↦ Real.exp (c 0)) := by
  rintro ⟨P, hP⟩
  have hzero : (fun c : ConstraintPoint ↦ Real.exp (c 0)) 0 = 0 := by
    simpa [hP] using P.penaltyTerm_zero
  simp at hzero

#print axioms chapter10Exercise106_exponentialScalar_not_admissiblePenaltyTerm

end
