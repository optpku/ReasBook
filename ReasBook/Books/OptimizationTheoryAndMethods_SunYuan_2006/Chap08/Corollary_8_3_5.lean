/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_4

noncomputable section

section Chapter08Corollary835

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ
local notation "Multiplier" => Fin m → ℝ

namespace ConstrainedOptimizationProblem

-- Domain sampling:
-- * primary domain: second-order sufficient conditions for constrained nonlinear programming
-- * inspected owner declarations in the same chapter/project:
--   `ConstrainedOptimizationProblem.positiveActiveIneqIndexSet` from `Definition_8_3_1`
--   `ConstrainedOptimizationProblem.linearizedNullConstraintDirections` and
--   `mem_linearizedNullConstraintDirections_iff_explicit` from `Definition_8_3_2`
--   `ConstrainedOptimizationProblem.lagrangianHessianQuadratic` from `Theorem_8_3_3`
--   `isStrictLocalMinOn_of_positive_lagrangianHessian_on_linearizedNullConstraintDirections`
--   from `Theorem_8_3_4`
-- * owner abstraction chosen first: `problem.linearizedNullConstraintDirections xStar lamStar`
-- * layer targeted here: `bridge/view`; the corollary keeps the textbook `A₊`-style vanishing
--   hypotheses but reuses the canonical owner theorem instead of restating a parallel core API
-- * primitive data reused: KKT pair, active-set owners, linearized pairings, and the
--   Lagrangian Hessian quadratic form
-- * derived API here: only the source-facing bridge from the unpacked `A₊` conditions to the
--   canonical linearized-null-direction positivity hypothesis

/-- Chapter08 Corollary 8.3.5: under the `C²` hypotheses of Theorem 8.3.4, if `xStar` is a KKT
point of `problem` with multiplier vector `lamStar` and the Lagrangian Hessian quadratic form is
strictly positive on every nonzero direction whose equality-constraint pairings and strictly
positive active-inequality pairings vanish at `xStar`, then `xStar` is a strict local minimizer
of `problem.objective` on `problem.feasibleSet`. -/
theorem isStrictLocalMinOn_of_isKKTPoint_of_positive_lagrangianHessian_on_APlusDirections
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Multiplier) (h_kkt : problem.IsKKTPoint xStar lamStar)
    (h_objective : ContDiffAt ℝ 2 problem.objective xStar)
    (h_constraints : ∀ i, ContDiffAt ℝ 2 (problem.constraint i) xStar)
    (h_positive :
      ∀ d : Point,
        d ≠ 0 →
          (∀ i ∈ problem.eqIndices, problem.linearizedConstraintPairing xStar d i = 0) →
          (∀ i ∈ problem.positiveActiveIneqIndexSet xStar lamStar,
            problem.linearizedConstraintPairing xStar d i = 0) →
          0 < problem.lagrangianHessianQuadratic xStar lamStar d) :
    IsStrictLocalMinOn problem.objective problem.feasibleSet xStar := by
  -- Repackage the source-style `A₊` vanishing hypothesis as positivity on the canonical set
  -- `G(xStar, lamStar) = problem.linearizedNullConstraintDirections xStar lamStar`.
  have h_positiveG :
      ∀ d ∈ problem.linearizedNullConstraintDirections xStar lamStar,
        0 < problem.lagrangianHessianQuadratic xStar lamStar d := by
    intro d hd
    rcases (problem.mem_linearizedNullConstraintDirections_iff_explicit xStar lamStar d).1 hd with
      ⟨_, _, hd_nonzero, h_pairing_zero, _⟩
    exact h_positive d hd_nonzero
      (fun i hi ↦ h_pairing_zero i (Or.inl hi))
      (fun i hi ↦ h_pairing_zero i (Or.inr hi))
  -- The dependency theorem is exactly the second-order sufficient condition after this bridge.
  exact
    problem.isStrictLocalMinOn_of_positive_lagrangianHessian_on_linearizedNullConstraintDirections
      xStar lamStar h_kkt h_objective h_constraints h_positiveG

end ConstrainedOptimizationProblem

end Chapter08Corollary835
