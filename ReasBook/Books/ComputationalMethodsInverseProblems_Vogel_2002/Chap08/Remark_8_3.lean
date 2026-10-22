/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_2.Clauses
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_3.Clauses
import Mathlib.Topology.MetricSpace.Contracting

public section

universe u v

open scoped Matrix

/-!
Source note for this item. The current Chapter 8 API still lacks a checked
lagged-diffusivity self-map/run owner that would make the global-convergence
clause source-faithful. Accordingly the convergence sentence remains a labeled
blocker/check-only surface, while the Hessian-difference clause is stated
directly as a theorem. The final sentence about linear convergence remains
explanatory prose until precise rate hypotheses are supplied.
-/

/- Remark 8.3 (1). Main labeled source-facing blocker entry for the
global-convergence clause of the lagged-diffusivity fixed-point iteration.

The current repository snapshot still does not expose a checked
lagged-diffusivity self-map/iterate owner or the source-specific bridge from
`Matrix.PosDef (Kᵀ * K)` to a contractive iteration theorem. This labeled
`#check` therefore records only the verified backend convergence owner rather
than quantifying over an arbitrary self-map unsupported by the Chapter 8 API.
-/
#check ContractingWith.tendsto_iterate_fixedPoint

namespace TVLaggedDiffusivity

/-- Remark 8.3 (2). The true Hessian formula differs from the lagged-diffusivity
approximate Hessian formula by the correction term `α • L' (f v) (f v)`. This
bridge theorem reuses the Chapter 8 penalty-Hessian and exact-Hessian clause
owners together with the lagged-diffusivity approximate-Hessian owner. -/
theorem trueHessianFormula_eq_approximateHessianFormula_add_correction
    {κ : Type u} {ι : Type v}
    [Fintype κ]
    [DecidableEq κ]
    [Fintype ι]
    [DecidableEq ι]
    (K : Matrix κ ι ℝ)
    (α : ℝ)
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ)
    (f : ℕ → ι → ℝ)
    (Lv HJ HApprox HTrue : ℕ → Matrix ι ι ℝ)
    (h_diffusion : HasDiffusionAssignment L f Lv)
    (h_approximate : HasApproximateHessianFormula K α Lv HApprox)
    (h_penaltyHessian : TVNewton.HasPenaltyHessianFormula L L' f HJ)
    (h_true : TVNewton.HasHessianFormula K α HJ HTrue)
    (v : ℕ) :
    HTrue v = HApprox v + α • L' (f v) (f v) := by
  rw [TVNewton.HasHessianFormula.eq h_true v,
    TVNewton.HasPenaltyHessianFormula.eq h_penaltyHessian v,
    HasApproximateHessianFormula.eq h_approximate v,
    HasDiffusionAssignment.eq h_diffusion v]
  simp [smul_add, add_assoc]

end TVLaggedDiffusivity

/- Remark 8.3 (3). The correction term `α • L' (f v) (f v)` does not typically
vanish along the lagged-diffusivity iteration, so the expected convergence
rate is only heuristic here and is left as explanatory prose until explicit
rate hypotheses are formalized.
-/
