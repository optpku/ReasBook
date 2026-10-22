/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_1

section

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * primary domain: lower level sets and trust-region assumption packages on `ℝ^n`;
-- * inspected owner declarations in this domain:
--   - `lowerLevelSetOn` / `mem_lowerLevelSetOn` in Chapter 1 for the canonical lower-level-set
--     owner, with the `Set.univ` specialization handled directly by `simp`;
--   - `quasiNewtonLevelSet` in Chapter 5 as an example of a source-facing bridge to that owner.
-- * best owner abstraction: the Chapter 6 level set is not a new owner; it is exactly
--   `lowerLevelSetOn Set.univ f x0`.
-- * layer targeted here: `source-facing`, since `TrustRegionAssumptionA0` is the Chapter 6
--   assumption package, but its level-set fields should live directly over the canonical owner.
-- Primitive data vs derived API:
-- * primitive data: the subproblem sequence, its uniform Hessian-operator-norm bound,
--   boundedness and `ContDiffOn` on the canonical lower level set `lowerLevelSetOn Set.univ f x0`,
--   and the step-size bound `‖s_k‖ ≤ η̃ * Δ_k`;
-- * derived API: only genuinely new consequences of `(A₀)`, such as the nonnegative uniform
--   Hessian bound below; owner facts already provided by `TrustRegionSubproblem.radius_pos` and
--   the direct `Set.univ` lower-level-set simp facts, and exact field projections, should not
--   be restated here.

/-- Chapter06 Assumption 6.1-extra-2: the stage subproblems `P_k` have uniformly bounded
Hessian operator norms `‖B_k‖₂ = P_k.hessianOperatorNorm`, the level set `{x | f x ≤ f x0}`
is bounded and `f` is continuously differentiable on it, and the approximate subproblem
solutions satisfy `‖s_k‖ ≤ η̃ * Δ_k` for a positive constant `η̃`, where `Δ_k = P_k.radius`.
The source-side fact that `s_k` is an approximate solution of the already-fixed subproblem
`(6.1.1)` remains ambient context, rather than part of the packaged assumptions `(A₀)` in
Section 6.1. -/
class TrustRegionAssumptionA0
    (f : Point → ℝ) (x0 : Point) (subproblem : ℕ → TrustRegionSubproblem n)
    (s : ℕ → Point) : Prop where
  hessianOperatorNorm_bounded :
    ∃ hessianBound : ℝ, ∀ k : ℕ, (subproblem k).hessianOperatorNorm ≤ hessianBound
  levelSet_bounded : Bornology.IsBounded (lowerLevelSetOn Set.univ f x0)
  contDiffOn_levelSet : ContDiffOn ℝ 1 f (lowerLevelSetOn Set.univ f x0)
  step_norm_bounded :
    ∃ etaTilde > 0, ∀ k : ℕ, ‖s k‖ ≤ etaTilde * (subproblem k).radius

namespace TrustRegionAssumptionA0

variable {f : Point → ℝ} {x0 : Point} {subproblem : ℕ → TrustRegionSubproblem n}
  {s : ℕ → Point}

/-- The uniform Hessian-operator-norm bound in `TrustRegionAssumptionA0` forces the bound
constant to be nonnegative. -/
theorem hessianBound_nonneg (hA0 : TrustRegionAssumptionA0 f x0 subproblem s) :
    ∃ hessianBound : ℝ,
      0 ≤ hessianBound ∧ ∀ k : ℕ, (subproblem k).hessianOperatorNorm ≤ hessianBound := by
  rcases hA0.hessianOperatorNorm_bounded with ⟨hessianBound, hhessianBound⟩
  refine ⟨hessianBound, ?_, hhessianBound⟩
  exact le_trans
    (by
      simp [TrustRegionSubproblem.hessianOperatorNorm_eq])
    (hhessianBound 0)

end TrustRegionAssumptionA0

#print axioms TrustRegionAssumptionA0

end
