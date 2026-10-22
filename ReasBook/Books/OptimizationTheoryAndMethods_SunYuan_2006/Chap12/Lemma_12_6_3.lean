/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Assumption_12_6_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_6_extra_1

noncomputable section

open Asymptotics Filter

section Chapter12Lemma1263

variable {Point Multiplier : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [CompleteSpace Point]
variable [NormedAddCommGroup Multiplier] [InnerProductSpace ℝ Multiplier]
  [CompleteSpace Multiplier]

-- Domain sampling:
-- * primary domain: Section 12.6 second-order correction subproblems and the quadratic-size
--   estimate for their chosen least-norm minimizers in real inner-product spaces;
-- * sampled owner declarations:
--   `isSqpSubproblemSolution`,
--   `IsSecondOrderCorrectionSubproblemSolution`,
--   `secondOrderCorrectionUniformModelBounds`,
--   and `Asymptotics.IsBigO`;
-- * best owner abstraction: `IsSecondOrderCorrectionSubproblemSolution` is the primitive
--   correction-subproblem owner, while the quadratic residual-size and correction-size bounds
--   should both use the canonical asymptotic owner `Asymptotics.IsBigO`;
-- * source/core/bridge triage:
--   - source-facing item here: Lemma 12.6.3, the quadratic correction estimate;
--   - core/canonical owners: `isSqpSubproblemSolution`,
--     `IsSecondOrderCorrectionSubproblemSolution`, and
--     `secondOrderCorrectionUniformModelBounds`;
--   - bridge/view: the threshold estimate and the residual hypothesis are both expressed through
--     `Asymptotics.IsBigO`;
-- * primitive data vs derived API: the primitive correction-step hypothesis is that `dHat k`
--   solves the correction subproblem, while the least-norm selection among all such minimizers is
--   extra source-facing data; the quadratic residual bound on `c (x k + d k)` and the
--   asymptotic bound on `‖dHat k‖` are derived API.

section

variable
    (x : ℕ → Point)
    (xStar : Point)
    (g : ℕ → Point)
    (c : Point → Multiplier)
    (A : Point → Multiplier →L[ℝ] Point)
    (B : ℕ → Point →L[ℝ] Point)
    (d dHat : ℕ → Point)

/-- Chapter12 Lemma 12.6.3: under the conditions of Assumption 12.6.1, if `d_k` is the base
SQP step, `dHat_k` solves the second-order correction subproblem `(12.6.3)`-`(12.6.4)`,
`dHat_k` is chosen with least norm among all such minimizers as in `(12.6.5)`, and
the next-constraint residual `c (x_k + d_k)` is quadratically small in `d_k`, then there exist a
positive constant `etaBar` and a threshold `K` such that for every `k ≥ K`,
`‖dHat_k‖ ≤ etaBar * ‖d_k‖^2`, matching the eventual quadratic estimate `(12.6.22)`. -/
theorem exists_eventually_norm_secondOrderCorrection_le_mul_sq_norm
    (hConverge : secondOrderCorrectionIteratesConverge x xStar)
    (hFullColumnRank : secondOrderCorrectionJacobianHasFullColumnRankAt A xStar)
    (hUniformBounds : secondOrderCorrectionUniformModelBounds x A B)
    (hBaseStep :
      ∀ k : ℕ,
        isSqpSubproblemSolution (g k) (B k) (A (x k)) (c (x k)) (d k))
    (hCorrectionSolution :
      ∀ k : ℕ,
        IsSecondOrderCorrectionSubproblemSolution
          (g k) (d k) (B k) (A (x k)) (c (x k + d k)) (dHat k))
    (hCorrectionLeastNorm :
      ∀ k : ℕ, ∀ d' : Point,
        IsSecondOrderCorrectionSubproblemSolution
            (g k) (d k) (B k) (A (x k)) (c (x k + d k)) d' →
          ‖dHat k‖ ≤ ‖d'‖)
    (hNextResidual :
      IsBigO atTop (fun k ↦ ‖c (x k + d k)‖) (fun k ↦ ‖d k‖ ^ (2 : ℕ))) :
    ∃ etaBar : ℝ,
      0 < etaBar ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ‖dHat k‖ ≤ etaBar * ‖d k‖ ^ (2 : ℕ) := sorry

/-- The eventual threshold estimate of Lemma 12.6.3 has the canonical asymptotic companion
`IsBigO atTop (fun k ↦ ‖dHat k‖) (fun k ↦ ‖d k‖^2)`. -/
theorem secondOrderCorrection_isBigO_sq_norm
    (hConverge : secondOrderCorrectionIteratesConverge x xStar)
    (hFullColumnRank : secondOrderCorrectionJacobianHasFullColumnRankAt A xStar)
    (hUniformBounds : secondOrderCorrectionUniformModelBounds x A B)
    (hBaseStep :
      ∀ k : ℕ,
        isSqpSubproblemSolution (g k) (B k) (A (x k)) (c (x k)) (d k))
    (hCorrectionSolution :
      ∀ k : ℕ,
        IsSecondOrderCorrectionSubproblemSolution
          (g k) (d k) (B k) (A (x k)) (c (x k + d k)) (dHat k))
    (hCorrectionLeastNorm :
      ∀ k : ℕ, ∀ d' : Point,
        IsSecondOrderCorrectionSubproblemSolution
            (g k) (d k) (B k) (A (x k)) (c (x k + d k)) d' →
          ‖dHat k‖ ≤ ‖d'‖)
    (hNextResidual :
      IsBigO atTop (fun k ↦ ‖c (x k + d k)‖) (fun k ↦ ‖d k‖ ^ (2 : ℕ))) :
    IsBigO atTop (fun k ↦ ‖dHat k‖) (fun k ↦ ‖d k‖ ^ (2 : ℕ)) := by
  rcases exists_eventually_norm_secondOrderCorrection_le_mul_sq_norm
      x xStar g c A B d dHat
      hConverge hFullColumnRank hUniformBounds hBaseStep
      hCorrectionSolution hCorrectionLeastNorm hNextResidual with
    ⟨etaBar, _, K, hEtaBar⟩
  refine IsBigO.of_bound etaBar ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨K, hEtaBar⟩] with k hk
  simpa only [Real.norm_eq_abs, abs_of_nonneg, norm_nonneg, pow_nonneg] using hk

end

end Chapter12Lemma1263
