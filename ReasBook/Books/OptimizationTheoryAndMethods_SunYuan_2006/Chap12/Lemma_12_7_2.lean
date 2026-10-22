/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Algorithm_12_7_1

noncomputable section

open Filter

section Chapter12Lemma1272

/-- The `n`-dimensional Euclidean space used for iterates and search directions. -/
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n m : ℕ}

-- Domain sampling for this file:
-- * primary domain: Section 12.7 Powell-Yuan smooth exact penalty SQP iterates;
-- * sampled owner declarations:
--   `PowellYuanMethod.acceptedPenaltyParameter`,
--   `PowellYuanMethod.hessianOperator`,
--   `Bornology.IsBounded`,
--   and `SmoothExactPenaltyMethod`;
-- * source-facing layer here: the continuous-linear-map method owner and the eventual
--   penalty-parameter stabilization statement of Lemma 12.7.2;
-- * core/canonical layer reused here: `Bornology.IsBounded` for bounded ranges and the
--   Section 12.7 algorithm owner from `Algorithm_12_7_1`;
-- * bridge/view layer here: `method.hessianOperator` and `method.constraintJacobian`, the
--   continuous-linear-map surfaces used for formulas of the form `A(x)ᵀ d = 0`.

/-- `PenaltyParameterStabilizesAt method k'` records that the accepted penalty parameters of
`method` agree from stage `k'` onward with the positive carry-over parameter at stage `k'`. -/
structure PenaltyParameterStabilizesAt
    (method : SmoothExactPenaltyMethod n m) (k' : ℕ) : Prop where
  sigmaStart_pos : 0 < method.sigmaStart k'
  eventually_eq :
    ∀ k : ℕ, k' ≤ k →
      method.acceptedPenaltyParameter k = method.sigmaStart k'

/-- Chapter12 Lemma 12.7.2 (1): assume that the iterate sequence `x_k`, the search directions
`d_k`, and the Hessian models `B_k` of the Section 12.7 Powell-Yuan smooth exact penalty method
`method` are bounded. If `A(x)` is full column rank for every `x ∈ ℝ^n`, encoded as injectivity
of `constraintJacobian x`, and if there exists `δ > 0` such that
`δ * ‖d‖^2 ≤ ⟪d, B_k d⟫` for every `k` and every direction satisfying `A(x_k)ᵀ d = 0`, then
there exists a positive integer `k'` such that the accepted penalty parameter
`σ_(k, i_k) = σ_(k',-1) = σbar > 0` for all `k ≥ k'`. -/
theorem penaltyParameters_eventuallyConstant_of_bounded
    (method : SmoothExactPenaltyMethod n m)
    (hx_bounded : Bornology.IsBounded (Set.range method.iterate))
    (hd_bounded : Bornology.IsBounded (Set.range method.searchDirection))
    (hB_bounded : Bornology.IsBounded (Set.range method.hessianOperator))
    (hA_fullColumnRank : ∀ x : Point n, Function.Injective (method.constraintJacobian x))
    {δ : ℝ} (hδ : 0 < δ)
    (hNullspaceCurvature :
      ∀ k : ℕ, ∀ d : Point n,
        ContinuousLinearMap.adjoint (method.constraintJacobian (method.iterate k)) d = 0 →
          δ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (method.hessianOperator k d)) :
    ∃ k' : ℕ,
      0 < k' ∧ PenaltyParameterStabilizesAt method k' := sorry

/-- Chapter12 Lemma 12.7.2 (2): under the same boundedness, full-column-rank, and nullspace
curvature hypotheses as part (1), the search-direction norms of the Section 12.7 Powell-Yuan
smooth exact penalty method satisfy `‖d_k‖ ⟶ 0`. -/
theorem searchDirectionNorm_tendsto_zero_of_bounded
    (method : SmoothExactPenaltyMethod n m)
    (hx_bounded : Bornology.IsBounded (Set.range method.iterate))
    (hd_bounded : Bornology.IsBounded (Set.range method.searchDirection))
    (hB_bounded : Bornology.IsBounded (Set.range method.hessianOperator))
    (hA_fullColumnRank : ∀ x : Point n, Function.Injective (method.constraintJacobian x))
    {δ : ℝ} (hδ : 0 < δ)
    (hNullspaceCurvature :
      ∀ k : ℕ, ∀ d : Point n,
        ContinuousLinearMap.adjoint (method.constraintJacobian (method.iterate k)) d = 0 →
          δ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (method.hessianOperator k d)) :
    Tendsto (fun k : ℕ ↦ ‖method.searchDirection k‖) atTop (nhds (0 : ℝ)) := sorry
end Chapter12Lemma1272
