/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.InitialSublevelSet
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_5_5

open Filter
open scoped Gradient

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling:
-- * project Wolfe-Powell owner for admissible parameters: `WolfePowellParameters`;
-- * project owner for the source-facing cosine-limit statement:
--   `wolfePowellLineSearch_gradientNorm_mul_cos_angle_tendsto_zero`;
-- * project bridge/view companion for the ratio-limit statement:
--   `wolfePowellLineSearch_gradientInner_div_searchDirectionNorm_tendsto_zero`;
-- * mathlib bridge from a Lipschitz-on-set hypothesis to the owner theorem's
--   uniform-continuity hypothesis: `LipschitzOnWith.uniformContinuousOn`.
-- Primitive data here are the iterate/update sequences, the descent inequality, the per-step
-- one-dimensional owner `WolfePowellCondition` on the canonical search-ray owner
-- `lineSearchObjective f (x k) (s k)`, and the Lipschitz-on-`initialSublevelSet f (x 0)`
-- hypothesis.
-- The limit conclusions are derived API obtained by reusing the Chapter 2 Wolfe-Powell owners,
-- so this file remains a bridge/view layer rather than a new owner abstraction.

/-- Chapter02 Exercise 2.9: if `f : E → ℝ` on a real Hilbert space `E` is continuously
differentiable and bounded below, `gradient f` is Lipschitz on the initial sublevel set
`initialSublevelSet f (x 0)`, and the iterates satisfy the Wolfe-Powell rule with parameters `ρ, σ`,
then `(inner ℝ (gradient f (x k)) (s k)) / ‖s k‖ → 0`. -/
theorem wolfePowell_gradientInner_div_searchDirectionNorm_tendsto_zero
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_bddBelow : BddBelow (Set.range f))
    (h_gradLipschitz :
      ∃ L : NNReal, LipschitzOnWith L (∇ f) (initialSublevelSet f (x 0)))
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    Tendsto (fun k : ℕ ↦ inner ℝ (∇ f (x k)) (s k) / ‖s k‖) atTop (nhds 0) := by
  have h_hasGradient :
      ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y := fun y _ ↦
    ((show ContDiffAt ℝ 1 f y from h_contDiff.contDiffAt).differentiableAt_one).hasGradientAt
  rcases h_gradLipschitz with ⟨L, hL⟩
  exact wolfePowellLineSearch_gradientInner_div_searchDirectionNorm_tendsto_zero
    f x s α ρ σ h_bddBelow h_hasGradient hL.uniformContinuousOn
    h_update h_descent h_wolfeStep

/-- Chapter02 Exercise 2.9: under the same hypotheses, the source-facing cosine
formulation from Chapter 2,
`‖gradient f (x k)‖ * Real.cos (InnerProductGeometry.angle (s k) (-gradient f (x k)))`,
tends to `0`. -/
theorem wolfePowell_gradientNorm_mul_cos_angle_tendsto_zero
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_contDiff : ContDiff ℝ 1 f)
    (h_bddBelow : BddBelow (Set.range f))
    (h_gradLipschitz :
      ∃ L : NNReal, LipschitzOnWith L (∇ f) (initialSublevelSet f (x 0)))
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    Tendsto
      (fun k : ℕ ↦
        ‖∇ f (x k)‖ * Real.cos (InnerProductGeometry.angle (s k) (-∇ f (x k))))
      atTop
      (nhds 0) := by
  have h_hasGradient :
      ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y := fun y _ ↦
    ((show ContDiffAt ℝ 1 f y from h_contDiff.contDiffAt).differentiableAt_one).hasGradientAt
  rcases h_gradLipschitz with ⟨L, hL⟩
  exact wolfePowellLineSearch_gradientNorm_mul_cos_angle_tendsto_zero
    f x s α ρ σ h_bddBelow h_hasGradient hL.uniformContinuousOn
    h_update h_descent h_wolfeStep

end
