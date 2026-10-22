/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: the Chapter 2 owner for admissible Wolfe-Powell parameters is
-- `WolfePowellParameters ρ σ`, and the one-dimensional acceptance predicate
-- `WolfePowellCondition φ φ' ρ σ α` derives its parameter data from that owner.
-- Nearby Chapter 2 files such as `Lemma_2_5_6` and `Exercise_2_9` already reuse
-- this owner abstraction directly. This exercise is source-facing existence data
-- for a one-dimensional line-search profile, with admissible Wolfe parameters
-- kept explicit in the theorem header rather than only inside the negated
-- acceptance predicate.

/-- Helper for Chapter02 Exercise 2.7: the derivative of the affine profile
`α ↦ -α` is constantly `-1`. -/
lemma deriv_neg_id_eq (x : ℝ) :
    deriv (fun t : ℝ ↦ -t) x = -1 := by
  -- Normalize the derivative of the chosen counterexample profile once and for all.
  exact deriv_neg'' (𝕜 := ℝ) (x := x)

/-- Helper for Chapter02 Exercise 2.7: any Wolfe step for the profile `α ↦ -α`
would force the curvature parameter `σ` to satisfy `1 ≤ σ`. -/
lemma wolfe_curvature_implies_sigma_ge_one_for_neg_id
    {ρ σ α : ℝ}
    (h_wolfe_step : WolfePowellCondition (fun t : ℝ ↦ -t) (deriv (fun t : ℝ ↦ -t)) ρ σ α) :
    1 ≤ σ := by
  rcases wolfePowellCondition_iff.mp h_wolfe_step with ⟨_, _, _, h_curvature⟩
  -- Only the curvature clause matters for this constant-slope profile.
  have h_curvature' : σ * (-1 : ℝ) ≤ (-1 : ℝ) := by
    simpa [deriv_neg_id_eq] using h_curvature
  -- Rewriting `σ * (-1)` as `-σ` exposes the contradiction with `σ < 1`.
  have h_neg : -σ ≤ (-1 : ℝ) := by
    simpa using h_curvature'
  exact neg_le_neg_iff.mp h_neg

/-- Helper for Chapter02 Exercise 2.7: if `σ < 1`, then the profile `α ↦ -α`
admits no Wolfe-Powell steplength. -/
lemma no_wolfe_step_for_neg_id
    {ρ σ : ℝ}
    (h_sigma_lt_one : σ < 1) :
    ∀ α : ℝ, ¬ WolfePowellCondition (fun t : ℝ ↦ -t) (deriv (fun t : ℝ ↦ -t)) ρ σ α := by
  intro α h_wolfe_step
  -- The curvature bound would force `σ ≥ 1`, contradicting the parameter range.
  have h_sigma_ge_one : 1 ≤ σ :=
    wolfe_curvature_implies_sigma_ge_one_for_neg_id h_wolfe_step
  exact (not_lt_of_ge h_sigma_ge_one) h_sigma_lt_one

/-- Chapter02 Exercise 2.7: there exists a differentiable line-search profile
`φ : ℝ → ℝ` for which no steplength satisfies the Wolfe rule with parameters
`ρ` and `σ`, assuming the Wolfe-Powell parameters are admissible:
`0 < ρ < σ < 1`. -/
theorem existsLineSearchProfileWithoutWolfeStep
    (ρ σ : ℝ)
    (h_wolfe : WolfePowellParameters ρ σ) :
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      ∀ α : ℝ, ¬ WolfePowellCondition φ (deriv φ) ρ σ α := by
  refine ⟨fun α ↦ -α, ?_, ?_⟩
  · -- The counterexample profile is the negation map, hence differentiable everywhere.
    simpa using (differentiable_neg : Differentiable ℝ (Neg.neg : ℝ → ℝ))
  · -- Once `σ < 1` is read from the parameter owner, the curvature clause rules out every step.
    exact no_wolfe_step_for_neg_id h_wolfe.sigma_lt_one
