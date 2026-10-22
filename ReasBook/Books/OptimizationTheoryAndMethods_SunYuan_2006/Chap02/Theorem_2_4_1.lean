/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.NumberTheory.Real.GoldenRatio

noncomputable section

-- Source/core/bridge triage:
-- * source-facing owner: `interpolationSecantSequence φ a₀ a₁`, the recursively generated
--   interpolation-secant sequence from its initial pair;
-- * core/canonical owner: Chapter 1's `HasQOrderConvergenceTo`;
-- * bridge theorem: `interpolationSecant_hasQOrderConvergenceTo_goldenRatio`.

/-- The denominator in the interpolation-secant update `(2.4.6)` applied to the current pair
`(a₀, a₁)`. -/
def interpolationSecantStepDenominator (φ : ℝ → ℝ) (a₀ a₁ : ℝ) : ℝ :=
  deriv φ a₁ - deriv φ a₀

/-- The interpolation-secant update `(2.4.6)` applied to the current pair `(a₀, a₁)`. -/
def interpolationSecantStep (φ : ℝ → ℝ) (a₀ a₁ : ℝ) : ℝ :=
  a₁ - deriv φ a₁ * (a₁ - a₀) / interpolationSecantStepDenominator φ a₀ a₁

/-- The recursively generated interpolation-secant sequence attached to the initial pair
`(a₀, a₁)`. -/
def interpolationSecantSequence (φ : ℝ → ℝ) (a₀ a₁ : ℝ) : ℕ → ℝ
  | 0 => a₀
  | 1 => a₁
  | n + 2 =>
      interpolationSecantStep φ
        (interpolationSecantSequence φ a₀ a₁ n)
        (interpolationSecantSequence φ a₀ a₁ (n + 1))

@[simp] theorem interpolationSecantSequence_zero
    (φ : ℝ → ℝ) (a₀ a₁ : ℝ) :
    interpolationSecantSequence φ a₀ a₁ 0 = a₀ := rfl

@[simp] theorem interpolationSecantSequence_one
    (φ : ℝ → ℝ) (a₀ a₁ : ℝ) :
    interpolationSecantSequence φ a₀ a₁ 1 = a₁ := rfl

/-- The recursive step relation for `interpolationSecantSequence`. -/
theorem interpolationSecantSequence_step_eq
    (φ : ℝ → ℝ) (a₀ a₁ : ℝ) (n : ℕ) :
    interpolationSecantSequence φ a₀ a₁ (n + 2) =
      interpolationSecantStep φ
        (interpolationSecantSequence φ a₀ a₁ n)
        (interpolationSecantSequence φ a₀ a₁ (n + 1)) := rfl

/-- Any sequence satisfying the interpolation-secant recurrence is the canonical recursively
generated interpolation-secant sequence from its first two terms. -/
theorem eq_interpolationSecantSequence_of_step_eq
    {φ : ℝ → ℝ} {α : ℕ → ℝ}
    (h_step :
      ∀ k : ℕ,
        α (k + 2) = interpolationSecantStep φ (α k) (α (k + 1))) :
    α = interpolationSecantSequence φ (α 0) (α 1) := by
  funext n
  exact Nat.twoStepInduction rfl rfl (fun k hk hk1 ↦ by
    rw [h_step k, interpolationSecantSequence_step_eq, hk, hk1]) n

/-- Chapter02 Theorem 2.4.1: if `φ : ℝ → ℝ` is `ContDiffAt ℝ 3` at `αStar` and `αStar` is a
nondegenerate stationary point of `φ`, then there is a positive neighborhood of `αStar` such
that the recursively generated interpolation-secant sequence from any initial pair in that
neighborhood converges to `αStar` with `Q`-order `Real.goldenRatio = (1 + √5) / 2`, provided
each secant denominator is nonzero. -/
theorem interpolationSecant_hasQOrderConvergenceTo_goldenRatio
    (φ : ℝ → ℝ) (αStar : ℝ)
    (h_smooth : ContDiffAt ℝ 3 φ αStar)
    (h_stationary : deriv φ αStar = 0)
    (h_nondegenerate : iteratedDeriv 2 φ αStar ≠ 0) :
    ∃ δ > 0, ∀ a₀ a₁ : ℝ,
      let α := interpolationSecantSequence φ a₀ a₁
      |a₀ - αStar| < δ →
      |a₁ - αStar| < δ →
      (∀ k : ℕ, interpolationSecantStepDenominator φ (α k) (α (k + 1)) ≠ 0) →
      ∃ β : ℝ, HasQOrderConvergenceTo α αStar Real.goldenRatio β := sorry
