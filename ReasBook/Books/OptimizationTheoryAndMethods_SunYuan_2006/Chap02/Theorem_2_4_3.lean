/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_4_2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

open Filter

-- This file keeps only the convergence-order constant and the Chapter 2 bridge from the
-- source-facing recursive owner `quadraticInterpolationSequence` to the Chapter 1 owner
-- `HasQOrderConvergenceTo`.

/-- The convergence-order constant for three-point quadratic interpolation, characterized by
`t ^ 3 = t + 1` and lying in `Set.Icc (1 : ℝ) 2`. It is approximately `1.32`. -/
def quadraticInterpolationOrder : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc (1 : ℝ) 2 ∧ t ^ (3 : ℕ) ≤ t + 1}

/-- The constant `quadraticInterpolationOrder` lies in `Set.Icc (1 : ℝ) 2`. -/
theorem quadraticInterpolationOrder_mem_Icc :
    quadraticInterpolationOrder ∈ Set.Icc (1 : ℝ) 2 := sorry

/-- The constant `quadraticInterpolationOrder` is the real root of `t ^ 3 = t + 1`
in `Set.Icc (1 : ℝ) 2`. -/
theorem quadraticInterpolationOrder_isRoot :
    quadraticInterpolationOrder ^ (3 : ℕ) = quadraticInterpolationOrder + 1 := sorry

/-- The quadratic interpolation convergence-order constant satisfies
`1 ≤ quadraticInterpolationOrder`. -/
theorem quadraticInterpolationOrder_one_le :
    1 ≤ quadraticInterpolationOrder := sorry

/-- `IsValidQuadraticInterpolationRun φ α` records the textbook nondegeneracy conditions on every
three-point interpolation window of the generated run `α`. -/
structure IsValidQuadraticInterpolationRun (φ : ℝ → ℝ) (α : ℕ → ℝ) : Prop where
  left_ne_middle : ∀ k : ℕ, α k ≠ α (k + 1)
  left_ne_right : ∀ k : ℕ, α k ≠ α (k + 2)
  middle_ne_right : ∀ k : ℕ, α (k + 1) ≠ α (k + 2)
  stepDenominator_ne_zero :
    ∀ k : ℕ,
      quadraticInterpolationStepDenominator φ (α k) (α (k + 1)) (α (k + 2)) ≠ 0

/-- `IsQuadraticInterpolationQOrderBasin φ αStar δ` means that the radius `δ` is an admissible
local basin for Theorem 2.4.3: every valid quadratic-interpolation run generated from an initial
triple inside that radius has `Q`-order `quadraticInterpolationOrder`. -/
private structure IsQuadraticInterpolationQOrderBasin
    (φ : ℝ → ℝ) (αStar δ : ℝ) : Prop where
  pos : 0 < δ
  hasQOrderConvergenceTo
      {a₀ a₁ a₂ : ℝ} :
    |a₀ - αStar| < δ →
    |a₁ - αStar| < δ →
    |a₂ - αStar| < δ →
    IsValidQuadraticInterpolationRun φ (quadraticInterpolationSequence φ a₀ a₁ a₂) →
    ∃ β : ℝ,
      HasQOrderConvergenceTo
        (quadraticInterpolationSequence φ a₀ a₁ a₂)
        αStar quadraticInterpolationOrder β

/-- Chapter02 Theorem 2.4.3 supplies a positive local basin around `αStar` in which every valid
quadratic-interpolation run has `Q`-order `quadraticInterpolationOrder`. -/
private theorem quadraticInterpolation_qOrderBasin
    (φ : ℝ → ℝ) (αStar : ℝ)
    (h_smooth : ContDiffAt ℝ 4 φ αStar)
    (h_stationary : deriv φ αStar = 0)
    (h_nondegenerate : iteratedDeriv 2 φ αStar ≠ 0) :
    ∃ δ : ℝ, IsQuadraticInterpolationQOrderBasin φ αStar δ := sorry

/-- Chapter02 Theorem 2.4.3: if `φ : ℝ → ℝ` is `ContDiffAt ℝ 4` at `αStar` and `αStar` is a
nondegenerate stationary point of `φ`, then there is a positive neighborhood of `αStar` such
that every valid quadratic-interpolation sequence generated from an initial triple in that
neighborhood converges to `αStar` with `Q`-order `quadraticInterpolationOrder`. -/
theorem quadraticInterpolation_hasQOrderConvergenceTo
    (φ : ℝ → ℝ) (αStar : ℝ)
    (h_smooth : ContDiffAt ℝ 4 φ αStar)
    (h_stationary : deriv φ αStar = 0)
    (h_nondegenerate : iteratedDeriv 2 φ αStar ≠ 0) :
    ∃ δ > 0, ∀ a₀ a₁ a₂ : ℝ,
      let α := quadraticInterpolationSequence φ a₀ a₁ a₂
      |a₀ - αStar| < δ →
      |a₁ - αStar| < δ →
      |a₂ - αStar| < δ →
      IsValidQuadraticInterpolationRun φ α →
      ∃ β : ℝ, HasQOrderConvergenceTo α αStar quadraticInterpolationOrder β := by
  rcases quadraticInterpolation_qOrderBasin φ αStar h_smooth h_stationary h_nondegenerate with
    ⟨δ, hδ⟩
  refine ⟨δ, hδ.pos, ?_⟩
  intro a₀ a₁ a₂ α ha₀ ha₁ ha₂ h_valid
  exact hδ.hasQOrderConvergenceTo ha₀ ha₁ ha₂ h_valid
