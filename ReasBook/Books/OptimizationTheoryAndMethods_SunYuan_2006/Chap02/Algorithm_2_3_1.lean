/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Interval.Set.Basic

/-- The nonterminal Step 3 update used when `phiLam k > phiMu k`. -/
structure GoldenSectionMethod.RightCaseUpdate
    (φ : ℝ → ℝ) (δ : ℝ) (a b lam mu phiLam phiMu : ℕ → ℝ) (k : ℕ) : Prop where
  continueCondition : δ < b k - lam k
  next_a : a (k + 1) = lam k
  next_b : b (k + 1) = b k
  next_lam : lam (k + 1) = mu k
  next_phiLam : phiLam (k + 1) = phiMu k
  next_mu :
    mu (k + 1) =
      a (k + 1) + Real.goldenRatio⁻¹ * (b (k + 1) - a (k + 1))
  next_phiMu : phiMu (k + 1) = φ (mu (k + 1))

/-- The nonterminal Step 4 update used when `phiLam k ≤ phiMu k`. -/
structure GoldenSectionMethod.LeftCaseUpdate
    (φ : ℝ → ℝ) (δ : ℝ) (a b lam mu phiLam phiMu : ℕ → ℝ) (k : ℕ) : Prop where
  continueCondition : δ < mu k - a k
  next_a : a (k + 1) = a k
  next_b : b (k + 1) = mu k
  next_mu : mu (k + 1) = lam k
  next_phiMu : phiMu (k + 1) = phiLam k
  next_lam :
    lam (k + 1) =
      a (k + 1) + (1 - Real.goldenRatio⁻¹) * (b (k + 1) - a (k + 1))
  next_phiLam : phiLam (k + 1) = φ (lam (k + 1))

/-- The terminal output data in the branch `phiLam k > phiMu k`. -/
structure GoldenSectionMethod.RightCaseStop
    (δ output : ℝ) (b lam mu : ℕ → ℝ) (k : ℕ) : Prop where
  stop : b k - lam k ≤ δ
  output_eq : output = mu k

/-- The terminal output data in the branch `phiLam k ≤ phiMu k`. -/
structure GoldenSectionMethod.LeftCaseStop
    (δ output : ℝ) (a lam mu : ℕ → ℝ) (k : ℕ) : Prop where
  stop : mu k - a k ≤ δ
  output_eq : output = lam k

/-- Chapter02 Algorithm 2.3.1: a terminated golden section search run for a
one-dimensional objective `φ`.

The data consist of a precision `δ > 0`, interval endpoints `a k`, `b k`, interior
observations `lam k`, `mu k`, and the cached function values `phiLam k = φ (lam k)` and
`phiMu k = φ (mu k)`. At `k = 1`, the observations are placed using the exact
golden-section weights `1 - Real.goldenRatio⁻¹` and `Real.goldenRatio⁻¹`, whose decimal
approximations are `0.382` and `0.618`. For each `k < terminalIndex`, the method compares
`phiLam k` and `phiMu k`: if `phiLam k > phiMu k`, then the right-case update of Step 3
is used and the nonterminal condition is `δ < b k - lam k`; if `phiLam k ≤ phiMu k`,
then the left-case update of Step 4 is used and the nonterminal condition is
`δ < mu k - a k`. At `terminalIndex`, the run stops with output `mu terminalIndex` in
the right branch and `lam terminalIndex` in the left branch. -/
structure GoldenSectionMethod (φ : ℝ → ℝ) where
  δ : ℝ
  terminalIndex : ℕ
  a : ℕ → ℝ
  b : ℕ → ℝ
  lam : ℕ → ℝ
  mu : ℕ → ℝ
  phiLam : ℕ → ℝ
  phiMu : ℕ → ℝ
  output : ℝ
  delta_pos : 0 < δ
  one_le_terminalIndex : 1 ≤ terminalIndex
  initialInterval : a 1 ≤ b 1
  initialLam :
    lam 1 = a 1 + (1 - Real.goldenRatio⁻¹) * (b 1 - a 1)
  initialMu :
    mu 1 = a 1 + Real.goldenRatio⁻¹ * (b 1 - a 1)
  phiLam_eval :
    ∀ k : ℕ, 1 ≤ k → k ≤ terminalIndex → phiLam k = φ (lam k)
  phiMu_eval :
    ∀ k : ℕ, 1 ≤ k → k ≤ terminalIndex → phiMu k = φ (mu k)
  rightCaseStep :
    ∀ k : ℕ, 1 ≤ k → k < terminalIndex → phiLam k > phiMu k →
      GoldenSectionMethod.RightCaseUpdate φ δ a b lam mu phiLam phiMu k
  leftCaseStep :
    ∀ k : ℕ, 1 ≤ k → k < terminalIndex → phiLam k ≤ phiMu k →
      GoldenSectionMethod.LeftCaseUpdate φ δ a b lam mu phiLam phiMu k
  rightCaseStop :
    phiLam terminalIndex > phiMu terminalIndex →
      GoldenSectionMethod.RightCaseStop δ output b lam mu terminalIndex
  leftCaseStop :
    phiLam terminalIndex ≤ phiMu terminalIndex →
      GoldenSectionMethod.LeftCaseStop δ output a lam mu terminalIndex

namespace GoldenSectionMethod

/-- Step indices of a golden section run are the integers from `1` through
`terminalIndex`. -/
instance {φ : ℝ → ℝ} : Membership ℕ (GoldenSectionMethod φ) where
  mem A k := 1 ≤ k ∧ k ≤ A.terminalIndex

/-- A natural number belongs to a golden section run exactly when it indexes one of
its recorded steps. -/
theorem mem_iff {φ : ℝ → ℝ} (A : GoldenSectionMethod φ) (k : ℕ) :
    k ∈ A ↔ 1 ≤ k ∧ k ≤ A.terminalIndex :=
  Iff.rfl

/-- The search interval `[a_k, b_k]` carried by a golden section run at step `k`. -/
def searchInterval {φ : ℝ → ℝ} (A : GoldenSectionMethod φ) (k : ℕ) : Set ℝ :=
  Set.Icc (A.a k) (A.b k)

end GoldenSectionMethod
