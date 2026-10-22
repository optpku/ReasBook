/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators

noncomputable section

section

variable {E : Type u} {G : Type v}
variable [AddCommMonoid E] [Module ℝ E] [Norm G]

/- Definition 8.21 is `source-facing`: the textbook introduces the full-history averaging rule
used in the dual projected subgradient method, with explicit normalized coefficients `μ_n^k`
built from the stepsizes `γ_n` and the norms `‖g(x^n)‖₂`. Domain sampling against the nearby
Chapter 8 weighted-average APIs (`projected_subgradient_stepsize_average_iterate`,
`projected_subgradient_strongly_convex_average_weight`) and mathlib's finite weighted-average
owner `Finset.centerMass` shows that the right public layer here is still the explicit textbook
coefficient family together with the resulting averaged iterate sequence, rather than a surrogate
package or existential interface. -/

/-- The full-history averaging coefficient `μ_n^k`, indexed by `n = 0, …, k`, is the normalized
weight obtained from `γ_n / ‖g n‖`. -/
def full_averaging_weight (γ : ℕ → ℝ) (g : ℕ → G) (k : ℕ) (n : Fin (k + 1)) : ℝ :=
  (γ n / ‖g n‖) / ∑ j : Fin (k + 1), γ j / ‖g j‖

-- Proof sketch: unfold `full_averaging_weight`; the value at `n` is definitionally the displayed
-- normalized quotient `(γ n / ‖g n‖) / ∑_{j=0}^k γ j / ‖g j‖`.
/-- Evaluating `full_averaging_weight γ g k` at `n` gives the textbook coefficient
`(γ_n / ‖g(x^n)‖₂) / ∑_{j=0}^k γ_j / ‖g(x^j)‖₂`, abstracted over the history `g`. -/
theorem full_averaging_weight_eq
    (γ : ℕ → ℝ) (g : ℕ → G) (k : ℕ) (n : Fin (k + 1)) :
    full_averaging_weight γ g k n =
      (γ n / ‖g n‖) / ∑ j : Fin (k + 1), γ j / ‖g j‖ := by
  -- This is exactly the displayed quotient after unfolding the coefficient definition.
  rfl

/-- Definition 8.21: the full averaging sequence uses the entire iterate history up to time `k`,
forming `x^(k)` as the weighted average `∑_{n=0}^k μ_n^k x^n`, where
`μ_n^k = (γ_n / ‖g(x^n)‖₂) / ∑_{j=0}^k γ_j / ‖g(x^j)‖₂`. -/
def full_averaging_sequence (x : ℕ → E) (γ : ℕ → ℝ) (g : ℕ → G) : ℕ → E :=
  fun k ↦ ∑ n : Fin (k + 1), full_averaging_weight γ g k n • x n

-- Proof sketch: unfold `full_averaging_sequence`; evaluation at `k` is definitionally the finite
-- sum of the prefix iterates `x^0, …, x^k` with coefficients `full_averaging_weight γ g k n`.
/-- Evaluating the full averaging sequence at `k` gives the weighted sum of the first `k + 1`
iterates with the coefficients `μ_n^k`. -/
theorem full_averaging_sequence_apply
    (x : ℕ → E) (γ : ℕ → ℝ) (g : ℕ → G) (k : ℕ) :
    full_averaging_sequence x γ g k =
      ∑ n : Fin (k + 1), full_averaging_weight γ g k n • x n := by
  -- Evaluating the sequence at `k` reduces directly to its defining finite weighted sum.
  rfl

end
