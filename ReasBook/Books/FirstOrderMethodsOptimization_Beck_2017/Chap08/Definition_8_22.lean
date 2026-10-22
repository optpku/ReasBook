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

/- Definition 8.22 is `source-facing`: the textbook introduces a suffix-window averaging rule for
the dual projected subgradient method, keeping the explicit coefficients `η_n^k` and the explicit
averaged iterate `x^(k)`. Domain sampling against the nearby Chapter 8 average-iterate owners
`full_averaging_sequence`, `projected_subgradient_stepsize_average_iterate`, and
`projected_subgradient_strongly_convex_average_iterate`, together with mathlib's finite weighted
sum owner `Finset.centerMass`, shows that the right public layer here is again the concrete
coefficient family and the resulting weighted sum over the textbook window `[k / 2, k]`, rather
than a surrogate wrapper or existential package. -/

/-- The partial-history averaging coefficient `η_n^k`, intended for indices
`n = k / 2, …, k`, is the normalized weight obtained from `γ_n / ‖g n‖` over the window
`[k / 2, k]`. -/
def partial_averaging_weight (γ : ℕ → ℝ) (g : ℕ → G) (k n : ℕ) : ℝ :=
  (γ n / ‖g n‖) /
    Finset.sum (Finset.Icc (k / 2) k) fun j ↦ γ j / ‖g j‖

-- Proof sketch: unfold `partial_averaging_weight`; its value at `n` is definitionally the
-- normalized quotient with denominator given by the suffix-window sum from `k / 2` through `k`.
/-- Evaluating `partial_averaging_weight γ g k` at `n` gives the textbook coefficient
`(γ_n / ‖g(x^n)‖₂) / ∑_{j=[k/2]}^k γ_j / ‖g(x^j)‖₂`, with the denominator taken over the
partial-averaging window `[k / 2, k]`. -/
theorem partial_averaging_weight_eq
    (γ : ℕ → ℝ) (g : ℕ → G) (k n : ℕ) :
    partial_averaging_weight γ g k n =
      (γ n / ‖g n‖) / Finset.sum (Finset.Icc (k / 2) k) (fun j ↦ γ j / ‖g j‖) := by
  -- This is exactly the displayed coefficient after unfolding the definition.
  rfl

/-- Definition 8.22: the partial averaging sequence uses only the iterate window
`x^([k/2]), x^([k/2] + 1), …, x^k`, forming
`x^(k) = ∑_{n=[k/2]}^k η_n^k x^n`
with `η_n^k = (γ_n / ‖g(x^n)‖₂) / ∑_{j=[k/2]}^k γ_j / ‖g(x^j)‖₂`. -/
def partial_averaging_sequence (x : ℕ → E) (γ : ℕ → ℝ) (g : ℕ → G) : ℕ → E :=
  fun k ↦
    Finset.sum (Finset.Icc (k / 2) k) fun n ↦ partial_averaging_weight γ g k n • x n

-- Proof sketch: unfold `partial_averaging_sequence`; evaluation at `k` is definitionally the
-- finite weighted sum of the iterates with indices in the suffix window `[k / 2, k]`.
/-- Evaluating the partial averaging sequence at `k` gives the weighted sum of the iterates in the
window `[k / 2, k]` with coefficients `η_n^k`. -/
theorem partial_averaging_sequence_apply
    (x : ℕ → E) (γ : ℕ → ℝ) (g : ℕ → G) (k : ℕ) :
    partial_averaging_sequence x γ g k =
      Finset.sum (Finset.Icc (k / 2) k) fun n ↦ partial_averaging_weight γ g k n • x n := by
  -- Evaluating the sequence at `k` reduces directly to its defining suffix-window sum.
  rfl

end
