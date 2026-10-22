/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap

universe u

/- Primary domain: estimating-sequence gap bounds with a quadratically regularized initial model.

Sampled declarations in this domain:
* `estimatingSequence_gap_mem_Icc`
* `quadraticallyRegularizedObjective`
* `quadraticallyRegularizedObjective_apply`
* `IsEstimatingSequence.gap_mem_Icc`

Best owner abstraction for this file:
* source-facing: the recursive scalar sequence `estimatingWeight α`;
* core/canonical: the stagewise gap-control theorem `estimatingSequence_gap_mem_Icc` together with
  the initial quadratic owner `quadraticallyRegularizedObjective`;
* bridge/view: the later packaged API `IsEstimatingSequence.gap_mem_Icc`, which adds the
  asymptotic hypothesis `λ_k → 0` and is therefore stronger than Theorem 2.19 needs, and the
  pointwise formula from `quadraticallyRegularizedObjective_apply`.

Primitive data kept here:
* the recursive weight family `estimatingWeight α`;
* the initial quadratic owner
  `φ 0 = quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0)`;
* the canonical function-space affine upper bound `φ k ≤ lineMap f (φ 0) (estimatingWeight α k)`.

Derived API:
* the product formula for the recursive weight family;
* the textbook suboptimality estimate, kept as a thin specialization of the owner gap bound.

The algorithmic owner `OptimalMethodRecurrence.weight` is only a later specialization of the same
recursion to a method object, so it is not the public owner for this source-facing file. -/

/-- The recursively defined coefficients `λₖ` attached to the estimating-sequence recursion
`λ₀ = 1`, `λₖ₊₁ = (1 - αₖ) λₖ`. -/
def estimatingWeight (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 - α k) * estimatingWeight α k

/-- The recursively defined estimating-sequence weights are the finite products
`∏_{i=0}^{k-1} (1 - αᵢ)`. -/
-- Proof sketch: argue by induction on `k`. The base case is `k = 0`, where both sides equal `1`.
-- For the step, unfold `estimatingWeight` at `k + 1` and rewrite the finite product
-- over `Finset.range (k + 1)` as the last factor `(1 - α k)` times the product over
-- `Finset.range k`.
theorem estimatingWeight_eq_prod
    (α : ℕ → ℝ) (k : ℕ) :
    estimatingWeight α k =
      Finset.prod (Finset.range k) (fun i ↦ (1 - α i)) := by
  induction k with
  | zero =>
      -- At stage `0`, both the recursive owner and the empty product equal `1`.
      simp [estimatingWeight]
  | succ k hk =>
      -- Extend the product by its last factor and match the recursive definition of `λₖ₊₁`.
      rw [estimatingWeight, Finset.prod_range_succ, hk]
      ring

section

variable {E : Type u} [NormedAddCommGroup E]

/-- Theorem 2.19: if `xₖ`, `φₖ`, and the recursively defined weights
`λ₀ = 1`, `λₖ₊₁ = (1 - αₖ) λₖ` satisfy the estimating-sequence upper-model hypotheses,
`φ₀ = quadraticallyRegularizedObjective (fun _ ↦ f(x₀)) γ₀ x₀`, equivalently
`φ₀(z) = f(x₀) + (γ₀ / 2) ‖z - x₀‖²`, and `xStar` is a minimizer of `f`, then
`f(xₖ) - f(xStar)` is bounded by `λₖ * (f(x₀) - f(xStar) + (γ₀ / 2) ‖x₀ - xStar‖²)`, where
`λₖ = ∏_{i=0}^{k-1} (1 - αᵢ)`. -/
-- Proof sketch: use `hφmin k` and `hfx k` to get
-- `f (x k) ≤ φStar k ≤ φ k xStar`. Apply the owner gap theorem
-- `estimatingSequence_gap_mem_Icc` with `λ_k = estimatingWeight α k`, use the function-space upper
-- bound `hφupper`, and then evaluate the owner initial quadratic model from `hφ0` at `xStar`
-- using `quadraticallyRegularizedObjective_apply`. Since `xStar` minimizes `f`, simplify the
-- resulting interval upper endpoint to the displayed bound. The product formula for `λₖ` is
-- provided by `estimatingWeight_eq_prod`.
theorem estimating_sequence_suboptimality_le
    (f : E → ℝ)
    (x : ℕ → E)
    (φ : ℕ → E → ℝ)
    (φStar : ℕ → ℝ)
    (α : ℕ → ℝ)
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (γ0 : ℝ)
    (hfx : ∀ k : ℕ, f (x k) ≤ φStar k)
    (hφmin : ∀ k : ℕ, IsLeast (Set.range (φ k)) (φStar k))
    (hφupper : ∀ k : ℕ, φ k ≤ lineMap f (φ 0) (estimatingWeight α k))
    (hφ0 : φ 0 = quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0))
    (k : ℕ) :
    f (x k) - f xStar ≤
      estimatingWeight α k *
        (f (x 0) - f xStar + (γ0 / 2) * ‖x 0 - xStar‖ ^ (2 : ℕ)) := by
  -- Reuse Lemma 2.7 to control the stagewise gap by the initial-model gap at `xStar`.
  have hgap :
      f (x k) - f xStar ∈
        Set.Icc 0 (estimatingWeight α k * (φ 0 xStar - f xStar)) := by
    exact estimatingSequence_gap_mem_Icc xStar φStar x hxStar hφupper hφmin hfx k
  -- Rewrite the initial-model gap using the explicit quadratic formula for `φ₀`.
  have hInitial :
      φ 0 xStar - f xStar =
        f (x 0) - f xStar + (γ0 / 2) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    have hφ0_at_xStar :
        φ 0 xStar =
          quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0) xStar := by
      exact congrFun hφ0 xStar
    calc
      φ 0 xStar - f xStar
          = quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0) xStar - f xStar := by
              rw [hφ0_at_xStar]
      _ = (f (x 0) + (γ0 / 2) * ‖xStar - x 0‖ ^ (2 : ℕ)) - f xStar := by
              rw [quadraticallyRegularizedObjective_apply]
      _ = f (x 0) - f xStar + (γ0 / 2) * ‖xStar - x 0‖ ^ (2 : ℕ) := by
              ring
      _ = f (x 0) - f xStar + (γ0 / 2) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
              rw [norm_sub_rev]
  -- Extract the upper endpoint from the interval estimate and substitute the rewritten model gap.
  simpa [hInitial] using hgap.2

end
