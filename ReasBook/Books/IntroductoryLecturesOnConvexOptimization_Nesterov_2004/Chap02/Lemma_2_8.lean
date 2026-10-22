/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_19

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex estimating sequences on real inner-product spaces.

Sampled owner-style declarations in this domain:
* `IsEstimatingSequence`
* `estimatingWeight`
* `lineMap`
* `firstOrderTaylorModelAt`
* `quadraticallyRegularizedObjective`
* `StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt`

Source/core/bridge triage for this file:
* source-facing: the recursive sequence `strongConvexEstimatingFunction`;
* core/canonical: `IsEstimatingSequence f φ lam`, `estimatingWeight α`, `lineMap`,
  `firstOrderTaylorModelAt`, and `quadraticallyRegularizedObjective`;
* bridge/view: the pointwise successor formula
  `strongConvexEstimatingFunction_succ_apply`.

Primitive data:
* the initial function `φ₀`;
* the recursive function sequence;
* the upstream real-valued weight sequence `estimatingWeight α`.

Derived API:
* the function-valued zero and successor equations for `strongConvexEstimatingFunction`;
* the pointwise successor expansion through the owner affine-quadratic model;
* the `NNReal` weight view `Real.toNNReal ∘ estimatingWeight α` used by
  `IsEstimatingSequence`. -/

section

variable (μ : ℝ) (f φ₀ : E → ℝ) (y : ℕ → E) (α : ℕ → ℝ)

/-- The recursively defined estimating-sequence functions in Nesterov's strong-convex
construction. -/
def strongConvexEstimatingFunction
    (μ : ℝ) (f φ₀ : E → ℝ) (y : ℕ → E) (α : ℕ → ℝ) :
    ℕ → E → ℝ
  | 0 => φ₀
  | k + 1 =>
      lineMap
        (strongConvexEstimatingFunction μ f φ₀ y α k)
        (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k))
        (α k)

/-- The estimating-sequence functions start from the initial model `φ₀`. -/
@[simp] theorem strongConvexEstimatingFunction_zero :
    strongConvexEstimatingFunction μ f φ₀ y α 0 = φ₀ := rfl

/-- The estimating-sequence functions satisfy their defining affine update with the owner
regularized first-order Taylor model. -/
theorem strongConvexEstimatingFunction_succ
    (k : ℕ) :
    strongConvexEstimatingFunction μ f φ₀ y α (k + 1) =
      lineMap
        (strongConvexEstimatingFunction μ f φ₀ y α k)
        (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k))
        (α k) := rfl

/-- Evaluating the successor stage recovers the textbook affine-quadratic update formula. -/
@[simp] theorem strongConvexEstimatingFunction_succ_apply
    (k : ℕ) (x : E) :
    strongConvexEstimatingFunction μ f φ₀ y α (k + 1) x =
      (1 - α k) * strongConvexEstimatingFunction μ f φ₀ y α k x +
        α k * (f (y k) + inner ℝ (∇ f (y k)) (x - y k) +
          (μ / 2) * ‖x - y k‖ ^ (2 : ℕ)) := by
  simpa [lineMap_apply_module, quadraticallyRegularizedObjective_apply,
    firstOrderTaylorModelAt_apply] using
    congrFun
      (strongConvexEstimatingFunction_succ μ f φ₀ y α k)
      x

end

/-- Helper for Lemma 2.8: the recursive estimating-sequence weights stay in the interval
`[0, 1]` when each coefficient `αₖ` does. -/
private theorem estimatingWeight_mem_Icc
    {α : ℕ → ℝ}
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) :
    ∀ k, estimatingWeight α k ∈ Set.Icc (0 : ℝ) 1
  | 0 => by
      -- The initial weight is exactly `1`.
      simp [estimatingWeight]
  | k + 1 => by
      -- The successor weight is the product of two factors already known to lie in `[0, 1]`.
      rcases estimatingWeight_mem_Icc hα k with ⟨hk_nonneg, hk_le_one⟩
      rcases hα k with ⟨hα_nonneg, hα_le_one⟩
      constructor
      · simp [estimatingWeight]
        nlinarith
      · simp [estimatingWeight]
        nlinarith

/-- Every stage of the recursive strong-convex estimating function is bounded above by the
canonical affine combination of `f` and `φ₀` with weight `estimatingWeight α k`. -/
theorem strongConvexEstimatingFunction_upper_bound_apply
    {μ : ℝ}
    {f φ₀ : E → ℝ}
    {y : ℕ → E}
    {α : ℕ → ℝ}
    (hf_strong : StrongConvexOn Set.univ μ f)
    (hf_grad : ∀ k, HasGradientAt f (∇ f (y k)) (y k))
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) :
    ∀ k x,
      strongConvexEstimatingFunction μ f φ₀ y α k x ≤
        (1 - estimatingWeight α k) * f x + estimatingWeight α k * φ₀ x := by
  intro k
  induction k with
  | zero =>
      intro x
      -- The base stage is the trivial identity `φ₀(x) = (1 - 1) f(x) + 1 * φ₀(x)`.
      simp [strongConvexEstimatingFunction, estimatingWeight]
  | succ k ih =>
      intro x
      have hk := ih x
      have hmodel :
          quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k) x ≤ f x :=
        by
          simpa [quadraticallyRegularizedObjective_apply, firstOrderTaylorModelAt_apply,
            ge_iff_le, add_assoc, add_left_comm, add_comm] using
            StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
              hf_strong (by simp) (by simp) (hf_grad k)
      have hα_nonneg : 0 ≤ α k := (hα k).1
      have hα_le_one : α k ≤ 1 := (hα k).2
      have hone_sub_nonneg : 0 ≤ 1 - α k := by
        linarith
      -- Substitute the inductive bound and the tangent-model domination into the successor update.
      calc
        strongConvexEstimatingFunction μ f φ₀ y α (k + 1) x
          = (1 - α k) * strongConvexEstimatingFunction μ f φ₀ y α k x +
              α k * quadraticallyRegularizedObjective
                (firstOrderTaylorModelAt f (y k)) μ (y k) x := by
              simp
        _ ≤ (1 - α k) *
              ((1 - estimatingWeight α k) * f x + estimatingWeight α k * φ₀ x) +
              α k * f x := by
              nlinarith
        _ = (1 - ((1 - α k) * estimatingWeight α k)) * f x +
              ((1 - α k) * estimatingWeight α k) * φ₀ x := by
              ring
        _ = (1 - estimatingWeight α (k + 1)) * f x +
              estimatingWeight α (k + 1) * φ₀ x := by
              simp [estimatingWeight]

/-- The recursive strong-convex estimating function is bounded above by the canonical
function-space affine combination of `f` and `φ₀` with weight `estimatingWeight α k`. -/
theorem strongConvexEstimatingFunction_upper_bound
    {μ : ℝ}
    {f φ₀ : E → ℝ}
    {y : ℕ → E}
    {α : ℕ → ℝ}
    (hf_strong : StrongConvexOn Set.univ μ f)
    (hf_grad : ∀ k, HasGradientAt f (∇ f (y k)) (y k))
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    strongConvexEstimatingFunction μ f φ₀ y α k ≤ lineMap f φ₀ (estimatingWeight α k) := by
  intro x
  simpa [lineMap_apply_module] using
    strongConvexEstimatingFunction_upper_bound_apply hf_strong hf_grad hα k x

/-- Lemma 2.8: if `f` is differentiable at the sampled points `y_k`, is `μ`-strongly convex on
the ambient real inner-product space `E`, the coefficients satisfy `0 ≤ α_k ≤ 1`, and the
canonical weight sequence
`Real.toNNReal ∘ estimatingWeight α` tends to `0`, then the recursively defined pair
`(φ_k, λ_k)` is an estimating sequence for `f`. The smooth convex case is the specialization
`μ = 0`; the textbook assumptions `0 < α_k < 1` and divergence of the partial sums are one
sufficient way to obtain the stated weight-limit hypothesis. -/
-- Proof sketch: prove the estimating-sequence inequality by induction on `k`. The base case is
-- `λ₀ = 1` and `φ₀ = φ₀`. For the step, use the strong-convexity lower tangent inequality from
-- `hf_strong.lower_tangent_quadratic_of_hasGradientAt` together with `hf_grad k` at the point
-- `y k` to bound the owner regularized
-- Taylor model `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k)` by
-- `f`, substitute this into `strongConvexEstimatingFunction_succ`, and simplify with the
-- recursion for `λ_{k+1}`. The asymptotic clause is exactly the hypothesis
-- `hweight_tendsto_zero`; in the textbook this is obtained from
-- `0 < α_k < 1` and divergence of the partial sums.
theorem strongConvexEstimatingFunction_isEstimatingSequence
    {μ : ℝ}
    {f : E → ℝ}
    (hf_strong : StrongConvexOn Set.univ μ f)
    (φ₀ : E → ℝ)
    (y : ℕ → E)
    (α : ℕ → ℝ)
    (hf_grad : ∀ k, HasGradientAt f (∇ f (y k)) (y k))
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1)
    (hweight_tendsto_zero :
      Filter.Tendsto (Real.toNNReal ∘ estimatingWeight α) Filter.atTop (nhds 0)) :
    IsEstimatingSequence f
      (strongConvexEstimatingFunction μ f φ₀ y α)
      (Real.toNNReal ∘ estimatingWeight α) := by
  refine ⟨hweight_tendsto_zero, ?_⟩
  intro k
  -- The limit clause is assumed, so only the stagewise affine upper bound remains.
  simpa [Real.coe_toNNReal _ (estimatingWeight_mem_Icc hα k).1] using
    strongConvexEstimatingFunction_upper_bound hf_strong hf_grad hα k
