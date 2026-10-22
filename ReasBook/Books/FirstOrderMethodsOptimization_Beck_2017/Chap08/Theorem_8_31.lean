/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_24
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11
import Mathlib.Analysis.Convex.Jensen

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k
local notation "x̄" =>
  projected_subgradient_method_iterate C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k

/- Theorem 8.31 is `source-facing`: it states the concrete `O(1 / k)` convergence guarantees for
the projected subgradient iterates in the strongly convex regime. The relevant owner abstractions
already present in the chapter are the iterate sequence `projected_subgradient_method`, the
running-best objective value `best_achieved_function_value`, the standing constrained-problem class
`IsConstrainedConvexProblem`, the norm-bound package `SubgradientNormBoundOn`, and the
canonical owner predicate `StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)` for
strong convexity. Since the Chapter 5 source-facing strong-convexity owner also requires `0 < σ`,
the rate clauses below keep that positivity explicit alongside `StrongConvexOn` rather than
weakening the theorem to a nonpositive modulus. -/

/-- The ergodic weight `α_n^k` used in the strongly convex projected-subgradient average, with the
canonical degenerate convention `α_0^0 = 1`. For `k > 0`, this is exactly `2n / (k (k + 1))`. -/
def projected_subgradient_strongly_convex_average_weight (k n : ℕ) : ℝ :=
  if k = 0 then
    if n = 0 then 1 else 0
  else
    (2 : ℝ) * n / (k * (k + 1) : ℝ)

namespace ProjectedSubgradientErgodicNotation

/-- Scoped notation for the strongly convex ergodic weights `α_n^k` from Theorem 8.31. -/
scoped notation "α[" k "](" n ")" =>
  projected_subgradient_strongly_convex_average_weight k n

end ProjectedSubgradientErgodicNotation

open scoped ProjectedSubgradientErgodicNotation

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_weight`; the displayed
-- piecewise formula is exactly the defining equation.
/-- Evaluating `projected_subgradient_strongly_convex_average_weight k n` gives the textbook weight
`α_n^k`, with the convention `α_0^0 = 1` and `α_n^k = 2n / (k (k + 1))` for `k > 0`. -/
theorem projected_subgradient_strongly_convex_average_weight_eq (k n : ℕ) :
    α[k](n) =
      if k = 0 then
        if n = 0 then 1 else 0
      else
        (2 : ℝ) * n / (k * (k + 1) : ℝ) := by
  rfl

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_weight`; when `k = 0`, the
-- outer branch applies and the inner branch at `n = 0` gives the value `1`.
/-- The degenerate ergodic weight at `k = 0` places all mass on the initial iterate. -/
@[simp] theorem projected_subgradient_strongly_convex_average_weight_zero :
    α[0](0) = 1 := by
  -- Unfold the degenerate branch of the weight definition.
  simp [projected_subgradient_strongly_convex_average_weight]

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_weight`; the hypothesis
-- `0 < k` rules out the degenerate branch, so the definition reduces to the displayed fraction.
/-- For `k > 0`, the strongly convex ergodic weight is the explicit coefficient
`2n / (k (k + 1))`. -/
theorem projected_subgradient_strongly_convex_average_weight_eq_of_pos
    {k n : ℕ} (hk : 0 < k) :
    α[k](n) =
      (2 : ℝ) * n / (k * (k + 1) : ℝ) := by
  -- A positive `k` eliminates the exceptional `k = 0` branch.
  simp [projected_subgradient_strongly_convex_average_weight, hk.ne']

-- Proof sketch: for `k > 0`, the preceding explicit formula gives the standard normalized
-- coefficients `2n / (k (k + 1))`; these are nonnegative and sum to `1` on `n = 0, …, k`.
/-- For `k > 0`, the strongly convex ergodic weights form a simplex on the prefix
`{0, …, k}`. -/
theorem projected_subgradient_strongly_convex_average_weights_form_simplex
    {k : ℕ} (hk : 0 < k) :
    (∀ n ∈ Finset.range (k + 1), 0 ≤ α[k](n)) ∧
      Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n)) = 1 := by
  constructor
  · -- The explicit positive-`k` formula makes each coefficient manifestly nonnegative.
    intro n hn
    rw [projected_subgradient_strongly_convex_average_weight_eq_of_pos hk]
    positivity
  · -- Normalize the explicit coefficients and evaluate the arithmetic progression sum.
    simp_rw [projected_subgradient_strongly_convex_average_weight_eq_of_pos hk]
    have hkR : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk.ne'
    have hk1R : (k + 1 : ℝ) ≠ 0 := by
      positivity
    have hsum_all :
        ∀ m : ℕ,
          Finset.sum (Finset.range (m + 1)) (fun n ↦ (n : ℝ)) =
            (m : ℝ) * (m + 1) / 2 := by
      intro m
      -- Evaluate the arithmetic progression directly in `ℝ` to avoid cast-normalization noise.
      induction m with
      | zero =>
          norm_num
      | succ m hm =>
          rw [Finset.sum_range_succ, hm]
          have hpoly :
              (m : ℝ) * (m + 1) / 2 + (m + 1 : ℝ) =
                ((m + 1 : ℝ) * ((m + 1 : ℝ) + 1) / 2) := by
            ring
          simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hpoly
    have hsum :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ)) =
          (k : ℝ) * (k + 1) / 2 :=
      hsum_all k
    calc
      Finset.sum (Finset.range (k + 1)) (fun n ↦ (2 : ℝ) * n / (k * (k + 1) : ℝ))
          = Finset.sum (Finset.range (k + 1))
              (fun n ↦ ((2 : ℝ) / (k * (k + 1) : ℝ)) * n) := by
              -- Pull the common denominator into a scalar factor.
              apply Finset.sum_congr rfl
              intro n hn
              field_simp [hkR, hk1R]
      _ = ((2 : ℝ) / (k * (k + 1) : ℝ)) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ)) := by
            rw [← Finset.mul_sum]
      _ = ((2 : ℝ) / (k * (k + 1) : ℝ)) * ((k : ℝ) * (k + 1) / 2) := by
            rw [hsum]
      _ = 1 := by
            field_simp [hkR, hk1R]

/-- The weighted average iterate `x^(k)` used in the ergodic part of the strongly convex
projected-subgradient rate. -/
def projected_subgradient_strongly_convex_average_iterate
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) (k : ℕ) : E :=
  let x :=
    projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  Finset.sum (Finset.range (k + 1)) fun n ↦
    projected_subgradient_strongly_convex_average_weight k n • (x n : E)

-- Keep this notation local: Theorem 8.28 owns the public `x^[...]` notation for its distinct
-- stepsize-weighted average, while this theorem's strongly convex average has different weights.
local notation "x^(" k ")" =>
  projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_iterate`; evaluation at
-- `k` is definitionally the finite weighted sum of the iterates `x^0, …, x^k`.
/-- Evaluating the strongly convex averaged iterate at `k` gives the weighted sum
`∑_{n=0}^k α_n^k x^n` with the canonical weights
`projected_subgradient_strongly_convex_average_weight k n`. -/
theorem projected_subgradient_strongly_convex_average_iterate_eq_sum
    (k : ℕ) :
    x^(k) = Finset.sum (Finset.range (k + 1)) fun n ↦ α[k](n) • x̄[n] := by
  rfl

-- Proof sketch: unfold `projected_subgradient_strongly_convex_average_iterate`; for `k = 0`, the
-- range consists only of `0`, and `projected_subgradient_strongly_convex_average_weight_zero`
-- makes the unique coefficient equal to `1`.
/-- The strongly convex weighted average at `k = 0` is the initial projected iterate `x^0`. -/
theorem projected_subgradient_strongly_convex_average_iterate_zero :
    x^(0) = x̄[0] := by
  -- Only the index `0` appears in the degenerate average, with coefficient `1`.
  rw [projected_subgradient_strongly_convex_average_iterate_eq_sum]
  simp

-- Proof sketch: convert the chosen iterate subgradient to the Euclidean owner required by
-- Theorem 5.24, apply the quadratic lower-support inequality at the optimal point `xStar`, and
-- then rewrite the resulting `EReal` inequality back into the real-valued objective gap form.
/-- Helper for Theorem 8.31: strong convexity upgrades the iterate-level subgradient gap estimate
by the quadratic term `(σ / 2) ‖x^n - xStar‖²`. -/
private lemma stronglyConvexGapAddQuadratic_le_inner_at_iterate
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ((f x̄[n]).toReal - fOpt) + (σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) ≤
      inner ℝ (g n (x[n])) (x̄[n] - xStar) := by
  -- Convert the optimal point and the current iterate into effective-domain points.
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_dom : xStar ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxStar_data.1)
  have hxn_dom : x̄[n] ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[n]).property)
  have hxStar_top : f xStar ≠ ⊤ := ne_of_lt hxStar_dom
  have hxStar_bot : f xStar ≠ ⊥ := h_problem.ne_bot xStar
  have hxn_top : f x̄[n] ≠ ⊤ := ne_of_lt hxn_dom
  have hxn_bot : f x̄[n] ≠ ⊥ := h_problem.ne_bot (x̄[n])
  have hsub_euclidean : g n (x[n]) ∈ euclideanSubdifferential f x̄[n] := by
    rw [mem_euclideanSubdifferential_iff]
    simpa using h_subgrad n
  have hquadratic :=
    euclideanSubgradientQuadraticLowerBound_of_strongConvexOn
      hσ (fun z ↦ h_problem.ne_bot z) h_strong x̄[n] (g n (x[n])) hsub_euclidean xStar hxStar_dom
  have hquadraticE :
      (((f x̄[n]).toReal +
            (inner ℝ (g n (x[n])) (xStar - x̄[n]) +
              (σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
        (((f xStar).toReal : ℝ) : EReal) := by
    rw [ge_iff_le] at hquadratic
    simpa [EReal.coe_toReal hxn_top hxn_bot, EReal.coe_toReal hxStar_top hxStar_bot,
      EReal.coe_add, add_assoc, norm_sub_rev] using hquadratic
  have hquadraticReal :
      (f x̄[n]).toReal +
          (inner ℝ (g n (x[n])) (xStar - x̄[n]) +
            (σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ)) ≤
        (f xStar).toReal := by
    exact_mod_cast hquadraticE
  have hinner_neg :
      inner ℝ (g n (x[n])) (xStar - x̄[n]) =
        -inner ℝ (g n (x[n])) (x̄[n] - xStar) := by
    rw [show xStar - x̄[n] = -(x̄[n] - xStar) by abel, inner_neg_right]
  -- Rewrite the optimal-point value as `fOpt` and rearrange the support inequality.
  rw [optimal_point_toReal_eq_fOpt h_problem hxStar] at hquadraticReal
  rw [hinner_neg] at hquadraticReal
  linarith

-- Proof sketch: replay the metric-projection expansion from Lemma 8.11, but keep the stronger
-- strong-convexity support estimate all the way to the final division by `2 * t_n`.
/-- Helper for Theorem 8.31: before specializing the textbook schedule, one projected
subgradient step yields the generic strongly-convex one-step gap inequality with coefficients
`(1 / (2 t_n) - σ / 2)` and `1 / (2 t_n)`. -/
private lemma stronglyConvexOneStepGap_le_beforeStepsizeSubstitution
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) (ht_pos : 0 < t n) :
    ((f x̄[n]).toReal - fOpt) ≤
      ((1 / (2 * t n)) - σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
        (1 / (2 * t n)) * ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
        (t n / 2) * h_bound.L_f ^ (2 : ℕ) := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxkp1 :
      x̄[n + 1] =
        metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex (x̄[n] - t n • g n (x[n])) := by
    simpa using
      projected_subgradient_method_iterate_succ C h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex g t x0 n
  have hxStar_proj :
      (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex xStar : E) = xStar := by
    simpa [projectionPoint] using
      projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex hxStar_data.1
  have hdist :
      ‖x̄[n + 1] - xStar‖ ≤ ‖(x̄[n] - t n • g n (x[n])) - xStar‖ := by
    simpa [hxkp1, hxStar_proj, dist_eq_norm] using
      LipschitzWith.dist_le_mul
        (metricProjection_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex)
        (x̄[n] - t n • g n (x[n])) xStar
  have hsq :
      ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) ≤ ‖(x̄[n] - t n • g n (x[n])) - xStar‖ ^ (2 : ℕ) := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact hdist
  have hgap_quad_le_inner :
      ((f x̄[n]).toReal - fOpt) + (σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) ≤
        inner ℝ (x̄[n] - xStar) (g n (x[n])) := by
    simpa [real_inner_comm] using
      stronglyConvexGapAddQuadratic_le_inner_at_iterate
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_subgrad hxStar n
  have hexpand :
      ‖(x̄[n] - t n • g n (x[n])) - xStar‖ ^ (2 : ℕ) =
        ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (x̄[n] - xStar) (g n (x[n])) +
            (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ) := by
    have hrewrite :
        (x̄[n] - t n • g n (x[n])) - xStar = (x̄[n] - xStar) - t n • g n (x[n]) := by
      abel
    rw [hrewrite, norm_sub_sq_real]
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
    ring
  have hgrad_norm :
      ‖g n (x[n])‖ ≤ h_bound.L_f := by
    simpa using h_bound.norm_le (x := x̄[n]) ((x[n]).property) (h_subgrad n)
  have hgrad_sq :
      ‖g n (x[n])‖ ^ (2 : ℕ) ≤ h_bound.L_f ^ (2 : ℕ) := by
    nlinarith [hgrad_norm, norm_nonneg (g n (x[n])), sq_nonneg h_bound.L_f]
  have hstep :
      ‖(x̄[n] - t n • g n (x[n])) - xStar‖ ^ (2 : ℕ) ≤
        (1 - σ * t n) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
          2 * t n * ((f x̄[n]).toReal - fOpt) +
            (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ) := by
    rw [hexpand]
    nlinarith
  have hmain :
      ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) ≤
        (1 - σ * t n) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
          2 * t n * ((f x̄[n]).toReal - fOpt) +
            (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ) :=
    hsq.trans hstep
  have hscale :
      (2 * t n) *
          (((1 / (2 * t n)) - σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
            (1 / (2 * t n)) * ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
            (t n / 2) * h_bound.L_f ^ (2 : ℕ)) =
        (1 - σ * t n) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
          ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
            (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ) := by
    field_simp [ht_pos.ne']
  have hmul :
      (2 * t n) * ((f x̄[n]).toReal - fOpt) ≤
        (2 * t n) *
          (((1 / (2 * t n)) - σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
            (1 / (2 * t n)) * ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
            (t n / 2) * h_bound.L_f ^ (2 : ℕ)) := by
    rw [hscale]
    nlinarith
  have h2t_pos : 0 < 2 * t n := by
    positivity
  nlinarith

-- Proof sketch: repeat the projection-expansion argument from Lemma 8.11, but replace the plain
-- subgradient gap estimate by the stronger helper above and then specialize the explicit
-- stepsizes `t_n = 2 / (σ (n + 1))`.
/-- Helper for Theorem 8.31: after substituting the strongly convex stepsize rule, one projected
subgradient step has the telescoping-ready form from the textbook proof. -/
private lemma stronglyConvexStepsize_gap_le_rearranged
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ((f x̄[n]).toReal - fOpt) ≤
      (σ * ((n : ℝ) - 1) / 4) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
        (σ * ((n : ℝ) + 1) / 4) * ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
        h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
  have ht_pos : 0 < t n := by
    rw [h_stepsize]
    positivity
  have hbase :=
    stronglyConvexOneStepGap_le_beforeStepsizeSubstitution
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_strong hσ h_subgrad hxStar n ht_pos
  have hInv :
      1 / (2 * t n) = σ * (n + 1 : ℝ) / 4 := by
    rw [h_stepsize]
    field_simp [hσ.ne']
    ring
  have hCoeff :
      (1 / (2 * t n)) - σ / 2 = σ * ((n : ℝ) - 1) / 4 := by
    rw [hInv]
    ring
  have hLast :
      (t n / 2) * h_bound.L_f ^ (2 : ℕ) =
        h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
    rw [h_stepsize]
    field_simp [hσ.ne']
  -- Route correction: keep all schedule normalization in this short adapter lemma.
  calc
    ((f x̄[n]).toReal - fOpt) ≤
        ((1 / (2 * t n)) - σ / 2) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
          (1 / (2 * t n)) * ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
            (t n / 2) * h_bound.L_f ^ (2 : ℕ) :=
      hbase
    _ =
        (σ * ((n : ℝ) - 1) / 4) * ‖x̄[n] - xStar‖ ^ (2 : ℕ) -
          (σ * ((n : ℝ) + 1) / 4) * ‖x̄[n + 1] - xStar‖ ^ (2 : ℕ) +
            h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
              rw [hCoeff, hInv, hLast]

-- Proof sketch: evaluate the shifted quadratic-coefficient sum by induction; each new term
-- cancels the previous boundary term and leaves only the final negative remainder.
/-- Helper for Theorem 8.31: the weighted squared-distance contributions telescope to the single
terminal remainder `-(σ k (k + 1) / 4) d_{k+1}`. -/
private lemma stronglyConvexWeightedDistanceTelescope
    (d : ℕ → ℝ) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦
          (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
            (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1)) =
      -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) := by
  induction k with
  | zero =>
      norm_num
  | succ k hk =>
      rw [Finset.sum_range_succ, hk]
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
      ring

-- Proof sketch: evaluate the arithmetic progression sum directly in `ℝ` so later rate proofs can
-- use the closed form `∑_{n=0}^k n = k (k + 1) / 2` without repeated cast normalization.
/-- Helper for Theorem 8.31: the real-valued prefix sum of the integers `0, …, k` is
`k (k + 1) / 2`. -/
private theorem sumRangeNatCast (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ)) =
      (k : ℝ) * (k + 1) / 2 := by
  induction k with
  | zero =>
      norm_num
  | succ k hk =>
      rw [Finset.sum_range_succ, hk]
      have hpoly :
          (k : ℝ) * (k + 1) / 2 + (k + 1 : ℝ) =
            ((k + 1 : ℝ) * ((k + 1 : ℝ) + 1) / 2) := by
        ring
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hpoly

-- Proof sketch: induct on `k`; the step adds the final term `(k + 1) / (k + 2)`, which is at
-- most `1`, so the whole prefix sum stays below `k + 1`.
/-- Helper for Theorem 8.31: the harmonic-type prefix sum `∑_{n=0}^k n / (n + 1)` is bounded by
`k`. -/
private theorem sumNatDivSucc_le (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) ≤ k := by
  induction k with
  | zero =>
      norm_num
  | succ k hk =>
      rw [Finset.sum_range_succ]
      have hfrac :
          ((k + 1 : ℝ) / ((k + 1 : ℝ) + 1)) ≤ 1 := by
        have hden : 0 < ((k + 1 : ℝ) + 1) := by positivity
        exact (div_le_iff₀ hden).2 (by nlinarith)
      have hmain :
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) +
              ((k + 1 : ℝ) / ((k + 1 : ℝ) + 1)) ≤
            (k + 1 : ℝ) := by
        nlinarith [hk, hfrac]
      simpa [Nat.cast_add, Nat.cast_one] using hmain

-- Proof sketch: multiply the one-step inequality by `n` and sum over the prefix. The positive
-- and negative squared-distance terms telescope exactly, leaving only the final negative tail and
-- the prefix sum of the harmonic-type remainder terms.
/-- Helper for Theorem 8.31: summing the weighted one-step inequalities yields the textbook
prefix estimate for `∑_{n=0}^k n (f(x^n) - fOpt)`. -/
private lemma stronglyConvexStepsize_weightedGap_prefix_sum_le
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt)) ≤
      h_bound.L_f ^ (2 : ℕ) * k / σ := by
  let d : ℕ → ℝ := fun n ↦ ‖x̄[n] - xStar‖ ^ (2 : ℕ)
  have hsum_le :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦
            (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
              (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1) +
              (n : ℝ) * (h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hstep :=
      stronglyConvexStepsize_gap_le_rearranged
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_subgrad h_stepsize hxStar n
    have hmul :
        (n : ℝ) * (((f x̄[n]).toReal - fOpt)) ≤
          (n : ℝ) *
            ((σ * ((n : ℝ) - 1) / 4) * d n -
              (σ * ((n : ℝ) + 1) / 4) * d (n + 1) +
              h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    nlinarith
  have htele :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦
            (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
              (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1)) =
        -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) :=
    stronglyConvexWeightedDistanceTelescope (σ := σ) d k
  have hrem_eq :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ (n : ℝ) * (h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) =
        (h_bound.L_f ^ (2 : ℕ) / σ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    field_simp [hσ.ne']
  have htail_nonpos :
      -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) ≤ 0 := by
    have hd_nonneg : 0 ≤ d (k + 1) := by
      positivity
    have hcoeff_nonneg : 0 ≤ σ * (k : ℝ) * (k + 1 : ℝ) / 4 := by
      positivity
    have hprod_nonneg : 0 ≤ (σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) := by
      exact mul_nonneg hcoeff_nonneg hd_nonneg
    simpa [neg_mul] using neg_nonpos.mpr hprod_nonneg
  have hrem_le :
      (h_bound.L_f ^ (2 : ℕ) / σ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) ≤
        h_bound.L_f ^ (2 : ℕ) * k / σ := by
    have hconst_nonneg : 0 ≤ h_bound.L_f ^ (2 : ℕ) / σ := by
      positivity
    have hsum_div :=
      mul_le_mul_of_nonneg_left (sumNatDivSucc_le k) hconst_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum_div
  calc
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt))
        ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦
          (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
            (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1) +
            (n : ℝ) * (h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) :=
      hsum_le
    _ =
      (Finset.sum (Finset.range (k + 1))
        (fun n ↦
          (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
            (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1))) +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (n : ℝ) * (h_bound.L_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) := by
            rw [Finset.sum_add_distrib]
    _ =
      -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) +
        (h_bound.L_f ^ (2 : ℕ) / σ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) := by
            rw [htele, hrem_eq]
    _ ≤ h_bound.L_f ^ (2 : ℕ) * k / σ := by
      nlinarith [htail_nonpos, hrem_le]

-- Proof sketch: the strong-convexity segment inequality on the feasible chord from `xStar` to `y`
-- shows that every feasible comparison point must lie above the quadratic model centered at the
-- constrained minimizer `xStar`.
omit [CompleteSpace E] in
/-- Helper for Theorem 8.31: on the convex feasible set `C`, strong convexity turns the objective
gap above the constrained minimizer `xStar` into the quadratic distance lower bound
`(σ / 2) ‖y - xStar‖² ≤ f(y) - fOpt`. -/
private lemma objectiveGap_ge_halfSigmaSqdist_at_feasible
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    {xStar y : E} (hxStar : xStar ∈ XStar) (hy : y ∈ C) :
    (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ) ≤ (f y).toReal - fOpt := by
  let φ : E → ℝ := fun z ↦ (f z).toReal
  let c : ℝ := (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_dom : xStar ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxStar_data.1)
  have hy_dom : y ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hy)
  have hmin_real : ∀ {z : E}, z ∈ C → φ xStar ≤ φ z := by
    intro z hz
    have hxStar_top : f xStar ≠ ⊤ := ne_of_lt hxStar_dom
    have hxStar_bot : f xStar ≠ ⊥ := h_problem.ne_bot xStar
    have hz_dom : z ∈ effective_domain f := by
      exact interior_subset (h_problem.feasible_subset_interior_effective_domain hz)
    have hz_top : f z ≠ ⊤ := ne_of_lt hz_dom
    have hz_bot : f z ≠ ⊥ := h_problem.ne_bot z
    have hmin : f xStar ≤ f z := (isMinOn_iff.mp hxStar_data.2) z hz
    have hmin_coe :
        (((f xStar).toReal : ℝ) : EReal) ≤ (((f z).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hxStar_top hxStar_bot, EReal.coe_toReal hz_top hz_bot] using hmin
    exact EReal.coe_le_coe_iff.mp hmin_coe
  have happrox :
      ∀ n : ℕ, (n : ℝ) / (n + 1 : ℝ) * c ≤ φ y - φ xStar := by
    intro n
    let a : ℝ := (n : ℝ) / (n + 1 : ℝ)
    let b : ℝ := 1 / (n + 1 : ℝ)
    let z : E := a • xStar + b • y
    have ha : 0 ≤ a := by positivity
    have hb : 0 ≤ b := by positivity
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp
    have hzC : z ∈ C := by
      dsimp [z]
      exact h_problem.feasible_convex hxStar_data.1 hy ha hb hab
    have hz_dom : z ∈ effective_domain f := by
      exact interior_subset (h_problem.feasible_subset_interior_effective_domain hzC)
    have hmin_mid : φ xStar ≤ φ z := hmin_real hzC
    have hstrong_mid :
        φ z ≤ a * φ xStar + b * φ y - a * b * c := by
      dsimp [φ, z, c]
      simpa [mul_assoc, mul_left_comm, mul_comm, norm_sub_rev] using
        h_strong.2 hxStar_dom hy_dom ha hb hab
    have hb_pos : 0 < b := by positivity
    have hscaled :
        0 ≤ b * (φ y - φ xStar - a * c) := by
      have hcombine :
          φ xStar ≤ a * φ xStar + b * φ y - a * b * c := by
        exact le_trans hmin_mid hstrong_mid
      have hrewrite :
          a * φ xStar + b * φ y - a * b * c - φ xStar =
            b * (φ y - φ xStar - a * c) := by
        have ha' : a = 1 - b := by
          linarith
        rw [ha']
        ring
      have hcombine' : 0 ≤ a * φ xStar + b * φ y - a * b * c - φ xStar := by
        linarith
      simpa [hrewrite] using hcombine'
    have hgoal_nonneg : 0 ≤ φ y - φ xStar - a * c := by
      by_contra hneg
      have hneg' : φ y - φ xStar - a * c < 0 := lt_of_not_ge hneg
      have : b * (φ y - φ xStar - a * c) < 0 := by
        exact mul_neg_of_pos_of_neg hb_pos hneg'
      linarith
    simpa [a] using hgoal_nonneg
  have hfull : c ≤ φ y - φ xStar := by
    by_cases hxy : y = xStar
    · subst hxy
      simp [c, φ]
    · have hc_pos : 0 < c := by
        dsimp [c]
        have hnorm_pos : 0 < ‖y - xStar‖ ^ (2 : ℕ) := by
          positivity [norm_pos_iff.mpr (sub_ne_zero.mpr hxy)]
        positivity
      by_contra hlt
      have hgap_pos : 0 < (c - (φ y - φ xStar)) / c := by
        have : 0 < c - (φ y - φ xStar) := by
          linarith
        exact div_pos this hc_pos
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap_pos
      have hfrac :
          (φ y - φ xStar) / c < (n : ℝ) / (n + 1 : ℝ) := by
        have hleft :
            1 - (1 / (n + 1 : ℝ)) > 1 - ((c - (φ y - φ xStar)) / c) := by
          linarith
        have hleft' : (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
          field_simp
          ring
        have hright' : 1 - ((c - (φ y - φ xStar)) / c) = (φ y - φ xStar) / c := by
          have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc_pos
          field_simp [hc_ne]
          ring
        linarith
      have hlt' : φ y - φ xStar < (n : ℝ) / (n + 1 : ℝ) * c := by
        have hmul := mul_lt_mul_of_pos_right hfrac hc_pos
        have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc_pos
        field_simp [hc_ne] at hmul
        have hn1pos : 0 < (n + 1 : ℝ) := by positivity
        have hmul' : (φ y - φ xStar) * (n + 1 : ℝ) < (n : ℝ) * c := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        have hdiv : φ y - φ xStar < ((n : ℝ) * c) / (n + 1 : ℝ) := by
          have hmul'' :
              (φ y - φ xStar) * (n + 1 : ℝ) <
                (((n : ℝ) * c) / (n + 1 : ℝ)) * (n + 1 : ℝ) := by
            simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
          have hdiv' :
              ((φ y - φ xStar) * (n + 1 : ℝ)) / (n + 1 : ℝ) <
                ((n : ℝ) * c) / (n + 1 : ℝ) := by
            exact (div_lt_iff₀ hn1pos).2 hmul''
          simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hge := happrox n
      linarith
  -- Rewrite the optimal-point value to the recorded optimum and isolate the desired gap.
  have hvalue :
      (σ / 2) * ‖y - xStar‖ ^ (2 : ℕ) ≤ (f y).toReal - (f xStar).toReal := by
    simpa [φ, c] using hfull
  rw [optimal_point_toReal_eq_fOpt h_problem hxStar] at hvalue
  simpa [sub_eq_add_neg] using hvalue

-- Proof sketch: combine Lemma 8.11 with strong convexity to sharpen the one-step estimate by the
-- quadratic growth term `(σ / 2) ‖x[n] - xStar‖²`, then substitute the stepsize
-- `t_n = 2 / (σ (n + 1))` and use the uniform norm bound `‖g_n‖ ≤ L_f`. Multiplying
-- by `n` and
-- summing from `0` to `k` telescopes the squared-distance terms and yields the prefix-best
-- objective gap estimate.
-- TODO: prove the weighted telescoping route using the strong-convexity bridge and the
-- rearranged one-step inequality from Agent C's plan.
/-- Theorem 8.31 (1): source part (a). Under Assumptions 8.7 and 8.12, if `f` is
`σ`-strongly convex with `σ > 0` and the projected subgradient method uses the stepsizes
`t_k = 2 / (σ (k + 1))`, then the best objective value attained among the first `k + 1` iterates
satisfies the `O(1 / k)` bound
`f_best^k - fOpt ≤ 2 L_f^2 / (σ (k + 1))`. -/
theorem projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt ≤
      2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  by_cases hk0 : k = 0
  · subst hk0
    have hbest0 :
        best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ 0 = (f x̄[0]).toReal := by
      unfold best_achieved_function_value
      simp
    have hgap0 :=
      stronglyConvexStepsize_gap_le_rearranged
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_subgrad h_stepsize hxStar 0
    -- At `k = 0`, the schedule-specific one-step inequality already bounds the initial gap.
    rw [hbest0]
    have hbase0 :
        (f x̄[0]).toReal - fOpt ≤
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
      have hfirst :
          (f x̄[0]).toReal - fOpt ≤ h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
        nlinarith [hgap0, sq_nonneg ‖x̄[0] - xStar‖, sq_nonneg ‖x̄[1] - xStar‖]
      have hnonneg :
          0 ≤ h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
        positivity
      have hsecond :
          h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) ≤
            2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
        calc
          h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) ≤
              h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) +
                h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
                  linarith
          _ = 2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
                ring
      exact hfirst.trans hsecond
    simpa using hbase0
  · let bestGap : ℝ :=
      best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have hweighted :=
      stronglyConvexStepsize_weightedGap_prefix_sum_le
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_subgrad h_stepsize hxStar k
    have hbest_sum :
        (Finset.sum (Finset.range (k + 1)) fun n ↦ (n : ℝ)) * bestGap ≤
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt)) := by
      calc
        (Finset.sum (Finset.range (k + 1)) fun n ↦ (n : ℝ)) * bestGap =
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) * bestGap) := by
              exact Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ (n : ℝ)) bestGap
        _ ≤ Finset.sum (Finset.range (k + 1))
              (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt)) := by
                refine Finset.sum_le_sum ?_
                intro n hn
                have hbest_le :
                    best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k ≤
                      (f x̄[n]).toReal :=
                  best_achieved_function_value_le_objective_value
                    (fun x : E ↦ (f x).toReal) x̄ k n hn
                exact mul_le_mul_of_nonneg_left
                  (sub_le_sub_right hbest_le fOpt)
                  (by positivity)
    have hmain :
        ((k : ℝ) * (k + 1 : ℝ) / 2) * bestGap ≤ h_bound.L_f ^ (2 : ℕ) * k / σ := by
      rw [sumRangeNatCast] at hbest_sum
      exact hbest_sum.trans hweighted
    have hkR_pos : 0 < (k : ℝ) := by
      exact_mod_cast hk_pos
    have hcoeff_pos : 0 < (k : ℝ) * (k + 1 : ℝ) / 2 := by
      positivity
    have hmain' :
        bestGap * ((k : ℝ) * (k + 1 : ℝ) / 2) ≤ h_bound.L_f ^ (2 : ℕ) * k / σ := by
      simpa [mul_comm] using hmain
    have hratio :
        (h_bound.L_f ^ (2 : ℕ) * k / σ) / ((k : ℝ) * (k + 1 : ℝ) / 2) =
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
      field_simp [hσ.ne', hkR_pos.ne']
    -- Divide by the positive weight sum `k (k + 1) / 2` to isolate the best gap.
    calc
      best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt = bestGap := by
        rfl
      _ ≤ (h_bound.L_f ^ (2 : ℕ) * k / σ) / ((k : ℝ) * (k + 1 : ℝ) / 2) :=
        (le_div_iff₀ hcoeff_pos).2 hmain'
      _ = 2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := hratio

-- Proof sketch: first apply clause (1) to the objective value of a prefix iterate attaining the
-- running minimum. Then use the quadratic growth estimate for the strongly convex constrained
-- objective `f + δ_C` at the optimal point `xStar` to convert the objective gap into the norm
-- bound `‖x[i] - xStar‖ ≤ 2 L_f / (σ √(k + 1))`.
-- TODO: combine the best-value bound with a constrained quadratic-growth lemma on `C`.
/-- Theorem 8.31 (2): source part (a). If `f` is `σ`-strongly convex with `σ > 0`, then any
iterate among the first `k + 1` steps that attains the best objective value on that prefix lies
within distance `2 L_f / (σ √(k + 1))` of the optimal point `xStar`. -/
theorem projected_subgradient_best_iterate_dist_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.range (k + 1))
    (hbest :
      (f x̄[i]).toReal = best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k) :
    ‖x̄[i] - xStar‖ ≤ 2 * h_bound.L_f / (σ * Real.sqrt (k + 1)) := by
  let _ := hi
  have hgap :
      (σ / 2) * ‖x̄[i] - xStar‖ ^ (2 : ℕ) ≤
        2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
    calc
      (σ / 2) * ‖x̄[i] - xStar‖ ^ (2 : ℕ) ≤ (f x̄[i]).toReal - fOpt := by
        exact
          objectiveGap_ge_halfSigmaSqdist_at_feasible
            (h_problem := h_problem) h_strong hσ hxStar (x[i]).property
      _ = best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt := by
        rw [hbest]
      _ ≤ 2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
        exact
          projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
            (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
            h_strong hσ h_subgrad h_stepsize hxStar k
  have hsq :
      ‖x̄[i] - xStar‖ ^ (2 : ℕ) ≤
        (2 * h_bound.L_f / (σ * Real.sqrt (k + 1))) ^ (2 : ℕ) := by
    have hdist_sq :
        ‖x̄[i] - xStar‖ ^ (2 : ℕ) ≤
          4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (k + 1 : ℝ)) := by
      have hsigma_half_pos : 0 < σ / 2 := by
        positivity
      have hgap' :
          ‖x̄[i] - xStar‖ ^ (2 : ℕ) * (σ / 2) ≤
            2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
        simpa [mul_comm] using hgap
      have hdiv :
          ‖x̄[i] - xStar‖ ^ (2 : ℕ) ≤
            (2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ))) / (σ / 2) :=
        (le_div_iff₀ hsigma_half_pos).2 hgap'
      have hratio :
          (2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ))) / (σ / 2) =
            4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (k + 1 : ℝ)) := by
        field_simp [pow_two, hσ.ne']
        ring
      rw [hratio] at hdiv
      exact hdiv
    have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
      exact Real.sq_sqrt (by positivity)
    have htarget_sq :
        (2 * h_bound.L_f / (σ * Real.sqrt (k + 1))) ^ (2 : ℕ) =
          4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (k + 1 : ℝ)) := by
      have hsqrt_ne : Real.sqrt ((k : ℝ) + 1) ≠ 0 := by
        positivity
      field_simp [pow_two, hσ.ne', hsqrt_ne]
      nlinarith [hsqrt_sq]
    rw [htarget_sq]
    exact hdist_sq
  have hright_nonneg : 0 ≤ 2 * h_bound.L_f / (σ * Real.sqrt (k + 1)) := by
    have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
      positivity
    have hden_pos : 0 < σ * Real.sqrt ((k : ℝ) + 1) := by
      positivity
    have hnum_nonneg : 0 ≤ 2 * h_bound.L_f := by
      nlinarith [h_bound.L_f_pos]
    exact div_nonneg hnum_nonneg hden_pos.le
  -- Convert the squared-distance estimate into the claimed norm bound.
  exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq

-- Proof sketch: start from the weighted inequality obtained in the proof of clause (1), divide by
-- `k (k + 1) / 2`, and rewrite the normalized coefficients as
-- `projected_subgradient_strongly_convex_average_weight k n`. Jensen's inequality for the convex
-- restriction of `f` then yields the same `O(1 / k)` bound for the averaged iterate.
-- TODO: prove the normalized weighted-gap estimate and then apply Jensen on the effective domain.
/-- Theorem 8.31 (3): source part (b). If `f` is `σ`-strongly convex with `σ > 0`, then for the
weighted average iterate
`x^(k) = ∑_{n=0}^k α_n^k x^n` with weights `α_n^k = 2n / (k (k + 1))` for `k > 0`, and
`x^(0) = x^0`, the objective gap also satisfies the bound
`f(x^(k)) - fOpt ≤ 2 L_f^2 / (σ (k + 1))`. -/
theorem projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (k : ℕ) :
    (f (x^(k))).toReal - fOpt ≤
      2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hbest0 :
        best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ 0 = (f x̄[0]).toReal := by
      unfold best_achieved_function_value
      simp
    have hbase :
        best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ 0 - fOpt ≤
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
      simpa using
        projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
          (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
          h_strong hσ h_subgrad h_stepsize hxStar 0
    -- The degenerate average is exactly the initial iterate, so part (1) applies verbatim.
    rw [hbest0] at hbase
    simpa [projected_subgradient_strongly_convex_average_iterate_zero] using hbase
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    rcases projected_subgradient_strongly_convex_average_weights_form_simplex
      (k := k) hk_pos with ⟨hnonneg, hsum⟩
    have hweighted :=
      stronglyConvexStepsize_weightedGap_prefix_sum_le
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_subgrad h_stepsize hxStar k
    have hweighted_avg :
        Finset.sum (Finset.range (k + 1))
            (fun n ↦ α[k](n) * ((f x̄[n]).toReal - fOpt)) ≤
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
      have hkR_pos : 0 < (k : ℝ) := by
        exact_mod_cast hk_pos
      have hrewrite :
          Finset.sum (Finset.range (k + 1))
              (fun n ↦ α[k](n) * ((f x̄[n]).toReal - fOpt)) =
            ((2 : ℝ) / (k * (k + 1) : ℝ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt)) := by
        simp_rw [projected_subgradient_strongly_convex_average_weight_eq_of_pos hk_pos]
        calc
          Finset.sum (Finset.range (k + 1))
              (fun n ↦
                (2 * (n : ℝ) / (k * (k + 1) : ℝ)) * ((f x̄[n]).toReal - fOpt)) =
              Finset.sum (Finset.range (k + 1))
                (fun n ↦
                  ((2 : ℝ) / (k * (k + 1) : ℝ)) *
                    ((n : ℝ) * ((f x̄[n]).toReal - fOpt))) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      field_simp [hkR_pos.ne']
          _ =
              ((2 : ℝ) / (k * (k + 1) : ℝ)) *
                Finset.sum (Finset.range (k + 1))
                  (fun n ↦ (n : ℝ) * ((f x̄[n]).toReal - fOpt)) := by
                    rw [← Finset.mul_sum]
      have hscaled :=
        mul_le_mul_of_nonneg_left hweighted (by positivity : 0 ≤ (2 : ℝ) / (k * (k + 1) : ℝ))
      rw [hrewrite]
      have hratio :
          ((2 : ℝ) / (k * (k + 1) : ℝ)) * (h_bound.L_f ^ (2 : ℕ) * k / σ) =
            2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
        field_simp [hσ.ne', hkR_pos.ne']
      simpa [hratio] using hscaled
    have hconv :
        ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) :=
      convexOn_toReal_of_is_convex_function h_problem.convex (fun z _ ↦ h_problem.ne_bot z)
    have hmem :
        ∀ n ∈ Finset.range (k + 1), x̄[n] ∈ effective_domain f := by
      intro n hn
      exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[n]).property)
    have hJensen :
        (f (x^(k))).toReal ≤
          Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f x̄[n]).toReal) := by
      rw [projected_subgradient_strongly_convex_average_iterate_eq_sum]
      simpa [smul_eq_mul] using hconv.map_sum_le hnonneg hsum hmem
    have hsum_const :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * fOpt) = fOpt := by
      calc
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * fOpt) =
            (Finset.sum (Finset.range (k + 1)) fun n ↦ α[k](n)) * fOpt := by
              exact (Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ α[k](n)) fOpt).symm
        _ = fOpt := by
              rw [hsum]
              ring
    have hgap_rewrite :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f x̄[n]).toReal) - fOpt =
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ α[k](n) * ((f x̄[n]).toReal - fOpt)) := by
      calc
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f x̄[n]).toReal) - fOpt =
            Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f x̄[n]).toReal) -
              Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * fOpt) := by
                rw [hsum_const]
        _ =
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ α[k](n) * ((f x̄[n]).toReal - fOpt)) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl ?_
                intro n hn
                ring
    -- Jensen converts the weighted value average into the value at the weighted iterate.
    calc
      (f (x^(k))).toReal - fOpt ≤
          Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f x̄[n]).toReal) - fOpt := by
            linarith
      _ =
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ α[k](n) * ((f x̄[n]).toReal - fOpt)) := hgap_rewrite
      _ ≤ 2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := hweighted_avg

-- Proof sketch: combine clause (3) with the same quadratic growth estimate used in clause (2) for
-- the strongly convex constrained objective `f + δ_C`. Rearranging the resulting inequality gives
-- the norm estimate for the averaged iterate.
-- TODO: combine the average-value bound with the same constrained quadratic-growth lemma as in
-- clause (2).
/-- Theorem 8.31 (4): source part (b). If `f` is `σ`-strongly convex with `σ > 0`, then the
weighted average iterate `x^(k)` lies within distance `2 L_f / (σ √(k + 1))` of the optimal
point `xStar`. -/
theorem projected_subgradient_average_dist_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖x^(k) - xStar‖ ≤
      2 * h_bound.L_f / (σ * Real.sqrt (k + 1)) := by
  by_cases hk0 : k = 0
  · subst hk0
    -- The degenerate average is the initial iterate, so the value-gap estimate closes directly.
    rw [projected_subgradient_strongly_convex_average_iterate_zero]
    have hgap :
        (σ / 2) * ‖x̄[0] - xStar‖ ^ (2 : ℕ) ≤
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
      calc
        (σ / 2) * ‖x̄[0] - xStar‖ ^ (2 : ℕ) ≤ (f x̄[0]).toReal - fOpt := by
          exact
            objectiveGap_ge_halfSigmaSqdist_at_feasible
              (h_problem := h_problem) h_strong hσ hxStar (x[0]).property
        _ = (f (x^(0))).toReal - fOpt := by
              rw [projected_subgradient_strongly_convex_average_iterate_zero]
        _ ≤ 2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
              simpa using
                projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
                  (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
                  h_strong hσ h_subgrad h_stepsize 0
    have hsq :
        ‖x̄[0] - xStar‖ ^ (2 : ℕ) ≤
          (2 * h_bound.L_f / (σ * Real.sqrt (0 + 1))) ^ (2 : ℕ) := by
      have hdist_sq :
          ‖x̄[0] - xStar‖ ^ (2 : ℕ) ≤
            4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (0 + 1 : ℝ)) := by
        have hsigma_half_pos : 0 < σ / 2 := by positivity
        have hgap' :
            ‖x̄[0] - xStar‖ ^ (2 : ℕ) * (σ / 2) ≤
              2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
          simpa [mul_comm] using hgap
        have hdiv :
            ‖x̄[0] - xStar‖ ^ (2 : ℕ) ≤
              (2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ))) / (σ / 2) :=
          (le_div_iff₀ hsigma_half_pos).2 hgap'
        have hratio :
            (2 * h_bound.L_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ))) / (σ / 2) =
              4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (0 + 1 : ℝ)) := by
          field_simp [pow_two, hσ.ne']
          ring
        rw [hratio] at hdiv
        exact hdiv
      have hsqrt_sq : Real.sqrt ((0 : ℝ) + 1) ^ (2 : ℕ) = (0 : ℝ) + 1 := by
        exact Real.sq_sqrt (by positivity)
      have htarget_sq :
          (2 * h_bound.L_f / (σ * Real.sqrt (0 + 1))) ^ (2 : ℕ) =
            4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (0 + 1 : ℝ)) := by
        have hsqrt_ne : Real.sqrt ((0 : ℝ) + 1) ≠ 0 := by positivity
        field_simp [pow_two, hσ.ne', hsqrt_ne]
        nlinarith [hsqrt_sq]
      rw [htarget_sq]
      exact hdist_sq
    have hright_nonneg : 0 ≤ 2 * h_bound.L_f / (σ * Real.sqrt (0 + 1)) := by
      have hden_pos : 0 < σ * Real.sqrt ((0 : ℝ) + 1) := by
        positivity
      have hnum_nonneg : 0 ≤ 2 * h_bound.L_f := by
        nlinarith [h_bound.L_f_pos]
      exact div_nonneg hnum_nonneg hden_pos.le
    simpa using (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    rcases projected_subgradient_strongly_convex_average_weights_form_simplex
      (k := k) hk_pos with ⟨hnonneg, hsum⟩
    have hxavgC : x^(k) ∈ C := by
      rw [projected_subgradient_strongly_convex_average_iterate_eq_sum]
      exact
        Convex.sum_mem (s := C) (t := Finset.range (k + 1))
          (w := fun n ↦ α[k](n)) (z := fun n ↦ x̄[n]) h_problem.feasible_convex
          hnonneg hsum (fun n hn ↦ (x[n]).property)
    have hgap :
        (σ / 2) * ‖x^(k) - xStar‖ ^ (2 : ℕ) ≤
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
      calc
        (σ / 2) * ‖x^(k) - xStar‖ ^ (2 : ℕ) ≤ (f (x^(k))).toReal - fOpt := by
          exact
            objectiveGap_ge_halfSigmaSqdist_at_feasible
              (h_problem := h_problem) h_strong hσ hxStar hxavgC
        _ ≤ 2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
          exact
            projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
              (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
              h_strong hσ h_subgrad h_stepsize k
    have hsq :
        ‖x^(k) - xStar‖ ^ (2 : ℕ) ≤
          (2 * h_bound.L_f / (σ * Real.sqrt (k + 1))) ^ (2 : ℕ) := by
      have hdist_sq :
          ‖x^(k) - xStar‖ ^ (2 : ℕ) ≤
            4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (k + 1 : ℝ)) := by
        have hsigma_half_pos : 0 < σ / 2 := by positivity
        have hgap' :
            ‖x^(k) - xStar‖ ^ (2 : ℕ) * (σ / 2) ≤
              2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
          simpa [mul_comm] using hgap
        have hdiv :
            ‖x^(k) - xStar‖ ^ (2 : ℕ) ≤
              (2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ))) / (σ / 2) :=
          (le_div_iff₀ hsigma_half_pos).2 hgap'
        have hratio :
            (2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ))) / (σ / 2) =
              4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (k + 1 : ℝ)) := by
          field_simp [pow_two, hσ.ne']
          ring
        rw [hratio] at hdiv
        exact hdiv
      have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
        exact Real.sq_sqrt (by positivity)
      have htarget_sq :
          (2 * h_bound.L_f / (σ * Real.sqrt (k + 1))) ^ (2 : ℕ) =
            4 * h_bound.L_f ^ (2 : ℕ) / (σ ^ (2 : ℕ) * (k + 1 : ℝ)) := by
        have hsqrt_ne : Real.sqrt ((k : ℝ) + 1) ≠ 0 := by positivity
        field_simp [pow_two, hσ.ne', hsqrt_ne]
        nlinarith [hsqrt_sq]
      rw [htarget_sq]
      exact hdist_sq
    have hright_nonneg : 0 ≤ 2 * h_bound.L_f / (σ * Real.sqrt (k + 1)) := by
      have hden_pos : 0 < σ * Real.sqrt ((k : ℝ) + 1) := by
        positivity
      have hnum_nonneg : 0 ≤ 2 * h_bound.L_f := by
        nlinarith [h_bound.L_f_pos]
      exact div_nonneg hnum_nonneg hden_pos.le
    -- The squared bound matches the square of the textbook radius exactly.
    exact (sq_le_sq₀ (norm_nonneg _) hright_nonneg).mp hsq

end
