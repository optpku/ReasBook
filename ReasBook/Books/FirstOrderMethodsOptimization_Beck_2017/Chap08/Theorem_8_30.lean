/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.HalfSquaredDiameterBound
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt Θ : ℝ}
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

/- The two textbook stepsize rules used in Theorem 8.30 are worth naming directly: they are
source-facing scalar formulas, not packaging scaffolding, and naming them keeps the theorem surface
short while preserving the distinction between the constant-`L_f` rule and the adaptive fallback
rule. -/

/-- The textbook stepsize `√(2 Θ) / (L_f √(k + 1))` from Theorem 8.30. -/
def projectedSubgradientHalfSquaredDiameterStepsize (Θ L : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (2 * Θ) / (L * Real.sqrt ((k : ℝ) + 1))

/-- The adaptive textbook stepsize from Theorem 8.30: use
`√(2 Θ) / (‖g_k‖ √(k + 1))` when the chosen subgradient is nonzero, and fall back to
`√(2 Θ) / (L_f √(k + 1))` when it vanishes. -/
def projectedSubgradientAdaptiveHalfSquaredDiameterStepsize (Θ L : ℝ) (k : ℕ) (v : E) : ℝ :=
  if ‖v‖ = 0 then
    projectedSubgradientHalfSquaredDiameterStepsize Θ L k
  else
    Real.sqrt (2 * Θ) / (‖v‖ * Real.sqrt ((k : ℝ) + 1))

/-- The projected subgradient method uses the constant-`L_f` half-squared-diameter stepsize rule
from Theorem 8.30 when `t_k = √(2 Θ) / (L_f √(k + 1))` for every `k`. -/
def projectedSubgradientUsesHalfSquaredDiameterStepsize
    (Θ L : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ k, t k = projectedSubgradientHalfSquaredDiameterStepsize Θ L k

/-- The projected subgradient method uses the adaptive half-squared-diameter stepsize rule from
Theorem 8.30 when `t_k` is the textbook fallback formula determined by the chosen vectors `v_k`.
-/
def projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize
    (Θ L : ℝ) (v : ℕ → E) (t : ℕ → ℝ) : Prop :=
  ∀ k, t k = projectedSubgradientAdaptiveHalfSquaredDiameterStepsize Θ L k (v k)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem projectedSubgradientAdaptiveHalfSquaredDiameterStepsize_zero
    (Θ L : ℝ) (k : ℕ) :
    projectedSubgradientAdaptiveHalfSquaredDiameterStepsize Θ L k (0 : E) =
      projectedSubgradientHalfSquaredDiameterStepsize Θ L k := by
  simp [projectedSubgradientAdaptiveHalfSquaredDiameterStepsize]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem projectedSubgradientAdaptiveHalfSquaredDiameterStepsize_of_ne_zero
    {Θ L : ℝ} {k : ℕ} {v : E} (hv : v ≠ 0) :
    projectedSubgradientAdaptiveHalfSquaredDiameterStepsize Θ L k v =
      Real.sqrt (2 * Θ) / (‖v‖ * Real.sqrt ((k : ℝ) + 1)) := by
  have hnorm : ‖v‖ ≠ 0 := by
    simpa [norm_eq_zero] using hv
  simp [projectedSubgradientAdaptiveHalfSquaredDiameterStepsize, hnorm]

theorem projectedSubgradientUsesHalfSquaredDiameterStepsize_apply
    {Θ L : ℝ} {t : ℕ → ℝ}
    (h : projectedSubgradientUsesHalfSquaredDiameterStepsize Θ L t) (k : ℕ) :
    t k = projectedSubgradientHalfSquaredDiameterStepsize Θ L k :=
  h k

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize_apply
    {Θ L : ℝ} {v : ℕ → E} {t : ℕ → ℝ}
    (h : projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize Θ L v t) (k : ℕ) :
    t k = projectedSubgradientAdaptiveHalfSquaredDiameterStepsize Θ L k (v k) :=
  h k

/- Theorem 8.30 is `source-facing`: it gives the `O(1 / √k)` convergence rate for the concrete
projected-subgradient iterates when the feasible set has a known half-squared-diameter bound `Θ`
and the stepsizes are chosen by either of the two textbook rules (8.39) or (8.40). The canonical
owners already present in Chapter 8 are the iterate sequence `projected_subgradient_method`, the
running-best value `best_achieved_function_value`, the standing problem class
`IsConstrainedConvexProblem`, and the norm-bound package `SubgradientNormBoundOn`. Since the
rate depends only on the explicit datum `C.HasHalfSquaredDiameterBound Θ`, the redundant
compactness hypothesis from the prose is not kept in the formal statement. -/

-- Proof sketch: pick an optimal point `xStar ∈ XStar` using `h_problem.optimal_set_nonempty`.
-- Apply Lemma 8.11 and sum the one-step inequality from indices `k / 2` through `k`. The
-- half-squared-diameter bound on `C` controls the telescoping distance term because every iterate
-- and every optimal point lie in `C`. Either stepsize choice gives both
-- `t n ^ 2 * ‖g_n‖ ^ 2 ≤ 2 Θ / (n + 1)` and
-- `√(2 Θ) / (L_f √(n + 1)) ≤ t n`; combine these estimates with the running-min inequality
-- for `best_achieved_function_value` and then invoke Lemma 8.27 (2) with `D = 1` to obtain
-- the stated `O(1 / √k)` bound.
/- Theorem 8.30: if `Θ` bounds the half squared diameter of the feasible set `C`, each chosen
direction satisfies `toDualMap ℝ E (g k (x[k])) ∈ ∂ₛf(x̄[k])`, and the
projected subgradient method uses either the textbook stepsizes
`t_k = √(2 Θ) / (L_f √(k + 1))` or
`t_k = √(2 Θ) / (‖f'(x^k)‖ √(k + 1))` with the fallback
`√(2 Θ) / (L_f √(k + 1))` when the chosen subgradient vanishes, then for every `k ≥ 2`
the best objective gap satisfies
`f_best^k - fOpt ≤ 2 (1 + log 3) L_f √(2 Θ) / √(k + 2)`. -/
/-- Helper for Theorem 8.30: the selected projected-subgradient directions inherit the uniform
bound `‖g_k‖ ≤ L_f` from Assumption 8.12. -/
private lemma selectedSubgradientNormLe
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ ∂ₛf(x̄[n]))
    (n : ℕ) :
    ‖g n (x[n])‖ ≤ h_bound.L_f := by
  -- Apply the standing norm bound to the strong-dual image of the chosen Euclidean vector.
  simpa using
    h_bound.norm_le (x := x̄[n]) (g := toDualMap ℝ E (g n (x[n])))
      (x[n]).property (h_subgrad n)

/-- Helper for Theorem 8.30: every feasible iterate still has objective value at least `fOpt`. -/
private lemma feasibleObjectiveValue_subFOpt_nonneg
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {y : E} (hy : y ∈ C) :
    0 ≤ (f y).toReal - fOpt := by
  -- Apply the optimal-value GLB to the feasible objective value and then descend from `EReal`.
  have hyImage : f y ∈ f '' C := by
    exact ⟨y, hy, rfl⟩
  have hlower : (fOpt : EReal) ≤ f y :=
    h_problem.optimal_value_isGLB.1 hyImage
  have hyDom : y ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hy)
  have hyTop : f y ≠ ⊤ := ne_of_lt hyDom
  have hyBot : f y ≠ ⊥ := h_problem.toIsProperExtendedRealFunction.ne_bot y
  have hreal : (fOpt : EReal) ≤ (((f y).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hyTop hyBot] using hlower
  have hreal' : fOpt ≤ (f y).toReal := EReal.coe_le_coe_iff.mp hreal
  linarith

/-- Helper for Theorem 8.30: the base half-squared-diameter stepsize is nonnegative whenever
`Θ ≥ 0`. -/
private lemma halfSquaredDiameterBaseStepsize_nonneg
    (hΘ_nonneg : 0 ≤ Θ) (n : ℕ) :
    0 ≤ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n := by
  -- Both the numerator and the denominator in the textbook formula are nonnegative.
  rw [projectedSubgradientHalfSquaredDiameterStepsize]
  refine div_nonneg (Real.sqrt_nonneg _) ?_
  exact mul_nonneg (le_of_lt h_bound.L_f_pos) (Real.sqrt_nonneg _)

/-- Helper for Theorem 8.30: either admissible stepsize rule dominates the base rule
`√(2 Θ) / (L_f √(n + 1))`. -/
private lemma halfSquaredDiameterBaseStepsize_le
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ ∂ₛf(x̄[n]))
    (hΘ_nonneg : 0 ≤ Θ)
    (h_stepsize :
      projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_bound.L_f t ∨
        projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize Θ h_bound.L_f
          (fun n ↦ g n (x[n])) t)
    (n : ℕ) :
    projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n ≤ t n := by
  rcases h_stepsize with h_const | h_adapt
  · -- Under the constant rule the comparison is exactly an equality.
    rw [projectedSubgradientUsesHalfSquaredDiameterStepsize_apply h_const n]
  · -- Under the adaptive rule, only the nonzero branch needs a denominator comparison.
    rw [projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize_apply h_adapt n]
    by_cases hg0 : g n (x[n]) = 0
    · rw [hg0, projectedSubgradientAdaptiveHalfSquaredDiameterStepsize_zero]
    · rw [projectedSubgradientAdaptiveHalfSquaredDiameterStepsize_of_ne_zero hg0]
      have hnorm_le :
          ‖g n (x[n])‖ ≤ h_bound.L_f :=
        selectedSubgradientNormLe
          (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
          h_subgrad n
      have hnum_nonneg : 0 ≤ Real.sqrt (2 * Θ) := Real.sqrt_nonneg _
      have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by
        apply Real.sqrt_pos.2
        positivity
      have hnorm_pos : 0 < ‖g n (x[n])‖ := by
        exact norm_pos_iff.mpr hg0
      have hdenom_le :
          ‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1) ≤
            h_bound.L_f * Real.sqrt ((n : ℝ) + 1) := by
        gcongr
      have hfrac :
          Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1)) ≤
            Real.sqrt (2 * Θ) / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)) := by
        exact div_le_div_of_nonneg_left hnum_nonneg (mul_pos hnorm_pos hsqrt_pos) hdenom_le
      simpa [projectedSubgradientHalfSquaredDiameterStepsize] using hfrac

/-- Helper for Theorem 8.30: either admissible stepsize rule puts the product
`t_n ‖g_n‖` in the common normal form `√(2 Θ) / √(n + 1)`. -/
private lemma halfSquaredDiameterStepsizeMulNorm_le
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ ∂ₛf(x̄[n]))
    (hΘ_nonneg : 0 ≤ Θ)
    (h_stepsize :
      projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_bound.L_f t ∨
        projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize Θ h_bound.L_f
          (fun n ↦ g n (x[n])) t)
    (n : ℕ) :
    t n * ‖g n (x[n])‖ ≤ Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1) := by
  rcases h_stepsize with h_const | h_adapt
  · -- Under the constant rule only the uniform norm bound needs to be inserted.
    rw [projectedSubgradientUsesHalfSquaredDiameterStepsize_apply h_const n]
    have hnorm_le :
        ‖g n (x[n])‖ ≤ h_bound.L_f :=
      selectedSubgradientNormLe
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_subgrad n
    have hfactor_nonneg :
        0 ≤ Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1)) := by
      exact div_nonneg (Real.sqrt_nonneg _) <|
        mul_nonneg (le_of_lt h_bound.L_f_pos) (Real.sqrt_nonneg _)
    have hmul :
        (Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) * ‖g n (x[n])‖ ≤
          (Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) * h_bound.L_f := by
      exact mul_le_mul_of_nonneg_left hnorm_le hfactor_nonneg
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by
      positivity
    calc
      projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n * ‖g n (x[n])‖
          = (Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) * ‖g n (x[n])‖ := by
              rw [projectedSubgradientHalfSquaredDiameterStepsize]
      _ ≤ (Real.sqrt (2 * Θ) / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) * h_bound.L_f := hmul
      _ = Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1) := by
          field_simp [h_bound.L_f_pos.ne', hsqrt_pos.ne']
  · -- Under the adaptive rule the nonzero branch cancels exactly, and the zero branch is trivial.
    rw [projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize_apply h_adapt n]
    by_cases hg0 : g n (x[n]) = 0
    · rw [hg0, projectedSubgradientAdaptiveHalfSquaredDiameterStepsize_zero]
      have hright_nonneg : 0 ≤ Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1) := by
        exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      simpa [projectedSubgradientHalfSquaredDiameterStepsize] using hright_nonneg
    · rw [projectedSubgradientAdaptiveHalfSquaredDiameterStepsize_of_ne_zero hg0]
      have hnorm_pos : 0 < ‖g n (x[n])‖ := by
        exact norm_pos_iff.mpr hg0
      have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by
        positivity
      calc
        (Real.sqrt (2 * Θ) / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1))) * ‖g n (x[n])‖
            = Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1) := by
                field_simp [hnorm_pos.ne', hsqrt_pos.ne']
        _ ≤ Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1) := le_rfl

/-- Helper for Theorem 8.30: under either admissible stepsize rule, the quadratic term in the
fundamental inequality is bounded by `2 Θ / (n + 1)`. -/
private lemma halfSquaredDiameterStepsizeNormSq_le
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ ∂ₛf(x̄[n]))
    (hΘ_nonneg : 0 ≤ Θ)
    (h_stepsize :
      projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_bound.L_f t ∨
        projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize Θ h_bound.L_f
          (fun n ↦ g n (x[n])) t)
    (n : ℕ) :
    (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ) ≤ (2 * Θ) / ((n : ℝ) + 1) := by
  -- Square the common product-form bound instead of normalizing each stepsize branch separately.
  have ht_nonneg : 0 ≤ t n := by
    exact le_trans
      (halfSquaredDiameterBaseStepsize_nonneg h_bound hΘ_nonneg n)
      (halfSquaredDiameterBaseStepsize_le
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_subgrad hΘ_nonneg h_stepsize n)
  have hmul :
      t n * ‖g n (x[n])‖ ≤ Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1) :=
    halfSquaredDiameterStepsizeMulNorm_le
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad hΘ_nonneg h_stepsize n
  have hmul_nonneg : 0 ≤ t n * ‖g n (x[n])‖ := by
    exact mul_nonneg ht_nonneg (norm_nonneg _)
  have hsq :
      (t n * ‖g n (x[n])‖) ^ (2 : ℕ) ≤
        (Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1)) ^ (2 : ℕ) := by
    simpa [pow_two] using mul_self_le_mul_self hmul_nonneg hmul
  have hright :
      (Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1)) ^ (2 : ℕ) =
        (2 * Θ) / ((n : ℝ) + 1) := by
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by
      positivity
    have hsqTheta : Real.sqrt (2 * Θ) * Real.sqrt (2 * Θ) = 2 * Θ := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Θ by nlinarith)]
    have hsqIndex :
        Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
    field_simp [pow_two, hsqrt_pos.ne']
    nlinarith
  calc
    (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ) = (t n * ‖g n (x[n])‖) ^ (2 : ℕ) := by
      ring
    _ ≤ (Real.sqrt (2 * Θ) / Real.sqrt ((n : ℝ) + 1)) ^ (2 : ℕ) := hsq
    _ = (2 * Θ) / ((n : ℝ) + 1) := hright

/-- Helper for Theorem 8.30: summing the one-step fundamental inequality over the interval
`{a, a + 1, …, a + m}` yields the expected telescoping remainder estimate. -/
private theorem weightedObjectiveGapIntervalWithRemainder_le
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ ∂ₛf(x̄[n]))
    (h_stepsize_nonneg : ∀ n, 0 ≤ t n)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (a m : ℕ) :
    Finset.sum (Finset.Icc a (a + m)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
        (1 / 2 : ℝ) * ‖x̄[a + m + 1] - xStar‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ‖x̄[a] - xStar‖ ^ (2 : ℕ) +
        (1 / 2 : ℝ) *
          Finset.sum (Finset.Icc a (a + m)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) := by
  induction m with
  | zero =>
      have hstep :=
        projected_subgradient_method_fundamental_inequality
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_subgrad hxStar a (h_stepsize_nonneg a)
      have hbase :
          t a * ((f x̄[a]).toReal - fOpt) + (1 / 2 : ℝ) * ‖x̄[a + 1] - xStar‖ ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * ‖x̄[a] - xStar‖ ^ (2 : ℕ) +
              (1 / 2 : ℝ) * ((t a) ^ (2 : ℕ) * ‖g a (x[a])‖ ^ (2 : ℕ)) := by
        nlinarith
      simpa using hbase
  | succ m ih =>
      have hstep :=
        projected_subgradient_method_fundamental_inequality
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_subgrad hxStar (a + m + 1) (h_stepsize_nonneg (a + m + 1))
      have hstep' :
          t (a + m + 1) * ((f x̄[a + m + 1]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x̄[a + m + 2] - xStar‖ ^ (2 : ℕ) ≤
            (1 / 2 : ℝ) * ‖x̄[a + m + 1] - xStar‖ ^ (2 : ℕ) +
              (1 / 2 : ℝ) *
                ((t (a + m + 1)) ^ (2 : ℕ) * ‖g (a + m + 1) (x[a + m + 1])‖ ^ (2 : ℕ)) := by
        nlinarith
      have hIcc :
          Finset.Icc a (a + m + 1) = insert (a + m + 1) (Finset.Icc a (a + m)) := by
        ext n
        simp [Finset.mem_Icc]
        omega
      calc
        Finset.sum (Finset.Icc a (a + m + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
            (1 / 2 : ℝ) * ‖x̄[a + m + 2] - xStar‖ ^ (2 : ℕ)
            =
          Finset.sum (Finset.Icc a (a + m)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
            (t (a + m + 1) * ((f x̄[a + m + 1]).toReal - fOpt) +
              (1 / 2 : ℝ) * ‖x̄[a + m + 2] - xStar‖ ^ (2 : ℕ)) := by
              rw [hIcc, Finset.sum_insert]
              · ring
              · simp
        _ ≤ (1 / 2 : ℝ) * ‖x̄[a] - xStar‖ ^ (2 : ℕ) +
            ((1 / 2 : ℝ) *
                Finset.sum (Finset.Icc a (a + m))
                  (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) +
              (1 / 2 : ℝ) *
                ((t (a + m + 1)) ^ (2 : ℕ) * ‖g (a + m + 1) (x[a + m + 1])‖ ^ (2 : ℕ))) := by
              nlinarith [ih, hstep']
        _ =
          (1 / 2 : ℝ) * ‖x̄[a] - xStar‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              Finset.sum (Finset.Icc a (a + m + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) := by
              rw [hIcc, Finset.sum_insert]
              · ring
              · simp

/-- Helper for Theorem 8.30: once `k ≥ 4`, the half-tail harmonic sum is bounded by `log 3`. -/
private lemma halfTailHarmonicSum_le_logThree_of_four_le
    (k : ℕ) (hk : 4 ≤ k) :
    Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / ((n : ℝ) + 1)) ≤ Real.log 3 := by
  -- Compare the harmonic half-tail with the integral of `x ↦ 1 / x` on the same interval.
  have hab : k / 2 ≤ k + 1 := by
    omega
  have hkhalf_pos : 0 < (((k / 2 : ℕ) : ℝ)) := by
    have hkhalf_nat : 1 ≤ k / 2 := by
      omega
    exact_mod_cast hkhalf_nat
  have hanti : AntitoneOn (fun x : ℝ ↦ 1 / x)
      (Set.Icc ((k / 2 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ))) := by
    -- The reciprocal is antitone on the positive interval starting at `k / 2`.
    simpa [one_div] using
      (inv_antitoneOn_Icc_right (a := ((k / 2 : ℕ) : ℝ)) (b := (((k + 1 : ℕ) : ℝ))) hkhalf_pos)
  have hsum :
      Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / ((n : ℝ) + 1)) ≤
        ∫ x in (((k / 2 : ℕ) : ℝ))..((k + 1 : ℕ) : ℝ), 1 / x := by
    -- Rewrite the tail sum as an `Ico` sum and apply the standard antitone comparison lemma.
    rw [show Finset.Icc (k / 2) k = Finset.Ico (k / 2) (k + 1) by
      ext n
      simp]
    simpa using
      (AntitoneOn.sum_le_integral_Ico (a := k / 2) (b := k + 1) (f := fun x : ℝ ↦ 1 / x)
        hab hanti)
  have hratio_le : (((k + 1 : ℕ) : ℝ) / (((k / 2 : ℕ) : ℝ))) ≤ 3 := by
    have hkhalf_pos' : 0 < (((k / 2 : ℕ) : ℝ)) := hkhalf_pos
    rw [div_le_iff₀ hkhalf_pos']
    norm_num
    exact_mod_cast (show k + 1 ≤ 3 * (k / 2) by omega)
  calc
    Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / ((n : ℝ) + 1))
        ≤ ∫ x in (((k / 2 : ℕ) : ℝ))..((k + 1 : ℕ) : ℝ), 1 / x := hsum
    _ = Real.log ((((k + 1 : ℕ) : ℝ) / (((k / 2 : ℕ) : ℝ))) : ℝ) := by
        rw [integral_one_div_of_pos hkhalf_pos]
        positivity
    _ ≤ Real.log 3 := Real.log_le_log (by positivity) hratio_le

/-- Helper for Theorem 8.30: for all `k ≥ 2`, the half-tail harmonic sum stays below `log 3`. -/
private lemma halfTailHarmonicSum_le_logThree
    {k : ℕ} (hk : 2 ≤ k) :
    Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / ((n : ℝ) + 1)) ≤ Real.log 3 := by
  by_cases hk4 : 4 ≤ k
  · -- The large-index range is handled by the integral comparison.
    exact halfTailHarmonicSum_le_logThree_of_four_le k hk4
  · -- Only the explicit cases `k = 2` and `k = 3` remain.
    have hk_cases : k = 2 ∨ k = 3 := by
      omega
    rcases hk_cases with rfl | rfl
    · have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 := by
        have htmp := Real.le_log_one_add_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num)
        norm_num at htmp ⊢
        exact htmp
      have hsum_eq :
          Finset.sum (Finset.Icc (2 / 2 : ℕ) 2) (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) = (5 : ℝ) / 6 := by
        have hIcc12 : Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) := by
          ext n
          simp [Finset.mem_Icc]
          omega
        calc
          Finset.sum (Finset.Icc (2 / 2 : ℕ) 2) (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
              = Finset.sum ({1, 2} : Finset ℕ) (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
                  rw [show (2 / 2 : ℕ) = 1 by norm_num, hIcc12]
          _ = (1 / (2 : ℝ)) + 1 / 3 := by
              norm_num
          _ = (5 : ℝ) / 6 := by
              norm_num
      rw [hsum_eq]
      linarith
    · have hlog32 : (2 : ℝ) / 5 ≤ Real.log (3 / 2 : ℝ) := by
        have htmp := Real.le_log_one_add_of_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        norm_num at htmp ⊢
        exact htmp
      have hlog43 : (2 : ℝ) / 7 ≤ Real.log (4 / 3 : ℝ) := by
        have htmp := Real.le_log_one_add_of_nonneg (show 0 ≤ (1 / 3 : ℝ) by norm_num)
        norm_num at htmp ⊢
        exact htmp
      have hlog3_lower :
          (13 : ℝ) / 12 ≤
            Real.log (3 / 2 : ℝ) + Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) := by
        nlinarith
      have hlog3_eq :
          Real.log 3 =
            Real.log (3 / 2 : ℝ) + Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) := by
        calc
          Real.log 3 = Real.log ((3 / 2 : ℝ) * ((4 / 3 : ℝ) * (3 / 2 : ℝ))) := by norm_num
          _ = Real.log (3 / 2 : ℝ) + Real.log ((4 / 3 : ℝ) * (3 / 2 : ℝ)) := by
              rw [Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (by norm_num : ((4 / 3 : ℝ) * (3 / 2 : ℝ)) ≠ 0)]
          _ = Real.log (3 / 2 : ℝ) + (Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ)) := by
              rw [Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
          _ = Real.log (3 / 2 : ℝ) + Real.log (4 / 3 : ℝ) + Real.log (3 / 2 : ℝ) := by ring
      have hsum_eq :
          Finset.sum (Finset.Icc (3 / 2 : ℕ) 3) (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) = (13 : ℝ) / 12 := by
        have hIcc13 : Finset.Icc (1 : ℕ) 3 = ({1, 2, 3} : Finset ℕ) := by
          ext n
          simp [Finset.mem_Icc]
          omega
        calc
          Finset.sum (Finset.Icc (3 / 2 : ℕ) 3) (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))
              = Finset.sum ({1, 2, 3} : Finset ℕ) (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
                  rw [show (3 / 2 : ℕ) = 1 by norm_num, hIcc13]
          _ = (1 / (2 : ℝ)) + 1 / 3 + 1 / 4 := by
              norm_num
          _ = (13 : ℝ) / 12 := by
              norm_num
      rw [hsum_eq]
      rw [hlog3_eq]
      exact hlog3_lower

/-- Helper for Theorem 8.30: the inverse-sqrt half-tail controls the corresponding sum of the
named base stepsizes from below. -/
private lemma halfTailBaseStepsizeSum_lower
    (k : ℕ) :
    (Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4) ≤
      Finset.sum (Finset.Icc (k / 2) k)
        (fun n ↦ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n) := by
  -- Pull out the constant factor and reuse the inverse-sqrt lower bound on the half-tail.
  have hterm :
      ∀ n ∈ Finset.Icc (k / 2) k,
        1 / Real.sqrt ((k : ℝ) + 2) ≤ 1 / Real.sqrt ((n : ℝ) + 1) := by
    intro n hn
    have hn_le : (n : ℝ) + 1 ≤ (k : ℝ) + 2 := by
      have hn_nat : n ≤ k := (Finset.mem_Icc.mp hn).2
      have hn_real : (n : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hn_nat
      linarith
    have hsqrt_le : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 2) := by
      exact Real.sqrt_le_sqrt hn_le
    exact one_div_le_one_div_of_le (by positivity) hsqrt_le
  have hsum :
      Finset.sum (Finset.Icc (k / 2) k) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 2)) ≤
        Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) := by
    simpa using Finset.sum_le_sum hterm
  have hcard_bound :
      Real.sqrt ((k : ℝ) + 2) / 4 ≤
        Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) := by
    have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
      positivity
    have hcount :
        ((k : ℝ) + 2) ≤ 4 * ((Finset.Icc (k / 2) k).card : ℝ) := by
      have hcount_nat : k + 2 ≤ 4 * (Finset.Icc (k / 2) k).card := by
        simpa [Nat.card_Icc] using (show k + 2 ≤ 4 * (k + 1 - k / 2) by omega)
      exact_mod_cast hcount_nat
    have hcount_div :
        Real.sqrt ((k : ℝ) + 2) / 4 ≤
          ((Finset.Icc (k / 2) k).card : ℝ) / Real.sqrt ((k : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hsqrt_pos]
      nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) + 2 by positivity), hcount]
    calc
      Real.sqrt ((k : ℝ) + 2) / 4
          ≤ ((Finset.Icc (k / 2) k).card : ℝ) / Real.sqrt ((k : ℝ) + 2) := hcount_div
      _ = Finset.sum (Finset.Icc (k / 2) k) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 2)) := by
          simp [div_eq_mul_inv]
      _ ≤ Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) := hsum
  have hfactor_nonneg : 0 ≤ Real.sqrt (2 * Θ) / h_bound.L_f := by
    exact div_nonneg (Real.sqrt_nonneg _) (le_of_lt h_bound.L_f_pos)
  calc
    (Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)
        ≤
          (Real.sqrt (2 * Θ) / h_bound.L_f) *
            Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hcard_bound hfactor_nonneg
    _ = Finset.sum (Finset.Icc (k / 2) k)
          (fun n ↦ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [projectedSubgradientHalfSquaredDiameterStepsize]
        field_simp [h_bound.L_f_pos.ne', show Real.sqrt ((n : ℝ) + 1) ≠ 0 by positivity]
/-- Theorem 8.30: if `Θ` bounds the half squared diameter of the feasible set `C`, each chosen
direction satisfies `toDualMap ℝ E (g k (x[k])) ∈ ∂ₛf(x̄[k])`, and the projected subgradient
method uses either textbook half-squared-diameter stepsize rule, then for every `k ≥ 2` the best
objective gap is `O(1 / √k)` with the stated explicit constant. -/
theorem projected_subgradient_best_value_gap_le_of_half_squared_diameter_stepsizes
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ ∂ₛf(x̄[n]))
    (hΘ : C.HasHalfSquaredDiameterBound Θ)
    (h_stepsize :
      projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_bound.L_f t ∨
        projectedSubgradientUsesAdaptiveHalfSquaredDiameterStepsize Θ h_bound.L_f
          (fun n ↦ g n (x[n])) t)
    {k : ℕ} (hk : 2 ≤ k) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt ≤
      (2 * (1 + Real.log 3)) * h_bound.L_f * Real.sqrt (2 * Θ) /
        Real.sqrt ((k : ℝ) + 2) := by
  -- Route correction: finish entirely from the local half-tail weighted-gap comparison, rather
  -- than routing through the currently broken standalone `Lemma_8_27` file.
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStarC : xStar ∈ C := hxStar_data.1
  have hΘ_nonneg : 0 ≤ Θ := by
    have hself := hΘ.bound x0.property x0.property
    nlinarith [hself]
  let tail : Finset ℕ := Finset.Icc (k / 2) k
  let bestGap : ℝ :=
    best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt
  have hbest_nonneg : 0 ≤ bestGap := by
    -- The running best value is still bounded below by the optimal value.
    have hbest_lower :
        fOpt ≤ best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k := by
      unfold best_achieved_function_value
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
      simpa using
        feasibleObjectiveValue_subFOpt_nonneg h_problem (x[n]).property
    dsimp [bestGap]
    linarith
  by_cases hTheta_zero : Θ = 0
  · -- If `Θ = 0`, the feasible set collapses to one point, so the running best value is already optimal.
    have hdist0 : (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [hTheta_zero] using hΘ.bound x0.property hxStarC
    have hnorm0 : ‖(x0 : E) - xStar‖ = 0 := by
      nlinarith [hdist0, sq_nonneg ‖(x0 : E) - xStar‖]
    have hx0_eq : (x0 : E) = xStar := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
    have hbest_le_opt :
        best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k ≤ fOpt := by
      -- Compare the running minimum with the initial iterate, which equals the optimal point.
      calc
        best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k ≤ (f x̄[0]).toReal := by
          exact
            best_achieved_function_value_le_objective_value
              (fun x : E ↦ (f x).toReal) x̄ k 0 (by simp)
        _ = (f (x0 : E)).toReal := by
            rw [projected_subgradient_method_iterate_zero C h_problem.feasible_nonempty
              h_problem.feasible_closed h_problem.feasible_convex g t x0]
        _ = (f xStar).toReal := by rw [hx0_eq]
        _ = fOpt := optimal_point_toReal_eq_fOpt h_problem hxStar
    have hright_zero :
        (2 * (1 + Real.log 3)) * h_bound.L_f * Real.sqrt (2 * Θ) /
          Real.sqrt ((k : ℝ) + 2) = 0 := by
      simp [hTheta_zero]
    rw [hright_zero]
    dsimp [bestGap] at hbest_nonneg ⊢
    linarith
  · have hTheta_ne : 0 ≠ Θ := by
      simpa [eq_comm] using hTheta_zero
    have hTheta_pos : 0 < Θ := lt_of_le_of_ne hΘ_nonneg hTheta_ne
    have hsqrtTheta_pos : 0 < Real.sqrt (2 * Θ) := by
      apply Real.sqrt_pos.2
      nlinarith
    have hstepsize_nonneg : ∀ n, 0 ≤ t n := by
      intro n
      exact le_trans
        (halfSquaredDiameterBaseStepsize_nonneg h_bound hΘ_nonneg n)
        (halfSquaredDiameterBaseStepsize_le
          (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
          h_subgrad hΘ_nonneg h_stepsize n)
    have hinterval :
        Finset.sum tail (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) +
            (1 / 2 : ℝ) * ‖x̄[k + 1] - xStar‖ ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * ‖x̄[k / 2] - xStar‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) *
              Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) := by
      -- Summing Lemma 8.11 over the half-tail gives the weighted objective-gap estimate.
      simpa [tail, Nat.add_sub_of_le (Nat.div_le_self k 2), add_assoc] using
        weightedObjectiveGapIntervalWithRemainder_le
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_subgrad hstepsize_nonneg hxStar (k / 2) (k - k / 2)
    have hquad_sum_le :
        Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
          Finset.sum tail (fun n ↦ (2 * Θ) / ((n : ℝ) + 1)) := by
      -- Replace each quadratic term by the common `2 Θ / (n + 1)` bound.
      refine Finset.sum_le_sum ?_
      intro n hn
      exact
        halfSquaredDiameterStepsizeNormSq_le
          (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
          h_subgrad hΘ_nonneg h_stepsize n
    have hquad_tail_le :
        (1 / 2 : ℝ) *
            Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
          Θ * Finset.sum tail (fun n ↦ 1 / ((n : ℝ) + 1)) := by
      -- After summing the quadratic bounds, factor out the common `Θ`.
      calc
        (1 / 2 : ℝ) *
            Finset.sum tail (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ))
            ≤
          (1 / 2 : ℝ) * Finset.sum tail (fun n ↦ (2 * Θ) / ((n : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hquad_sum_le (by norm_num : 0 ≤ (1 / 2 : ℝ))
        _ = Finset.sum tail (fun n ↦ (1 / 2 : ℝ) * ((2 * Θ) / ((n : ℝ) + 1))) := by
            rw [Finset.mul_sum]
        _ = Finset.sum tail (fun n ↦ Θ * (1 / ((n : ℝ) + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]
        _ = Θ * Finset.sum tail (fun n ↦ 1 / ((n : ℝ) + 1)) := by
            symm
            rw [Finset.mul_sum]
    have hstart_le :
        (1 / 2 : ℝ) * ‖x̄[k / 2] - xStar‖ ^ (2 : ℕ) ≤ Θ := by
      -- The half-squared-diameter bound controls the initial point of the half-tail.
      exact hΘ.bound (x[k / 2]).property hxStarC
    have hrest_nonneg :
        0 ≤ (1 / 2 : ℝ) * ‖x̄[k + 1] - xStar‖ ^ (2 : ℕ) := by
      positivity
    have hweighted_tail_le :
        Finset.sum tail (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) ≤
          Θ + Θ * Finset.sum tail (fun n ↦ 1 / ((n : ℝ) + 1)) := by
      -- Drop the nonnegative remainder term and use the diameter and quadratic tail bounds.
      nlinarith [hinterval, hstart_le, hquad_tail_le, hrest_nonneg]
    have hbase_best_le :
        Finset.sum tail (fun n ↦ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n * bestGap) ≤
          Finset.sum tail (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
      -- Compare each tail summand with the running-best gap and then with the actual stepsize.
      refine Finset.sum_le_sum ?_
      intro n hn
      have hn_range : n ∈ Finset.range (k + 1) := by
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp (by simpa [tail] using hn)).2)
      have hbest_le :
          best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k ≤ (f x̄[n]).toReal :=
        best_achieved_function_value_le_objective_value
          (fun x : E ↦ (f x).toReal) x̄ k n hn_range
      have hgap_nonneg : 0 ≤ (f x̄[n]).toReal - fOpt := by
        simpa using
          feasibleObjectiveValue_subFOpt_nonneg h_problem (x[n]).property
      have hbase_nonneg :
          0 ≤ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n :=
        halfSquaredDiameterBaseStepsize_nonneg h_bound hΘ_nonneg n
      have hbase_le :
          projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n ≤ t n :=
        halfSquaredDiameterBaseStepsize_le
          (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
          h_subgrad hΘ_nonneg h_stepsize n
      calc
        projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n * bestGap
            ≤
          projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n *
            ((f x̄[n]).toReal - fOpt) := by
                exact mul_le_mul_of_nonneg_left (sub_le_sub_right hbest_le fOpt) hbase_nonneg
        _ ≤ t n * ((f x̄[n]).toReal - fOpt) := by
            exact mul_le_mul_of_nonneg_right hbase_le hgap_nonneg
    have hbase_sum_best_le :
        (Finset.sum tail (fun n ↦ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n)) * bestGap ≤
          Finset.sum tail (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
      simpa [bestGap, tail, mul_comm, mul_left_comm, mul_assoc, Finset.sum_mul] using
        hbase_best_le
    have hbase_sum_lower :
        (Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4) ≤
          Finset.sum tail (fun n ↦ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n) := by
      simpa [tail] using halfTailBaseStepsizeSum_lower (h_bound := h_bound) (Θ := Θ) k
    have hscaled_best_le :
        ((Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)) * bestGap ≤
          Finset.sum tail (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
      -- Insert the explicit lower bound for the half-tail sum of base stepsizes.
      have hmul_lower :
          ((Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)) * bestGap ≤
            (Finset.sum tail (fun n ↦ projectedSubgradientHalfSquaredDiameterStepsize Θ h_bound.L_f n)) * bestGap := by
        exact mul_le_mul_of_nonneg_right hbase_sum_lower hbest_nonneg
      exact hmul_lower.trans hbase_sum_best_le
    have hharmonic_le :
        Finset.sum tail (fun n ↦ 1 / ((n : ℝ) + 1)) ≤ Real.log 3 := by
      simpa [tail] using halfTailHarmonicSum_le_logThree (k := k) hk
    have hupper_const :
        Θ + Θ * Finset.sum tail (fun n ↦ 1 / ((n : ℝ) + 1)) ≤ Θ * (1 + Real.log 3) := by
      -- The half-tail harmonic sum contributes at most the textbook `log 3` term.
      nlinarith [mul_le_mul_of_nonneg_left hharmonic_le hΘ_nonneg]
    have hmain_mul :
        ((Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)) * bestGap ≤
          Θ * (1 + Real.log 3) := by
      exact hscaled_best_le.trans (hweighted_tail_le.trans hupper_const)
    have hcoeff_pos :
        0 < (Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4) := by
      have hquot_pos : 0 < Real.sqrt (2 * Θ) / h_bound.L_f := by
        exact div_pos hsqrtTheta_pos h_bound.L_f_pos
      have hquarter_pos : 0 < Real.sqrt ((k : ℝ) + 2) / 4 := by
        positivity
      exact mul_pos hquot_pos hquarter_pos
    have hbest_div :
        bestGap ≤
          (Θ * (1 + Real.log 3)) /
            ((Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)) := by
      -- Divide through by the positive explicit denominator lower bound.
      rw [le_div_iff₀ hcoeff_pos]
      simpa [bestGap, mul_comm, mul_left_comm, mul_assoc] using hmain_mul
    have hratio_eq :
        (Θ * (1 + Real.log 3)) /
            ((Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)) =
          (2 * (1 + Real.log 3)) * h_bound.L_f * Real.sqrt (2 * Θ) /
            Real.sqrt ((k : ℝ) + 2) := by
      have hsqrt_index_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
        positivity
      field_simp [hsqrtTheta_pos.ne', h_bound.L_f_pos.ne', hsqrt_index_pos.ne']
      have hsqTheta : Real.sqrt (Θ * 2) ^ (2 : ℕ) = Θ * 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [hsqTheta]
    calc
      best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt = bestGap := by
        rfl
      _ ≤
          (Θ * (1 + Real.log 3)) /
            ((Real.sqrt (2 * Θ) / h_bound.L_f) * (Real.sqrt ((k : ℝ) + 2) / 4)) := hbest_div
      _ =
          (2 * (1 + Real.log 3)) * h_bound.L_f * Real.sqrt (2 * Θ) /
            Real.sqrt ((k : ℝ) + 2) := hratio_eq

end
