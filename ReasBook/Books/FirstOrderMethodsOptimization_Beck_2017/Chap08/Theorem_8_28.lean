/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_24
import Mathlib.Analysis.Convex.Jensen
import Mathlib.NumberTheory.Harmonic.Bounds

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open scoped BigOperators

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
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

/- Theorem 8.28 is `source-facing`: it gives the explicit `O(log k / √k)` convergence rate for
the concrete projected-subgradient iterates under the textbook's dynamic stepsize rule. Domain
sampling against the nearby Chapter 8 API shows that the right owner abstractions are the
projected iterate sequence `projected_subgradient_method`, the running-best value
`best_achieved_function_value`, the standing problem class `IsConstrainedConvexProblem`, and the
bound package `SubgradientNormBoundOn`. The averaged iterate `x^(k)` is a genuine textbook object,
and its normalization uses the concrete stepsize prefix sums `T_k = ∑_{n=0}^k t_n`, so both are
exposed directly rather than via an existential or package wrapper. -/

/-- The textbook dynamic stepsize from Theorem 8.28: use `1 / L` when the chosen subgradient
vanishes, and otherwise use `1 / (‖v‖ √(k + 1))`. -/
def projectedSubgradientDynamicStepsize (L : ℝ) (k : ℕ) (v : E) : ℝ :=
  if ‖v‖ = 0 then
    1 / L
  else
    1 / (‖v‖ * Real.sqrt ((k : ℝ) + 1))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem projectedSubgradientDynamicStepsize_zero
    (L : ℝ) (k : ℕ) :
    projectedSubgradientDynamicStepsize L k (0 : E) = 1 / L := by
  simp [projectedSubgradientDynamicStepsize]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem projectedSubgradientDynamicStepsize_of_ne_zero
    {L : ℝ} {k : ℕ} {v : E} (hv : v ≠ 0) :
    projectedSubgradientDynamicStepsize L k v =
      1 / (‖v‖ * Real.sqrt ((k : ℝ) + 1)) := by
  have hnorm : ‖v‖ ≠ 0 := by
    simpa [norm_eq_zero] using hv
  simp [projectedSubgradientDynamicStepsize, hnorm]

/-- The partial sums `T_k = ∑_{n=0}^k t_n` of the projected-subgradient stepsizes. -/
def projected_subgradient_stepsize_prefix_sum (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun n ↦ t n

namespace ProjectedSubgradientErgodicNotation

/-- Scoped notation for the projected-subgradient stepsize prefix sums `T_k = ∑_{n=0}^k t_n`. -/
scoped notation "T[" t "](" k ")" =>
  projected_subgradient_stepsize_prefix_sum t k

end ProjectedSubgradientErgodicNotation

open scoped ProjectedSubgradientErgodicNotation

local notation "T_" k => (T[t](k))

/-- The initial stepsize prefix sum is `T_0 = t_0`. -/
@[simp] theorem projected_subgradient_stepsize_prefix_sum_zero :
    (T_ 0) = t 0 := by
  simp [projected_subgradient_stepsize_prefix_sum]

-- Proof sketch: split the sum over `Finset.range (k + 2)` into the prefix
-- `Finset.range (k + 1)` and the last term `k + 1`.
/-- The stepsize prefix sums satisfy `T_{k+1} = T_k + t_{k+1}`. -/
theorem projected_subgradient_stepsize_prefix_sum_succ (k : ℕ) :
    (T_ (k + 1)) = (T_ k) + t (k + 1) := by
  simpa [projected_subgradient_stepsize_prefix_sum, Nat.add_assoc] using
    Finset.sum_range_succ (fun n ↦ t n) (k + 1)

/-- The stepsize-weighted average iterate
`x^(k) = T_k⁻¹ • ∑_{n=0}^k t_n x^n`, where `T_k = ∑_{n=0}^k t_n`,
used in the ergodic projected-subgradient rate. -/
def projected_subgradient_stepsize_average_iterate
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C) (k : ℕ) : E :=
  (projected_subgradient_stepsize_prefix_sum t k)⁻¹ •
    Finset.sum (Finset.range (k + 1)) fun n ↦
      t n •
        projected_subgradient_method_iterate C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex g t x0 n

namespace ProjectedSubgradientErgodicNotation

/-- Scoped notation for the projected-subgradient weighted averages `x^(k)` from Theorem 8.28. -/
scoped notation "x^[" h_problem ", " g ", " t ", " x0 "](" k ")" =>
  projected_subgradient_stepsize_average_iterate h_problem g t x0 k

end ProjectedSubgradientErgodicNotation

local notation "x^(" k ")" => x^[h_problem, g, t, x0](k)

/-- Evaluating the stepsize-weighted average iterate at `k` gives the normalized weighted sum
`T_k⁻¹ • ∑_{n=0}^k t_n x^n`. -/
theorem projected_subgradient_stepsize_average_iterate_eq_sum
    (k : ℕ) :
    x^(k) = ((T_ k))⁻¹ • Finset.sum (Finset.range (k + 1)) fun n ↦ t n • x̄[n] := by
  rfl

-- Proof sketch: unfold `projected_subgradient_stepsize_average_iterate`; when `k = 0`, both
-- prefix sums have a single term indexed by `0`, so the weighted average is
-- `(t 0)⁻¹ • (t 0 • x^0)`. Cancel the nonzero scalar using `ht0`.
/-- If the initial stepsize is nonzero, the stepsize-weighted average iterate at `k = 0` is the
initial iterate `x^0`. -/
theorem projected_subgradient_stepsize_average_iterate_zero
    (ht0 : t 0 ≠ 0) :
    x^(0) = x̄[0] := by
  -- The average at `k = 0` is the one-term normalized weighted sum.
  rw [projected_subgradient_stepsize_average_iterate_eq_sum]
  rw [projected_subgradient_stepsize_prefix_sum_zero]
  simp [ht0]

omit [CompleteSpace E] in
/-- Helper for Theorem 8.28: every feasible point has objective value at least `fOpt`. -/
lemma feasible_objective_value_sub_fOpt_nonneg
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt) {y : E}
    (hy : y ∈ C) :
    0 ≤ (f y).toReal - fOpt := by
  have hyImage : f y ∈ f '' C := by
    exact ⟨y, hy, rfl⟩
  have hlower : (fOpt : EReal) ≤ f y :=
    h_problem.optimal_value_isGLB.left hyImage
  have hyDom : y ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hy)
  have hyTop : f y ≠ ⊤ := ne_of_lt hyDom
  have hyBot : f y ≠ ⊥ := h_problem.ne_bot y
  have hreal : (fOpt : EReal) ≤ (((f y).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hyTop hyBot] using hlower
  have hreal' : fOpt ≤ (f y).toReal := EReal.coe_le_coe_iff.mp hreal
  linarith

/-- Helper for Theorem 8.28: the dynamic stepsize makes each weighted squared selected
subgradient term at most the corresponding harmonic summand. -/
lemma dynamicStepsize_sq_mul_norm_sq_le_inv
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    (n : ℕ) :
    (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ) ≤ 1 / ((n : ℝ) + 1) := by
  by_cases hg0 : g n (x[n]) = 0
  · -- In the zero-subgradient branch, the numerator vanishes.
    rw [h_stepsize n, hg0, projectedSubgradientDynamicStepsize_zero]
    have hzero : (1 / h_bound.L_f) ^ (2 : ℕ) * ‖(0 : E)‖ ^ (2 : ℕ) = 0 := by
      simp
    have hright : 0 ≤ 1 / ((n : ℝ) + 1) := by
      positivity
    nlinarith [hzero, hright]
  · -- In the nonzero branch, the formula is exact after canceling the norm and the square root.
    have hstep :
        t n = 1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)) := by
      rw [h_stepsize n]
      exact projectedSubgradientDynamicStepsize_of_ne_zero hg0
    have hnorm : ‖g n (x[n])‖ ≠ 0 := by
      simpa [norm_eq_zero] using hg0
    have hsqrt : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
    calc
      (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ) =
          (1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1))) ^ (2 : ℕ) *
            ‖g n (x[n])‖ ^ (2 : ℕ) := by
        rw [hstep]
      _ = 1 / (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) := by
        field_simp [hnorm, hsqrt]
      _ = 1 / ((n : ℝ) + 1) := by
        have hsq :
            Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 := by
          simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity))
        rw [hsq]
      _ ≤ 1 / ((n : ℝ) + 1) := by
        exact le_rfl

/-- Helper for Theorem 8.28: the dynamic stepsize is bounded below by the inverse-square-root
rule controlled by `L_f`. -/
lemma dynamicStepsize_invSqrt_lower_bound
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    (n : ℕ) :
    1 / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1)) ≤ t n := by
  by_cases hg0 : g n (x[n]) = 0
  · -- In the zero branch, compare `1 / (L_f √(n + 1))` with `1 / L_f`.
    rw [h_stepsize n, hg0, projectedSubgradientDynamicStepsize_zero]
    have hsqrt_one_le : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1), hsqrt_nonneg]
    have hden :
        h_bound.L_f ≤ h_bound.L_f * Real.sqrt ((n : ℝ) + 1) := by
      nlinarith [h_bound.L_f_pos, hsqrt_one_le]
    exact one_div_le_one_div_of_le h_bound.L_f_pos hden
  · -- In the nonzero branch, use the subgradient norm bound `‖g_n‖ ≤ L_f`.
    have hstep :
        t n = 1 / (‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1)) := by
      rw [h_stepsize n]
      exact projectedSubgradientDynamicStepsize_of_ne_zero hg0
    have hgradNorm :
        ‖g n (x[n])‖ ≤ h_bound.L_f := by
      simpa using h_bound.norm_le (x := x̄[n]) ((x[n]).property) (h_subgrad n)
    have hsqrtPos : 0 < Real.sqrt ((n : ℝ) + 1) := by
      exact Real.sqrt_pos.2 (by positivity)
    have hnormPos : 0 < ‖g n (x[n])‖ := by
      exact norm_pos_iff.mpr hg0
    have hden :
        ‖g n (x[n])‖ * Real.sqrt ((n : ℝ) + 1) ≤
          h_bound.L_f * Real.sqrt ((n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right hgradNorm hsqrtPos.le
    rw [hstep]
    exact one_div_le_one_div_of_le
      (mul_pos hnormPos hsqrtPos)
      hden

/-- Helper for Theorem 8.28: the dynamic stepsizes are strictly positive. -/
lemma dynamicStepsize_pos
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    (n : ℕ) :
    0 < t n := by
  have hlower :=
    dynamicStepsize_invSqrt_lower_bound
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize n
  have hlowerPos : 0 < 1 / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1)) := by
    have hdenPos : 0 < h_bound.L_f * Real.sqrt ((n : ℝ) + 1) := by
      exact mul_pos h_bound.L_f_pos (Real.sqrt_pos.2 (by positivity))
    exact one_div_pos.mpr hdenPos
  exact lt_of_lt_of_le hlowerPos hlower

/-- Helper for Theorem 8.28: the weighted average iterate is exactly the `Finset.centerMass`
representation needed for Jensen's inequality. -/
lemma projected_subgradient_stepsize_average_iterate_eq_centerMass
    (k : ℕ) :
    x^(k) = (Finset.range (k + 1)).centerMass (fun n ↦ t n) (fun n ↦ x̄[n]) := by
  -- This is just the owner definition of `Finset.centerMass`.
  simpa [Finset.centerMass, projected_subgradient_stepsize_prefix_sum] using
    projected_subgradient_stepsize_average_iterate_eq_sum
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) k

/-- Helper for Theorem 8.28: the prefix harmonic sum `∑_{n=0}^k 1 / (n + 1)` used in the final
logarithmic ratio bound. -/
private def dynamicHarmonicPrefixSum (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun n ↦ 1 / (n + 1 : ℝ)

/-- Helper for Theorem 8.28: the prefix inverse-square-root sum `∑_{n=0}^k 1 / √(n + 1)` used in
the final denominator estimate. -/
private def dynamicInverseSqrtPrefixSum (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun n ↦ 1 / Real.sqrt (n + 1 : ℝ)

/-- Helper for Theorem 8.28: the localized harmonic prefix sum is bounded by `1 + log (k + 1)`. -/
private lemma dynamicHarmonicPrefixSum_le_one_add_log (k : ℕ) :
    dynamicHarmonicPrefixSum k ≤ 1 + Real.log ((k : ℝ) + 1) := by
  -- Rewrite the localized owner as the standard harmonic number and use mathlib's bound.
  simpa [dynamicHarmonicPrefixSum, harmonic] using harmonic_le_one_add_log (k + 1)

/-- Helper for Theorem 8.28: every term in the localized inverse-square-root sum is at least the
last one, so the whole sum dominates `√(k + 1)`. -/
private lemma sqrt_le_dynamicInverseSqrtPrefixSum (k : ℕ) :
    Real.sqrt ((k : ℝ) + 1) ≤ dynamicInverseSqrtPrefixSum k := by
  have hterm :
      ∀ n ∈ Finset.range (k + 1),
        1 / Real.sqrt ((k : ℝ) + 1) ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
    intro n hn
    have hn_le : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    have hsqrt_le : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
      exact Real.sqrt_le_sqrt hn_le
    exact one_div_le_one_div_of_le (by positivity) hsqrt_le
  have hsum :
      Finset.sum (Finset.range (k + 1)) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 1)) ≤
        dynamicInverseSqrtPrefixSum k := by
    -- Summing the constant lower bound gives the denominator estimate.
    simpa [dynamicInverseSqrtPrefixSum] using Finset.sum_le_sum hterm
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    positivity
  calc
    Real.sqrt ((k : ℝ) + 1)
        = ((k + 1 : ℝ) / Real.sqrt ((k : ℝ) + 1)) := by
            have hsq : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := by
              nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity)]
            apply (eq_div_iff hsqrt_pos.ne').2
            nlinarith
    _ = Finset.sum (Finset.range (k + 1)) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 1)) := by
      simp [div_eq_mul_inv]
    _ ≤ dynamicInverseSqrtPrefixSum k := hsum

/-- Helper for Theorem 8.28: the localized prefix ratio satisfies the same logarithmic bound as
Lemma 8.27(1), but we prove it here directly because the owner file is not currently buildable. -/
private lemma dynamicPrefixRatio_le_log_bound
    (D : ℝ) (hD : 0 ≤ D) (k : ℕ) :
    (D + dynamicHarmonicPrefixSum k) / dynamicInverseSqrtPrefixSum k ≤
      (D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1) := by
  have hnum :
      D + dynamicHarmonicPrefixSum k ≤ D + 1 + Real.log ((k : ℝ) + 1) := by
    linarith [dynamicHarmonicPrefixSum_le_one_add_log k]
  have hnum_nonneg : 0 ≤ D + dynamicHarmonicPrefixSum k := by
    have hprefix_nonneg :
        0 ≤ Finset.sum (Finset.range (k + 1)) (fun x ↦ 1 / (x + 1 : ℝ)) := by
      positivity
    simpa [dynamicHarmonicPrefixSum] using add_nonneg hD hprefix_nonneg
  have hden : Real.sqrt ((k : ℝ) + 1) ≤ dynamicInverseSqrtPrefixSum k :=
    sqrt_le_dynamicInverseSqrtPrefixSum k
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    positivity
  -- Shrink the denominator to the explicit square-root term, then enlarge the numerator.
  exact
    (div_le_div_iff₀ (lt_of_lt_of_le hsqrt_pos hden) hsqrt_pos).2 <|
      by nlinarith

/-- Helper for Theorem 8.28: every dynamic-stepsize prefix sum `T_k = ∑_{n=0}^k t_n` is strictly
positive. -/
private lemma dynamicStepsizePrefixSum_pos
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    (k : ℕ) :
    0 < T_ k := by
  -- The first positive dynamic stepsize already appears in every prefix sum.
  have hmem : 0 ∈ Finset.range (k + 1) := by
    simp
  have hle : t 0 ≤ T_ k := by
    simpa [projected_subgradient_stepsize_prefix_sum] using
      (Finset.single_le_sum
        (fun n _ ↦ le_of_lt <| dynamicStepsize_pos
          (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
          h_subgrad h_stepsize n)
        hmem)
  exact lt_of_lt_of_le
    (dynamicStepsize_pos
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize 0)
    hle

/-- Helper for Theorem 8.28: summing the pointwise dynamic-stepsize norm estimate gives the
prefix harmonic bound for the numerator. -/
private lemma dynamicStepsizeNormSqPrefixSum_le_harmonicPrefixSum
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
      dynamicHarmonicPrefixSum k := by
  -- Summing the pointwise Chapter 8 estimate produces the exact harmonic normal form.
  simpa [dynamicHarmonicPrefixSum] using
    (Finset.sum_le_sum fun n _ ↦
      dynamicStepsize_sq_mul_norm_sq_le_inv
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_stepsize n)

/-- Helper for Theorem 8.28: summing the pointwise dynamic-stepsize lower bound gives the
inverse-square-root denominator estimate. -/
private lemma inverseSqrtPrefixSum_le_Lf_mulStepsizePrefixSum
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    (k : ℕ) :
    dynamicInverseSqrtPrefixSum k ≤ h_bound.L_f * T_ k := by
  have hterm :
      ∀ n ∈ Finset.range (k + 1),
        1 / Real.sqrt ((n : ℝ) + 1) ≤ h_bound.L_f * t n := by
    intro n hn
    have hlower :=
      dynamicStepsize_invSqrt_lower_bound
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_subgrad h_stepsize n
    have hmul := mul_le_mul_of_nonneg_left hlower (le_of_lt h_bound.L_f_pos)
    have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
    calc
      1 / Real.sqrt ((n : ℝ) + 1) =
          h_bound.L_f * (1 / (h_bound.L_f * Real.sqrt ((n : ℝ) + 1))) := by
            field_simp [h_bound.L_f_pos.ne', hsqrt_ne]
      _ ≤ h_bound.L_f * t n := hmul
  -- Summing the pointwise comparison yields the denominator bridge to Lemma 8.27.
  calc
    dynamicInverseSqrtPrefixSum k =
        Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) := by
          simp [dynamicInverseSqrtPrefixSum]
    _ ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ h_bound.L_f * t n) := by
          exact Finset.sum_le_sum hterm
    _ = h_bound.L_f * T_ k := by
          simpa [projected_subgradient_stepsize_prefix_sum] using
            (Finset.mul_sum (Finset.range (k + 1)) (fun n ↦ t n) h_bound.L_f).symm

/-- Helper for Theorem 8.28: after normalizing the numerator and denominator prefix sums, the
weighted objective-gap quotient is controlled by the canonical prefix ratio from Lemma 8.27. -/
private lemma weightedGapQuotient_le_dynamicPrefixRatio
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    {xStar : E} (k : ℕ) :
    (‖x0 - xStar‖ ^ (2 : ℕ) +
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ))) / (T[t](k)) ≤
      h_bound.L_f *
        ((‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) /
          dynamicInverseSqrtPrefixSum k) := by
  have hTk_pos :=
    dynamicStepsizePrefixSum_pos
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize k
  have hInvSqrt_le :=
    inverseSqrtPrefixSum_le_Lf_mulStepsizePrefixSum
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize k
  have hInvSqrt_pos : 0 < dynamicInverseSqrtPrefixSum k := by
    exact lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) (sqrt_le_dynamicInverseSqrtPrefixSum k)
  have hNumerator :
      ‖x0 - xStar‖ ^ (2 : ℕ) +
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
        ‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k := by
    have hsum :=
      dynamicStepsizeNormSqPrefixSum_le_harmonicPrefixSum
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_stepsize k
    linarith
  have hRightNonneg : 0 ≤ ‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k := by
    have hD_nonneg : 0 ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
      positivity
    have hHarm_nonneg : 0 ≤ dynamicHarmonicPrefixSum k := by
      have hsum_nonneg :
          0 ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / (n + 1 : ℝ)) := by
        positivity
      simpa [dynamicHarmonicPrefixSum] using hsum_nonneg
    exact add_nonneg hD_nonneg hHarm_nonneg
  have hFirstStep :
      (‖x0 - xStar‖ ^ (2 : ℕ) +
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ))) / (T[t](k)) ≤
        (‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) / (T[t](k)) := by
    rw [div_le_div_iff_of_pos_right hTk_pos]
    exact hNumerator
  have hSecondStep :
      (‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) / (T[t](k)) ≤
        h_bound.L_f *
          ((‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) /
            dynamicInverseSqrtPrefixSum k) := by
    have hCross :
        (‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) *
            dynamicInverseSqrtPrefixSum k ≤
          (h_bound.L_f * (‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k)) * (T[t](k)) := by
      have hmul := mul_le_mul_of_nonneg_left hInvSqrt_le hRightNonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hDiv :
        (‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) / (T[t](k)) ≤
          (h_bound.L_f * (‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k)) /
            dynamicInverseSqrtPrefixSum k := by
      rw [div_le_div_iff₀ hTk_pos hInvSqrt_pos]
      exact hCross
    simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hDiv
  exact hFirstStep.trans hSecondStep

-- Proof sketch: combine the weighted objective-gap estimate from Lemma 8.24 with the prefix-min
-- characterization of `best_achieved_function_value` and with Jensen's inequality for the convex
-- restriction of `f` on `C` to control the weighted average iterate. The dynamic stepsize rule
-- gives `t_n^2 ‖g_n‖^2 ≤ 1 / (n + 1)` and `t_n ≥ 1 / (L_f √(n + 1))`; substituting these bounds
-- and then applying Lemma 8.27 (1) with `D = ‖x^0 - xStar‖^2` yields the displayed
-- `O(log(k) / √k)` estimate.
/-- Theorem 8.28: under Assumptions 8.7 and 8.12, if the projected subgradient method uses the
dynamic stepsizes
`t_k = 1 / (‖f'(x^k)‖ √(k + 1))` when the chosen subgradient `f'(x^k)` is nonzero and
`t_k = 1 / L_f` otherwise, then for every `k ≥ 1` the larger of the best-value gap
`f_best^k - fOpt` and the averaged-iterate gap `f(x^(k)) - fOpt` is bounded by
`(L_f / 2) (‖x^0 - xStar‖^2 + 1 + log(k + 1)) / √(k + 1)`. -/
theorem projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    max
        (best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt)
        ((f (x^(k))).toReal - fOpt) ≤
      (h_bound.L_f / 2) *
        (‖x0 - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := by
  -- Route correction: instead of reproving the logarithmic ratio bound locally, normalize both
  -- branches to the single weighted-gap quotient and then invoke Lemma 8.27.
  let weightedNormSum : ℝ :=
    Finset.sum (Finset.range (k + 1))
      (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ))
  let bestGap : ℝ :=
    best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt
  have hTk_pos :=
    dynamicStepsizePrefixSum_pos
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize k
  have hStepsize_nonneg : ∀ n, 0 ≤ t n := by
    intro n
    exact le_of_lt <| dynamicStepsize_pos
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize n
  have hWeightedGap :
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) ≤
        (1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum := by
    -- Lemma 8.24 gives the common weighted objective-gap estimate for both branches.
    simpa [weightedNormSum] using
      projected_subgradient_method_weighted_objective_gap_sum_le
        (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
        (g := g) (t := t) (x0 := x0) h_subgrad hStepsize_nonneg hxStar k
  have hBestGapLeWeighted :
      bestGap ≤
        ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) / (T[t](k)) := by
    have hBestSum :
        (T[t](k)) * bestGap ≤
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
      -- Compare the running best gap with each weighted summand and sum the inequalities.
      calc
        (T[t](k)) * bestGap =
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * bestGap) := by
              calc
                (T[t](k)) * bestGap =
                    (Finset.sum (Finset.range (k + 1)) fun n ↦ t n) * bestGap := by
                      simp [projected_subgradient_stepsize_prefix_sum]
                _ = Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * bestGap) := by
                      exact Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ t n) bestGap
        _ ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
              refine Finset.sum_le_sum ?_
              intro n hn
              have hbest_le :
                  best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k ≤ (f x̄[n]).toReal :=
                best_achieved_function_value_le_objective_value
                  (fun x : E ↦ (f x).toReal) x̄ k n hn
              exact mul_le_mul_of_nonneg_left
                (sub_le_sub_right hbest_le fOpt)
                (hStepsize_nonneg n)
    -- Divide by the positive prefix sum to isolate the best achieved value gap.
    rw [le_div_iff₀ hTk_pos]
    simpa [mul_comm] using hBestSum.trans hWeightedGap
  have hBestCommon :
      best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt ≤
        (1 / 2 : ℝ) *
          ((‖x0 - xStar‖ ^ (2 : ℕ) + weightedNormSum) / (T[t](k))) := by
    calc
      best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt = bestGap := by
        rfl
      _ ≤
          ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) / (T[t](k)) :=
          hBestGapLeWeighted
      _ = (1 / 2 : ℝ) * ((‖x0 - xStar‖ ^ (2 : ℕ) + weightedNormSum) / (T[t](k))) := by
          field_simp [hTk_pos.ne']
  have hConvToReal : ConvexOn ℝ (effective_domain f) (fun y : E ↦ (f y).toReal) :=
    convexOn_toReal_of_is_convex_function h_problem.convex (fun z _ ↦ h_problem.ne_bot z)
  have hMemDomain : ∀ n ∈ Finset.range (k + 1), x̄[n] ∈ effective_domain f := by
    intro n hn
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[n]).property)
  have hJensenCenter :
      (f (x^(k))).toReal ≤
        (Finset.range (k + 1)).centerMass (fun n ↦ t n) (fun n ↦ (f x̄[n]).toReal) := by
    -- Jensen applies to the effective-domain center of mass of the iterates.
    rw [projected_subgradient_stepsize_average_iterate_eq_centerMass
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) k]
    simpa [Function.comp] using
      hConvToReal.map_centerMass_le
        (t := Finset.range (k + 1)) (w := fun n ↦ t n) (p := fun n ↦ x̄[n])
        (fun n _ ↦ hStepsize_nonneg n) hTk_pos hMemDomain
  have hJensen :
      (f (x^(k))).toReal ≤
        (T[t](k))⁻¹ *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) := by
    -- Expand the center-of-mass output to the normalized weighted sum.
    calc
      (f (x^(k))).toReal ≤
          (Finset.range (k + 1)).centerMass (fun n ↦ t n) (fun n ↦ (f x̄[n]).toReal) :=
          hJensenCenter
      _ =
          (T[t](k))⁻¹ *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) := by
              simp [Finset.centerMass, projected_subgradient_stepsize_prefix_sum, smul_eq_mul]
  have hWeightedGapAsAverage :
      (f (x^(k))).toReal - fOpt ≤
        ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) / (T[t](k)) := by
    have hSumConst :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt) = (T[t](k)) * fOpt := by
      calc
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt) =
            (Finset.sum (Finset.range (k + 1)) fun n ↦ t n) * fOpt := by
              exact (Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ t n) fOpt).symm
        _ = (T[t](k)) * fOpt := by
              simp [projected_subgradient_stepsize_prefix_sum]
    have hConstantAverage :
        (T[t](k))⁻¹ * Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt) = fOpt := by
      calc
        (T[t](k))⁻¹ * Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt) =
            (T[t](k))⁻¹ * ((T[t](k)) * fOpt) := by
              rw [hSumConst]
        _ = fOpt := by
              field_simp [hTk_pos.ne']
    have hSumSub :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) -
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt) =
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro n hn
      ring
    have hGapRewrite :
        (T[t](k))⁻¹ * Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) - fOpt =
          (T[t](k))⁻¹ *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
      -- Push the constant `fOpt` through the normalized weighted sum.
      calc
        (T[t](k))⁻¹ * Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) - fOpt =
            (T[t](k))⁻¹ * Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) -
              ((T[t](k))⁻¹ * Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt)) := by
                rw [hConstantAverage]
        _ = (T[t](k))⁻¹ *
              (Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) -
                Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * fOpt)) := by
                  ring
        _ = (T[t](k))⁻¹ *
              Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
                  rw [hSumSub]
    have hScaledWeighted :
        (T[t](k))⁻¹ *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) ≤
          (T[t](k))⁻¹ *
            ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) := by
      exact mul_le_mul_of_nonneg_left hWeightedGap (by positivity)
    -- Rewrite Jensen's right-hand side into the same weighted-gap quotient as the best branch.
    calc
      (f (x^(k))).toReal - fOpt ≤
          (T[t](k))⁻¹ *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * (f x̄[n]).toReal) - fOpt := by
              linarith
      _ =
          (T[t](k))⁻¹ *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
              exact hGapRewrite
      _ ≤
          (T[t](k))⁻¹ *
            ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) :=
          hScaledWeighted
      _ =
          ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) / (T[t](k)) := by
              rw [div_eq_mul_inv]
              ring
  have hAverageCommon :
      (f (x^(k))).toReal - fOpt ≤
        (1 / 2 : ℝ) * ((‖x0 - xStar‖ ^ (2 : ℕ) + weightedNormSum) / (T[t](k))) := by
    calc
      (f (x^(k))).toReal - fOpt ≤
          ((1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * weightedNormSum) / (T[t](k)) :=
          hWeightedGapAsAverage
      _ = (1 / 2 : ℝ) * ((‖x0 - xStar‖ ^ (2 : ℕ) + weightedNormSum) / (T[t](k))) := by
          field_simp [hTk_pos.ne']
  have hD_nonneg : 0 ≤ ‖x0 - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hCommonQuotient :
      (1 / 2 : ℝ) * ((‖x0 - xStar‖ ^ (2 : ℕ) + weightedNormSum) / (T[t](k))) ≤
        (h_bound.L_f / 2) *
          (‖x0 - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
            Real.sqrt ((k : ℝ) + 1) := by
    have hRatioBound :=
      weightedGapQuotient_le_dynamicPrefixRatio
        (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
        h_subgrad h_stepsize (xStar := xStar) k
    have hLogBound :=
      dynamicPrefixRatio_le_log_bound
        (‖x0 - xStar‖ ^ (2 : ℕ)) hD_nonneg k
    have hLfHalf_nonneg : 0 ≤ h_bound.L_f / 2 := by
      nlinarith [h_bound.L_f_pos]
    -- Lemma 8.27 closes the normalized quotient exactly in the textbook form.
    calc
      (1 / 2 : ℝ) * ((‖x0 - xStar‖ ^ (2 : ℕ) + weightedNormSum) / (T[t](k))) ≤
          (1 / 2 : ℝ) *
            (h_bound.L_f *
              ((‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) /
                dynamicInverseSqrtPrefixSum k)) := by
                exact mul_le_mul_of_nonneg_left hRatioBound (by norm_num)
      _ = (h_bound.L_f / 2) *
            ((‖x0 - xStar‖ ^ (2 : ℕ) + dynamicHarmonicPrefixSum k) /
              dynamicInverseSqrtPrefixSum k) := by
              ring
      _ ≤ (h_bound.L_f / 2) *
            ((‖x0 - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
              Real.sqrt ((k : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hLogBound hLfHalf_nonneg
      _ = (h_bound.L_f / 2) *
            (‖x0 - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
              Real.sqrt ((k : ℝ) + 1) := by
              ring
  -- Both branches now factor through the same normalized quotient bound.
  exact (max_le_iff.mpr
    ⟨hBestCommon.trans hCommonQuotient, hAverageCommon.trans hCommonQuotient⟩)

-- Proof sketch: apply the combined max estimate from
-- `projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize` and use
-- `le_max_left` to extract the first component.
/-- The best objective value attained by the first `k + 1` projected-subgradient iterates satisfies
the `O(log(k) / √k)` bound from the dynamic stepsize theorem. -/
theorem projected_subgradient_best_value_gap_le_of_dynamic_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    best_achieved_function_value (fun x : E ↦ (f x).toReal) x̄ k - fOpt ≤
      (h_bound.L_f / 2) *
        (‖x0 - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := by
  -- Project the first component from the combined max estimate.
  exact le_trans
    (le_max_left _ _)
    (projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize hxStar hk)

-- Proof sketch: apply the combined max estimate from
-- `projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize` and use
-- `le_max_right` to extract the averaged-iterate component.
/-- The stepsize-weighted average iterate `x^(k)` satisfies the same `O(log(k) / √k)` objective-gap
bound as the best achieved value in the dynamic stepsize regime. -/
theorem projected_subgradient_average_value_gap_le_of_dynamic_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize :
      ∀ n, t n = projectedSubgradientDynamicStepsize h_bound.L_f n (g n (x[n])))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 1 ≤ k) :
    (f (x^(k))).toReal - fOpt ≤
      (h_bound.L_f / 2) *
        (‖x0 - xStar‖ ^ (2 : ℕ) + 1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := by
  -- Project the second component from the combined max estimate.
  exact le_trans
    (le_max_right _ _)
    (projected_subgradient_best_and_average_value_gap_le_of_dynamic_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      h_subgrad h_stepsize hxStar hk)

end
