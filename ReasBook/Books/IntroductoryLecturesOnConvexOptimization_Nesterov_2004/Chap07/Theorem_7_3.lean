/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {X : Type u}

/- Theorem 7.3 lies in the autonomous discrete-trajectory / first-stopping-time domain.

Sampled owner-style declarations:
- `relativeScaleSubgradientApproximationIterate`,
  `relativeScaleSubgradientApproximationStoppingIndex`, and
  `relativeScaleSubgradientApproximationStoppingTime` in `Algorithm_7_2.lean`;
- `ConstrainedLevelMethod.stoppingIndex` in `Chap03/Algorithm_3_11.lean`;
- `gradientMethod` in `Chap01/Algorithm_1_6_1.lean`;
- `NewtonSystem.orbit` in `Chap01/Algorithm_1_7_1.lean`.

Best owner abstraction:
- source-facing: Theorem 7.3's stopping-time, terminal-value, and work bounds for Algorithm 7.2;
- core/canonical: the Algorithm 7.2 iterate owner
  `relativeScaleSubgradientApproximationIterate G f x0 δ α γ0` together with the canonical
  stopping index/time derived from `hTerminate`;
- bridge/view: the derived lower-level work count
  `relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate`.

Primitive data:
- the update-scheme data `G`, `f`, `x0`, `δ`, `α`, and `γ0`;
- the existence witness `hTerminate` for the stopping criterion;
- the actual optimality data and Chapter 7 parameter relations;
- the lower-level stage guarantee attached to the fixed block length.

Derived API:
- the canonical stage sequence `\hat x_t`;
- the first stopping index `s` and stopping time `T = s + 1`;
- the total lower-level work up to `T`;
- the three bounds asserted by Theorem 7.3.

Source/core/bridge triage:
- source-facing: the three theorem conclusions;
- core/canonical: the Algorithm 7.2 iterate and stopping-time owners;
- bridge/view: the work-count formula `T * \hat N`.

The stopping data already has a canonical owner in `Algorithm_7_2.lean`, so this file states the
Theorem 7.3 conclusions directly on that owner instead of introducing a separate public result
wrapper.
-/

-- Semantic recall via `lean_leansearch` did not reveal a reusable mathlib owner here; the local
-- Chapter 7 iterate/stopping-time API remains the correct public surface for this item.

/-- The total number of lower-level gradient steps used by the relative-scale subgradient
approximation trajectory up to its stopping time, assuming that each stage uses
`relativeScaleSubgradientApproximationBlockLength δ α` lower-level steps. -/
def relativeScaleSubgradientApproximationTotalLowerLevelSteps
    {f : X → ℝ} {G : ℕ → ℝ → X} {x0 : X} {δ α γ0 : ℝ}
    (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0) : ℕ :=
  relativeScaleSubgradientApproximationStoppingTime hTerminate *
    relativeScaleSubgradientApproximationBlockLength δ α

-- Proof sketch: unfold `relativeScaleSubgradientApproximationTotalLowerLevelSteps`.
/-- Expanding `relativeScaleSubgradientApproximationTotalLowerLevelSteps` gives the product of the
stopping time and the per-stage lower-level step count. -/
theorem relativeScaleSubgradientApproximationTotalLowerLevelSteps_def
    {f : X → ℝ} {G : ℕ → ℝ → X} {x0 : X} {δ α γ0 : ℝ}
    (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0) :
    relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate =
      relativeScaleSubgradientApproximationStoppingTime hTerminate *
        relativeScaleSubgradientApproximationBlockLength δ α :=
  rfl

section TerminationBounds

variable [NormedAddCommGroup X]
variable {f : X → ℝ} {G : ℕ → ℝ → X} {x0 xStar : X} {δ α γ0 γ1 : ℝ}

local notation "x̂" => relativeScaleSubgradientApproximationIterate G f x0 δ α γ0

variable
  (hTerminate : relativeScaleSubgradientApproximationTerminates G f x0 δ α γ0)

local notation "s" => relativeScaleSubgradientApproximationStoppingIndex hTerminate
local notation "T" => relativeScaleSubgradientApproximationStoppingTime hTerminate

/-- Helper for Theorem 7.3: the Algorithm 7.2 stopping factor `1 / √e` is exactly
`exp (-(1 : ℝ) / 2)`. -/
lemma relativeScaleSubgradientApproximationStoppingFactor_eq_exp_neg_half :
    relativeScaleSubgradientApproximationStoppingFactor = Real.exp (-(1 : ℝ) / 2) := by
  -- Rewrite the square-root form through `exp (1 / 2)` and then invert the exponential.
  rw [relativeScaleSubgradientApproximationStoppingFactor_def, ← Real.exp_half (1 : ℝ)]
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

/-- Helper for Theorem 7.3: before the first accepted stage, each failed stopping test multiplies
the objective by at most `exp (-(1 : ℝ) / 2)`, so the value at stage `t` is bounded by
`exp (-(t : ℝ) / 2) * f x0`. -/
lemma relativeScaleSubgradientApproximation_value_le_exp_neg_half_until_stoppingIndex :
    ∀ ⦃t : ℕ⦄, t ≤ s → f (x̂ t) ≤ Real.exp (-(t : ℝ) / 2) * f x0 := by
  have _ := (inferInstance : NormedAddCommGroup X)
  intro t ht
  induction t with
  | zero =>
      -- The geometric envelope is exact at the initial iterate.
      simp
  | succ t ih =>
      -- Each preterminal stage fails the stopping test, so one more factor `exp (-1 / 2)` is
      -- gained before the accepted stage.
      have ht_lt : t < s := Nat.lt_of_succ_le ht
      have hfail :
          f (x̂ (t + 1)) <
            relativeScaleSubgradientApproximationStoppingFactor * f (x̂ t) :=
        relativeScaleSubgradientApproximationStoppingIndex_min hTerminate ht_lt
      have hprev :
          f (x̂ t) ≤ Real.exp (-(t : ℝ) / 2) * f x0 :=
        ih (Nat.le_of_lt ht_lt)
      have hfactor_nonneg : 0 ≤ relativeScaleSubgradientApproximationStoppingFactor := by
        rw [relativeScaleSubgradientApproximationStoppingFactor_eq_exp_neg_half]
        positivity
      have hstep :
          f (x̂ (t + 1)) ≤
            relativeScaleSubgradientApproximationStoppingFactor *
              (Real.exp (-(t : ℝ) / 2) * f x0) := by
        exact (le_of_lt hfail).trans (mul_le_mul_of_nonneg_left hprev hfactor_nonneg)
      calc
        f (x̂ (t + 1))
            ≤ relativeScaleSubgradientApproximationStoppingFactor *
                (Real.exp (-(t : ℝ) / 2) * f x0) := hstep
        _ = Real.exp (-((t + 1 : ℕ) : ℝ) / 2) * f x0 := by
              calc
                relativeScaleSubgradientApproximationStoppingFactor *
                    (Real.exp (-(t : ℝ) / 2) * f x0)
                    = (Real.exp (-(1 : ℝ) / 2) * Real.exp (-(t : ℝ) / 2)) * f x0 := by
                        rw [relativeScaleSubgradientApproximationStoppingFactor_eq_exp_neg_half]
                        ring
                _ = Real.exp ((-(1 : ℝ) / 2) + (-(t : ℝ) / 2)) * f x0 := by
                      rw [← Real.exp_add]
                _ = Real.exp (-((t + 1 : ℕ) : ℝ) / 2) * f x0 := by
                      congr 2
                      norm_num [Nat.cast_add]
                      ring_nf

/-- Helper for Theorem 7.3: comparing the preterminal value with the global minimizer and the
initial normalization inequality yields `exp (s / 2) ≤ 1 / α`. -/
lemma relativeScaleSubgradientApproximation_exp_half_stoppingIndex_le_inv_alpha
    (hα : 0 < α)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar) :
    Real.exp ((s : ℝ) / 2) ≤ 1 / α := by
  have _ := (inferInstance : NormedAddCommGroup X)
  -- Compare the preterminal iterate both with the global optimum and with the decay envelope.
  have hs_lower : f xStar ≤ f (x̂ s) :=
    (isMinOn_univ_iff.mp hxStar) (x̂ s)
  have hs_decay :
      f (x̂ s) ≤ Real.exp (-(s : ℝ) / 2) * f x0 :=
    relativeScaleSubgradientApproximation_value_le_exp_neg_half_until_stoppingIndex
      (hTerminate := hTerminate) le_rfl
  have hcomparison :
      α * f x0 ≤ Real.exp (-(s : ℝ) / 2) * f x0 :=
    hOptimalValue_lower.trans (hs_lower.trans hs_decay)
  have halpha_le_exp_neg :
      α ≤ Real.exp (-(s : ℝ) / 2) :=
    le_of_mul_le_mul_right hcomparison hInitialValue_pos
  -- Multiplying by `exp (s / 2)` cancels the decay factor and isolates the stopping index.
  have hexp_mul_le_one :
      Real.exp ((s : ℝ) / 2) * α ≤ 1 := by
    have hmul :
        Real.exp ((s : ℝ) / 2) * α ≤
          Real.exp ((s : ℝ) / 2) * Real.exp (-(s : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left halpha_le_exp_neg (Real.exp_nonneg _)
    calc
      Real.exp ((s : ℝ) / 2) * α ≤
          Real.exp ((s : ℝ) / 2) * Real.exp (-(s : ℝ) / 2) := hmul
      _ = Real.exp (((s : ℝ) / 2) + (-(s : ℝ) / 2)) := by
            rw [← Real.exp_add]
      _ = Real.exp 0 := by
            congr 1
            ring
      _ = 1 := by simp
  exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hexp_mul_le_one)

/-- Helper for Theorem 7.3: the final-stage subgradient bound compresses to
`f (\hat x_T) - f(xStar) ≤ δ * f(xStar)` under the source parameter assumptions. -/
lemma relativeScaleSubgradientApproximation_terminalRatio_le_deltaOverOneAddDelta
    (hParameter_bound : γ1 / γ0 ≤ Real.sqrt (Real.exp 1) / α)
    (hTermination_rule :
      Real.sqrt (Real.exp 1) /
          (α *
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) ≤
        δ / (1 + δ))
    : ((γ1 / γ0) /
          Real.sqrt
            ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) ≤
        δ / (1 + δ) := by
  -- Scale the parameter bound by the terminal inverse square-root factor and invoke the stopping
  -- rule at the same block length.
  have hinv_nonneg :
      0 ≤
        (Real.sqrt
          ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1))⁻¹ := by
    positivity
  have hscaled :
      ((γ1 / γ0) /
          Real.sqrt
            ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) ≤
        (Real.sqrt (Real.exp 1) / α) /
          Real.sqrt
            ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hParameter_bound hinv_nonneg
  exact hscaled.trans (by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hTermination_rule)

/-- Helper for Theorem 7.3: when the final-stage coefficient is nonnegative, scaling the
a-priori-radius bound turns the terminal distance into the normalized optimal-value factor. -/
lemma relativeScaleSubgradientApproximation_scaledDistance_le
    (hcoeff_nonneg :
      0 ≤
        γ1 /
          Real.sqrt
            ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1))
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar) :
    (γ1 /
        Real.sqrt
          ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
        ‖x0 - xStar‖ ≤
      (((γ1 / γ0) /
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
          f xStar) := by
  -- Scale the radius estimate by the nonnegative coefficient and then rewrite the scalar factor.
  have hdistance_scaled :
      (γ1 /
          Real.sqrt
            ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
          ‖x0 - xStar‖ ≤
        (γ1 /
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
          aPrioriRadiusEstimate f γ0 xStar := by
    exact mul_le_mul_of_nonneg_left hOptimal_solution_distance hcoeff_nonneg
  simpa [aPrioriRadiusEstimate_eq_div, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hdistance_scaled

/-- Helper for Theorem 7.3: the final-stage subgradient bound compresses to
`f (\hat x_T) - f(xStar) ≤ δ * f(xStar)` under the source parameter assumptions. -/
lemma relativeScaleSubgradientApproximation_terminalGap_le_deltaMulOptimal
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_bound : γ1 / γ0 ≤ Real.sqrt (Real.exp 1) / α)
    (hFinalStage_gap :
      f (x̂ T) - f xStar ≤
        (γ1 /
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
          ‖x0 - xStar‖)
    (hTermination_rule :
      Real.sqrt (Real.exp 1) /
          (α *
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) ≤
        δ / (1 + δ))
    : f (x̂ T) - f xStar ≤ δ * f xStar := by
  let coeff : ℝ :=
    γ1 /
      Real.sqrt
        ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)
  have hfStar_pos : 0 < f xStar := by
    have hscaled_pos : 0 < α * f x0 := mul_pos hα hInitialValue_pos
    exact lt_of_lt_of_le hscaled_pos hOptimalValue_lower
  have hfStar_nonneg : 0 ≤ f xStar := hfStar_pos.le
  have hratio_bound :
      ((γ1 / γ0) /
          Real.sqrt
            ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) ≤
        δ / (1 + δ) :=
    relativeScaleSubgradientApproximation_terminalRatio_le_deltaOverOneAddDelta
      (δ := δ) (α := α) hParameter_bound hTermination_rule
  have hratio_scaled :
      (((γ1 / γ0) /
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
          f xStar) ≤
        (δ / (1 + δ)) * f xStar := by
    exact mul_le_mul_of_nonneg_right hratio_bound hfStar_nonneg
  have hratio_le_delta : δ / (1 + δ) ≤ δ := by
    have hOne_add_δ : 0 < 1 + δ := by linarith
    refine (div_le_iff₀ hOne_add_δ).2 ?_
    nlinarith [hδ]
  have hdelta_scaled :
      (δ / (1 + δ)) * f xStar ≤ δ * f xStar := by
    exact mul_le_mul_of_nonneg_right hratio_le_delta hfStar_nonneg
  by_cases hcoeff_nonneg : 0 ≤ coeff
  · -- With a nonnegative coefficient, scale the radius bound and then compress the scalar factor.
    have hdistance_scaled :
        coeff * ‖x0 - xStar‖ ≤
          (((γ1 / γ0) /
                Real.sqrt
                  ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
              f xStar) := by
      simpa [coeff] using
        relativeScaleSubgradientApproximation_scaledDistance_le
          (δ := δ) (α := α) (f := f) (γ0 := γ0) (γ1 := γ1) (x0 := x0) (xStar := xStar)
          hcoeff_nonneg hOptimal_solution_distance
    exact hFinalStage_gap.trans (hdistance_scaled.trans (hratio_scaled.trans hdelta_scaled))
  · -- If the terminal coefficient is nonpositive, the final-stage gap is already nonpositive.
    have hcoeff_le_zero : coeff ≤ 0 := le_of_not_ge hcoeff_nonneg
    have hcoeff_mul_nonpos : coeff * ‖x0 - xStar‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoeff_le_zero (norm_nonneg _)
    have hgap_nonpos : f (x̂ T) - f xStar ≤ 0 := hFinalStage_gap.trans hcoeff_mul_nonpos
    have hdelta_nonneg : 0 ≤ δ * f xStar := by positivity
    exact hgap_nonpos.trans hdelta_nonneg

/-- Helper for Theorem 7.3: the canonical block length is bounded above by its unfloored real
expression in the positive-parameter regime. -/
lemma relativeScaleSubgradientApproximationBlockLength_le_unfloored
    (hα : 0 < α)
    (hδ : 0 < δ) :
    (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) ≤
      ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) := by
  have hexpr_nonneg :
      0 ≤ ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) := by
    positivity
  -- `Nat.floor` is always bounded above by the real expression it floors.
  simpa [relativeScaleSubgradientApproximationBlockLength_def] using Nat.floor_le hexpr_nonneg

-- Proof sketch: use `relativeScaleSubgradientApproximationStoppingIndex_min` to show that before
-- the first accepted stage the objective decays by the factor `1 / √e`, then combine the
-- resulting estimate at `T - 1` with the optimality witness `hxStar`, the lower bound
-- `α * f x0 ≤ f xStar`, and the positive initial value `0 < f x0` to obtain
-- `(T : ℝ) ≤ 1 + 2 log (1 / α)`. For the terminal value, apply the
-- source final-stage gap estimate at time `T`, use the distance bound
-- `‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar`, combine it with the source coefficient bound
-- `γ1 / γ0 ≤ √e / α`, and then use the source termination inequality for the explicit final-stage
-- lower-level step count `Nhat`. Finally multiply the per-stage block length by the stopping-time
-- bound to control the total lower-level work.
/-- Theorem 7.3 (1): under the canonical stopping-time setup for Algorithm 7.2, the stopping time
`T` is bounded above by `1 + 2 log (1 / α)` once the initial value `f x0` is positive. -/
theorem relativeScaleSubgradientApproximation_stopping_time_bound
    (hα : 0 < α)
    (hα_le_one : α ≤ 1)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    : (T : ℝ) ≤ 1 + 2 * Real.log (1 / α) := by
  have _ := hα_le_one
  -- The preterminal decay helper isolates the logarithmic scalar bound on the stopping index.
  have hs_le_log :
      (s : ℝ) / 2 ≤ Real.log (1 / α) :=
    (Real.le_log_iff_exp_le (one_div_pos.mpr hα)).2
      (relativeScaleSubgradientApproximation_exp_half_stoppingIndex_le_inv_alpha
        (hTerminate := hTerminate) hα hInitialValue_pos hxStar hOptimalValue_lower)
  -- Rewriting `T = s + 1` finishes the source stopping-time estimate.
  calc
    (T : ℝ) = (s : ℝ) + 1 := by
      simp [relativeScaleSubgradientApproximationStoppingTime]
    _ ≤ 1 + 2 * Real.log (1 / α) := by
      linarith [hs_le_log]

-- Proof sketch: apply the source final-stage gap estimate at time `T`, specialized to the
-- canonical final-stage block length `relativeScaleSubgradientApproximationBlockLength δ α`; use
-- the distance bound `‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar`, combine it with the
-- source parameter bound `γ1 / γ0 ≤ √e / α`, use `0 < f x0` together with
-- `α * f x0 ≤ f xStar` to obtain `0 < f xStar`, and then compare the resulting terminal estimate
-- with `f xStar` using the source termination inequality for that same fixed block length.
/-- Theorem 7.3 (2): under the canonical stopping-time setup for Algorithm 7.2, the terminal value
`f(\hat x_T)` satisfies the source bound `f(\hat x_T) ≤ (1 + δ) f(xStar)` in the
positive-initial-value regime `0 < f x0`. -/
theorem relativeScaleSubgradientApproximation_terminal_relative_accuracy
    (hα : 0 < α)
    (hα_le_one : α ≤ 1)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    (hOptimal_solution_distance : ‖x0 - xStar‖ ≤ aPrioriRadiusEstimate f γ0 xStar)
    (hParameter_bound : γ1 / γ0 ≤ Real.sqrt (Real.exp 1) / α)
    (hFinalStage_gap :
      f (x̂ T) - f xStar ≤
        (γ1 /
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) *
          ‖x0 - xStar‖)
    (hTermination_rule :
      Real.sqrt (Real.exp 1) /
          (α *
            Real.sqrt
              ((relativeScaleSubgradientApproximationBlockLength δ α : ℝ) + 1)) ≤
        δ / (1 + δ))
    : f (x̂ T) ≤ (1 + δ) * f xStar := by
  have _ := hα_le_one
  have _ := hxStar
  -- First compress the final-stage estimate to a direct `δ * f(xStar)` gap bound.
  have hgap :
      f (x̂ T) - f xStar ≤ δ * f xStar :=
    relativeScaleSubgradientApproximation_terminalGap_le_deltaMulOptimal
      (hTerminate := hTerminate) hα hδ hInitialValue_pos hOptimalValue_lower
      hOptimal_solution_distance hParameter_bound hFinalStage_gap hTermination_rule
  have hvalue : f (x̂ T) ≤ δ * f xStar + f xStar :=
    sub_le_iff_le_add.mp hgap
  -- Rearranging the gap bound matches the source `(1 + δ) f(xStar)` conclusion.
  calc
    f (x̂ T) ≤ δ * f xStar + f xStar := hvalue
    _ = (1 + δ) * f xStar := by ring

-- Proof sketch: combine the stopping-time bound from Theorem 7.3 (1), which uses `0 < f x0`,
-- with the explicit formula for `relativeScaleSubgradientApproximationTotalLowerLevelSteps`,
-- using that each stage performs
-- `relativeScaleSubgradientApproximationBlockLength δ α` lower-level steps.
/-- Theorem 7.3 (3): under the canonical stopping-time setup for Algorithm 7.2, the total number
of lower-level gradient steps up to time `T` is bounded by
`(e / α²) (1 + 1 / δ)² (1 + 2 log (1 / α))`, again in the positive-initial-value regime
`0 < f x0`. -/
theorem relativeScaleSubgradientApproximation_total_lower_level_steps_bound
    (hα : 0 < α)
    (hα_le_one : α ≤ 1)
    (hδ : 0 < δ)
    (hInitialValue_pos : 0 < f x0)
    (hxStar : IsMinOn f Set.univ xStar)
    (hOptimalValue_lower : α * f x0 ≤ f xStar)
    :
    (relativeScaleSubgradientApproximationTotalLowerLevelSteps hTerminate : ℝ) ≤
      ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) *
        (1 + 2 * Real.log (1 / α)) := by
  have htime :
      (T : ℝ) ≤ 1 + 2 * Real.log (1 / α) :=
    relativeScaleSubgradientApproximation_stopping_time_bound
      (hTerminate := hTerminate) hα hα_le_one hInitialValue_pos hxStar hOptimalValue_lower
  have hblock :
      (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) ≤
        ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) :=
    relativeScaleSubgradientApproximationBlockLength_le_unfloored hα hδ
  have htime_nonneg : 0 ≤ 1 + 2 * Real.log (1 / α) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    linarith [htime, hT_nonneg]
  -- Bound the stopping-time and block-length factors separately, then combine them through the
  -- product formula for the total lower-level work.
  rw [relativeScaleSubgradientApproximationTotalLowerLevelSteps_def, Nat.cast_mul]
  have htime_mul :
      (T : ℝ) * (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) ≤
        (1 + 2 * Real.log (1 / α)) *
          (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) := by
    exact mul_le_mul_of_nonneg_right htime (by positivity)
  have hblock_mul :
      (1 + 2 * Real.log (1 / α)) *
          (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) ≤
        (1 + 2 * Real.log (1 / α)) *
          (((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hblock htime_nonneg
  calc
    (T : ℝ) * (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) ≤
        (1 + 2 * Real.log (1 / α)) *
          (relativeScaleSubgradientApproximationBlockLength δ α : ℝ) := htime_mul
    _ ≤ (1 + 2 * Real.log (1 / α)) *
          (((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ)) := hblock_mul
    _ = ((Real.exp 1) / (α ^ (2 : ℕ))) * (1 + 1 / δ) ^ (2 : ℕ) *
          (1 + 2 * Real.log (1 / α)) := by
            ring

end TerminationBounds

end
