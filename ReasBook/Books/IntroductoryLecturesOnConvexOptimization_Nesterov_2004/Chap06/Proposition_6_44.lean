/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_32
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_53
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_59
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_14

noncomputable section

open scoped BigOperators WeightSequenceNotation TotalVariationNotation

universe u

namespace ConditionalGradientContraction

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 6.44 lies in the Chapter 6 conditional-gradient / total-variation / sampled-prefix
domain.

Sampled owner declarations:
- `bestFunctionValueUpTo` in `Chap03/Theorem_3_2_10`, the chapter owner for sampled prefix minima;
- `accumulatedWeights` with notation `A[a](t)` and `weightCoefficient` with notation `τ[a](t)`
  in `Definition_6_53`, the Chapter 6 owners for the accumulated weights and normalized
  coefficients;
- `ContractedFeasibleSetTrustRegionScheme` in `Algorithm_6_5`, the source-facing owner for the
  Chapter 6 conditional-gradient iterates `x_t`;
- `linearModelTotalVariationReal` in `Definition_6_59`, the canonical real-valued bridge for the
  Chapter 6 total variation `δ(x_t)`.

Best owner abstraction:
- source-facing: Proposition 6.44's bound on the sampled minimum total variation
  `δ_T^* = min_{0 ≤ t ≤ T} δ(x_t)` for the Chapter 6 method with the standard coefficients;
- core/canonical: `bestFunctionValueUpTo` together with the Chapter 6 owners
  `A[a](t)`, `τ[a](t)`, and `linearModelTotalVariationReal`;
- bridge/view: the internal weighted-prefix arithmetic lemma below.

Primitive data:
- the Chapter 6 standard weight sequence `a_t = t`;
- its derived owners `A_t = A[standardWeight](t)` and `τ_t = τ[standardWeight](t)`;
- the conditional-gradient iterate owner `method`;
- the weighted total-variation estimate along `method`.

Derived API:
- the closed forms for `A[standardWeight](t)` and `τ[standardWeight](t)`;
- the sampled minimum
  `bestFunctionValueUpTo
    (fun t ↦ linearModelTotalVariationReal ... ⟨method t, method.iterates_mem_feasibleSet t⟩) T`;
- Proposition 6.44's rate bound on that sampled minimum.

Source/core/bridge triage:
- source-facing: the standard-weight specialization of the Chapter 6 total-variation estimate;
- core/canonical: `bestFunctionValueUpTo`, `A[a](t)`, `τ[a](t)`,
  `ContractedFeasibleSetTrustRegionScheme`, and `linearModelTotalVariationReal`;
- bridge/view: the weighted-prefix estimate used internally to pass from the weighted bound to the
  sampled-prefix minimum.

The previous file kept only a free-floating arithmetic implication over arbitrary `x` and `δ`.
This refinement restores the actual Chapter 6 owners on the theorem surface: the standard weight
sequence, its accumulated weights and coefficients, the conditional-gradient iterate owner, and
the total-variation bridge consumed by later Chapter 6 estimates. The weighted-prefix estimate is
now kept as a chapter-facing companion theorem derived from those owners, while the sampled-
minimum statement remains the source-facing Proposition 6.44 surface.
-/

/-- The standard Chapter 6 coefficient sequence `a_t = t`. -/
def standardWeight : ℕ → ℝ :=
  fun t ↦ t

/-- Evaluating the standard Chapter 6 weights gives `a_t = t`. -/
@[simp] theorem standardWeight_apply (t : ℕ) :
    standardWeight t = t :=
  rfl

/-- For the standard Chapter 6 weights `a_t = t`, the accumulated weights satisfy
`A_t = A[standardWeight](t) = t (t + 1) / 2`. -/
theorem accumulatedWeights_standardWeight (t : ℕ) :
    A[standardWeight](t) = (t : ℝ) * (t + 1) / 2 := by
  rw [accumulatedWeights_apply]
  have hnat :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ k) * 2 = t * (t + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Finset.sum_range_id_mul_two (t + 1)
  have hreal :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ (k : ℝ)) * 2 = (t : ℝ) * (t + 1) := by
    exact (by
      simpa [Nat.cast_sum, Nat.cast_mul] using
        congrArg (fun n : ℕ ↦ (n : ℝ)) hnat)
  have hsum :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ (k : ℝ)) = (t : ℝ) * (t + 1) / 2 := by
    nlinarith
  simpa [standardWeight] using hsum

/-- For the standard Chapter 6 weights `a_t = t`, the normalized coefficients satisfy
`τ_t = τ[standardWeight](t) = 2 / (t + 2)`. -/
theorem weightCoefficient_standardWeight (t : ℕ) :
    τ[standardWeight](t) = 2 / ((t + 2 : ℕ) : ℝ) := by
  rw [weightCoefficient_apply, standardWeight_apply, accumulatedWeights_standardWeight (t + 1)]
  have ht1 : ((t + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have ht2 : ((t + 2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  field_simp [ht1, ht2]
  rw [Nat.cast_add, Nat.cast_add]
  ring

private theorem bestFunctionValueUpTo_le_of_standardWeight_bound
    (values : ℕ → ℝ) {T : ℕ} {B : ℝ}
    (hweighted :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) ≤
        B * A[standardWeight]((T + 1)) / ((T + 1 : ℕ) : ℝ)) :
    bestFunctionValueUpTo values T ≤ B / ((T + 1 : ℕ) : ℝ) := by
  let vT : ℝ := bestFunctionValueUpTo values T
  have hv_le : ∀ t ∈ Finset.range (T + 1), vT ≤ values t := by
    intro t ht
    exact bestFunctionValueUpTo_le ⟨t, Finset.mem_range.mp ht⟩
  have hsum_lower :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * vT) ≤
        Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) := by
    refine Finset.sum_le_sum fun t ht ↦ ?_
    rw [standardWeight_apply]
    exact mul_le_mul_of_nonneg_left (hv_le t ht) (by positivity)
  have hsum_id :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ)) = (T : ℝ) * (T + 1) / 2 := by
    have hnat :
        Finset.sum (Finset.range (T + 1)) (fun t ↦ t) * 2 = T * (T + 1) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Finset.sum_range_id_mul_two (T + 1)
    have hreal :
        Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ)) * 2 = (T : ℝ) * (T + 1) := by
      exact (by
        simpa [Nat.cast_sum, Nat.cast_mul] using
          congrArg (fun n : ℕ ↦ (n : ℝ)) hnat)
    nlinarith
  have hsum_weights :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1)) =
        accumulatedWeights standardWeight (T + 1) := by
    calc
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1)) =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ) + 1) := by
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            rw [standardWeight_apply]
            norm_num
      _ =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ)) +
            Finset.sum (Finset.range (T + 1)) (fun _ ↦ (1 : ℝ)) := by
              simp [Finset.sum_add_distrib]
      _ = ((T : ℝ) * (T + 1)) / 2 + ((T + 1 : ℕ) : ℝ) := by
            rw [hsum_id]
            simp
      _ = accumulatedWeights standardWeight (T + 1) := by
            rw [accumulatedWeights_standardWeight]
            norm_num [Nat.cast_add]
            ring
  have hprefix :
      vT * accumulatedWeights standardWeight (T + 1) ≤
        Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) := by
    calc
      vT * accumulatedWeights standardWeight (T + 1) =
          vT * Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1)) := by
            rw [hsum_weights]
      _ =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ vT * standardWeight (t + 1)) := by
            rw [Finset.mul_sum]
      _ =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * vT) := by
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            ring
      _ ≤ Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) :=
            hsum_lower
  have hmain :
      accumulatedWeights standardWeight (T + 1) * vT ≤
        accumulatedWeights standardWeight (T + 1) * (B / ((T + 1 : ℕ) : ℝ)) := by
    have :
        vT * accumulatedWeights standardWeight (T + 1) ≤
          B * accumulatedWeights standardWeight (T + 1) / ((T + 1 : ℕ) : ℝ) :=
      hprefix.trans hweighted
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hA_pos : 0 < accumulatedWeights standardWeight (T + 1) := by
    rw [accumulatedWeights_standardWeight]
    positivity
  nlinarith

/-- Helper for Proposition 6.44: `compositeObjectiveValue method t` is the Chapter 6 composite
objective `f(x_t) + Ψ(x_t)` along the method iterates. -/
private def compositeObjectiveValue
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (t : ℕ) : ℝ :=
  problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)

/-- Helper for Proposition 6.44: `standardWeightErrorValue G₁ D t` is the explicit `ν = 1`
Hölder remainder `2 G₁ D² / (t + 2)²` appearing in the standard-weight one-step estimate. -/
private def standardWeightErrorValue
    (G₁ : NNReal) (D : ℝ) (t : ℕ) : ℝ :=
  (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))

-- Proof sketch: combine the Chapter 6 objective-drop owner from `Theorem_6_14` with the
-- standard-weight specialization `τ_t = τ[standardWeight](t) = 2 / (t + 2)`, rewrite the
-- resulting chosen-dual gap in terms of the canonical total-variation bridge
-- `linearModelTotalVariationReal`, and sum the per-step estimate to obtain the displayed weighted
-- prefix bound.
/-- Helper for Proposition 6.44: the iterate-level bridge identifying Algorithm 6.5's
`fderivWithin`-based chosen-dual gap with the canonical Chapter 6 total-variation owner at the
same iterate once the stored dual field agrees with the ambient gradient dual. -/
private theorem iterate_linearizedCompositeGap_eq_totalVariation
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (t : ℕ)
    (hgradient :
      method.gradient (method t) =
        InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates t))) :
    linearizedCompositeGap problem.feasibleSet
        (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
        (method.iterates t) =
      linearModelTotalVariation
        problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
        (method.iterates t) := by
  -- Route correction: the source-faithful proof needs this adapter before any summation.
  -- Once the dual field is identified with the ambient gradient, the bridge is exactly
  -- `linearModelTotalVariation_eq_linearizedCompositeGap`.
  simpa [hgradient] using
    (linearModelTotalVariation_eq_linearizedCompositeGap
      problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
      (method.iterates t)).symm

/-- Helper for Proposition 6.44: the Chapter 6 total variation is nonnegative because the base
point itself is an admissible comparison in the defining supremum. -/
private theorem linearModelTotalVariation_nonneg
    (Q : Set E) (f Ψ : E → ℝ) (x : Q) :
    (0 : EReal) ≤ δ[Q, f, Ψ](x) := by
  -- Choosing the feasible comparison point `y = x` produces the zero gap.
  rw [linearModelTotalVariation_def]
  exact le_sSup ⟨x, x.property, by simp⟩

/-- Helper for Proposition 6.44: under `ν = 1` and the standard weights
`τ_t = 2 / (t + 2)`, the Hölder remainder from Theorem 6.14 reduces to the explicit
term `2 G₁ D² / (t + 2)²`. -/
private theorem standard_weight_holder_error_eq
    (G₁ : NNReal) (D : ℝ) (t : ℕ) :
    (G₁ : ℝ) * Real.rpow D (1 + ((1 : NNReal) : ℝ)) / (1 + ((1 : NNReal) : ℝ)) *
        Real.rpow (τ[standardWeight](t)) (1 + ((1 : NNReal) : ℝ)) =
      (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
  -- Rewrite the standard Chapter 6 coefficient and simplify both quadratic powers.
  rw [weightCoefficient_standardWeight]
  norm_num
  have ht2 : (((t + 2 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp [Real.rpow_natCast, ht2]

/-- Helper for Proposition 6.44: once the chosen dual field agrees with the ambient gradient at
step `t`, Theorem 6.14 gives the real-valued standard-weight one-step recurrence used in the
final summation. -/
private theorem standard_weight_totalVariationReal_drop_le
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ) {T : ℕ}
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤)
    (t : ℕ) (ht : t ≤ T)
    (hgradient :
      method.gradient (method t) =
        InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates t))) :
    (2 / ((t + 2 : ℕ) : ℝ)) *
        linearModelTotalVariationReal
          problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
          ⟨method t, method.iterates_mem_feasibleSet t⟩ ≤
      (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
        (problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1))) +
        (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
  let δt : EReal :=
    δ[problem.feasibleSet, problem.smoothPart,
      withTopRealPart problem.nonsmoothPart](⟨method t, method.iterates_mem_feasibleSet t⟩)
  have hgap :
      linearizedCompositeGap problem.feasibleSet
          (withTopRealPart problem.nonsmoothPart) (method.gradient (method t))
          (method.iterates t) = δt := by
    simpa [δt] using iterate_linearizedCompositeGap_eq_totalVariation method t hgradient
  have hdrop :=
    objective_drop_ge_stepSize_mul_totalVariation_sub_holderError
      method hholder hdiam t hgap
  have hdrop' :
      (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (((2 / ((t + 2 : ℕ) : ℝ) : ℝ) : EReal) * δt) -
          ((standardWeightErrorValue G₁ D t : ℝ) : EReal) := by
    -- Rewrite the step size and the `ν = 1` Hölder remainder onto the proposition's owner
    -- surface before casting back to `ℝ`.
    have herror :
        ((((G₁ : ℝ) * Real.rpow D (1 + ((1 : NNReal) : ℝ)) / (1 + ((1 : NNReal) : ℝ)) *
                Real.rpow (τ[standardWeight](t)) (1 + ((1 : NNReal) : ℝ)) : ℝ) : EReal)) =
          ((standardWeightErrorValue G₁ D t : ℝ) : EReal) := by
      simpa [standardWeightErrorValue] using
        (show
            ((((G₁ : ℝ) * Real.rpow D (1 + ((1 : NNReal) : ℝ)) / (1 + ((1 : NNReal) : ℝ)) *
                    Real.rpow (τ[standardWeight](t)) (1 + ((1 : NNReal) : ℝ)) : ℝ) : EReal)) =
              (((2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) : ℝ) : EReal) from by
          exact_mod_cast standard_weight_holder_error_eq G₁ D t)
    rw [hstep t, herror] at hdrop
    simpa [δt, weightCoefficient_standardWeight] using hdrop
  have hmove :
      (((2 / ((t + 2 : ℕ) : ℝ) : ℝ) : EReal) * δt) ≤
        (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
              (problem.smoothPart (method (t + 1)) +
                withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) +
          ((standardWeightErrorValue G₁ D t : ℝ) : EReal) := by
    have hdrop_le :
        ((((2 / ((t + 2 : ℕ) : ℝ) : ℝ) : EReal) * δt) -
              ((standardWeightErrorValue G₁ D t : ℝ) : EReal)) ≤
          (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
                (problem.smoothPart (method (t + 1)) +
                  withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) := by
      simpa [ge_iff_le] using hdrop'
    rw [EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))] at hdrop_le
    exact hdrop_le
  have hnonneg :
      (0 : EReal) ≤ δt := by
    simpa [δt] using
      linearModelTotalVariation_nonneg
        problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
        ⟨method t, method.iterates_mem_feasibleSet t⟩
  have hbot : δt ≠ ⊥ := by
    intro hbot
    simp [hbot] at hnonneg
  have hcoeff_nonneg : (0 : ℝ) ≤ 2 / ((t + 2 : ℕ) : ℝ) := by positivity
  have hprod_top :
      (((2 / ((t + 2 : ℕ) : ℝ) : ℝ) : EReal) * δt) ≠ ⊤ := by
    refine (EReal.mul_ne_top _ _).2 ?_
    exact ⟨Or.inl (EReal.coe_ne_bot _),
      Or.inl (show (0 : EReal) ≤ (((2 / ((t + 2 : ℕ) : ℝ) : ℝ) : EReal)) by
        exact_mod_cast hcoeff_nonneg),
      Or.inl (EReal.coe_ne_top _), Or.inr (hfinite t ht)⟩
  have hprod_bot :
      (((2 / ((t + 2 : ℕ) : ℝ) : EReal) * δt)) ≠ ⊥ := by
    refine (EReal.mul_ne_bot _ _).2 ?_
    exact ⟨Or.inl (EReal.coe_ne_bot _), Or.inr hbot,
      Or.inl (EReal.coe_ne_top _),
      Or.inl (show (0 : EReal) ≤ (((2 / ((t + 2 : ℕ) : ℝ) : ℝ) : EReal)) by
        exact_mod_cast hcoeff_nonneg)⟩
  -- Finally cast the finite `EReal` step estimate back to the real-valued bridge `δ_real(x_t)`.
  have hreal :
      (2 / ((t + 2 : ℕ) : ℝ)) *
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩ ≤
        (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) +
          standardWeightErrorValue G₁ D t := by
    simpa [δt, linearModelTotalVariationReal_def, EReal.toReal_mul] using
      EReal.toReal_le_toReal hmove hprod_bot (EReal.coe_ne_top _)
  simpa [standardWeightErrorValue] using hreal

/-- Helper for Proposition 6.44: finite sums of adjacent differences telescope on `Finset.Icc`. -/
private theorem sum_Icc_sub_eq
    (u : ℕ → ℝ) {m T : ℕ} (hmT : m ≤ T) :
    Finset.sum (Finset.Icc m T) (fun t ↦ u t - u (t + 1)) = u m - u (T + 1) := by
  -- Induct on the upper endpoint and peel off the last difference at each step.
  induction T with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      simp
  | succ T ih =>
      by_cases hmTs : m ≤ T
      · rw [Finset.sum_Icc_succ_top (Nat.le_trans hmTs (Nat.le_succ T)), ih hmTs]
        ring
      · have hm : m = T + 1 := by omega
        subst hm
        simp

/-- Helper for Proposition 6.44: the composite-objective gap from `x_s` to any later iterate
`x_r` is bounded by the Chapter 6 total variation at `x_s`. -/
private theorem compositeObjectiveGapToFutureIterate_le_totalVariationReal
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) {T s r : ℕ}
    (_hsT : s ≤ T) (_hsr : s ≤ r)
    (hgradient :
      method.gradient (method s) =
        InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates s)))
    (hfinite :
      linearModelTotalVariation
        problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
        (⟨method s, method.iterates_mem_feasibleSet s⟩) ≠ ⊤) :
    (problem.smoothPart (method s) + withTopRealPart problem.nonsmoothPart (method s)) -
        (problem.smoothPart (method r) + withTopRealPart problem.nonsmoothPart (method r)) ≤
      linearModelTotalVariationReal
        problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
        ⟨method s, method.iterates_mem_feasibleSet s⟩ := by
  -- Move the smooth-part gap to the tangent-plane linearization at `x_s`.
  have hgradWithin :
      HasGradientWithinAt
        problem.smoothPart
        (gradient problem.smoothPart (method.iterates s))
        problem.feasibleSet
        (method s) := by
    have hfd :
        HasFDerivWithinAt
          problem.smoothPart
          (InnerProductSpace.toDualMap ℝ E
            (gradient problem.smoothPart (method.iterates s)))
          problem.feasibleSet
          (method s) := by
      simpa [hgradient] using
        method.hasFDerivWithinAt_gradient (x := method s) (method.iterates_mem_feasibleSet s)
    have hgradient_vec :
        (InnerProductSpace.toDual ℝ E).symm
            (InnerProductSpace.toDualMap ℝ E
              (gradient problem.smoothPart (method.iterates s))) =
          gradient problem.smoothPart (method.iterates s) := by
      exact
        (InnerProductSpace.toDual ℝ E).symm_apply_apply
          (gradient problem.smoothPart (method.iterates s))
    convert hfd.hasGradientWithinAt using 1
    exact hgradient_vec.symm
  have hsmooth_convex : ConvexOn ℝ problem.feasibleSet problem.smoothPart :=
    problem.smoothPart_convex
  have htangent :=
    hsmooth_convex.lower_tangent_plane_of_hasGradientWithinAt
      (method s) (method.iterates_mem_feasibleSet s)
      (gradient problem.smoothPart (method.iterates s)) hgradWithin
      (method r) (method.iterates_mem_feasibleSet r)
  have hgap_real :
      (problem.smoothPart (method s) + withTopRealPart problem.nonsmoothPart (method s)) -
          (problem.smoothPart (method r) + withTopRealPart problem.nonsmoothPart (method r)) ≤
        inner ℝ (gradient problem.smoothPart (method.iterates s)) ((method s) - (method r)) +
          withTopRealPart problem.nonsmoothPart (method s) -
          withTopRealPart problem.nonsmoothPart (method r) := by
    have hsub :
        ((method r) : E) - method s = -((method s : E) - method r) := by
      simp [sub_eq_add_neg]
    have hrewrite :
        inner ℝ (gradient problem.smoothPart (method.iterates s)) (((method r : E)) - method s) =
          -inner ℝ (gradient problem.smoothPart (method.iterates s))
            (((method s : E)) - method r) := by
      rw [hsub, inner_neg_right]
    rw [hrewrite] at htangent
    linarith
  have hcomparison :
      (((inner ℝ (gradient problem.smoothPart (method.iterates s)) ((method s) - (method r)) +
            withTopRealPart problem.nonsmoothPart (method s) -
            withTopRealPart problem.nonsmoothPart (method r) : ℝ) : EReal)) ≤
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](
          ⟨method s, method.iterates_mem_feasibleSet s⟩) := by
    -- Spend the future iterate `x_r` as a feasible comparison point in the defining supremum.
    rw [linearModelTotalVariation_def
      problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
      ⟨method s, method.iterates_mem_feasibleSet s⟩]
    exact le_sSup ⟨method r, method.iterates_mem_feasibleSet r, rfl⟩
  have hgap_ereal :
      (((problem.smoothPart (method s) + withTopRealPart problem.nonsmoothPart (method s)) -
            (problem.smoothPart (method r) + withTopRealPart problem.nonsmoothPart (method r)) :
          ℝ) : EReal) ≤
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](
          ⟨method s, method.iterates_mem_feasibleSet s⟩) := by
    have hgap_ereal_aux :
        (((problem.smoothPart (method s) + withTopRealPart problem.nonsmoothPart (method s)) -
              (problem.smoothPart (method r) + withTopRealPart problem.nonsmoothPart (method r)) :
            ℝ) : EReal) ≤
          (((inner ℝ (gradient problem.smoothPart (method.iterates s)) ((method s) - (method r)) +
                withTopRealPart problem.nonsmoothPart (method s) -
                withTopRealPart problem.nonsmoothPart (method r) : ℝ) : EReal)) := by
      exact_mod_cast hgap_real
    exact hgap_ereal_aux.trans hcomparison
  have hnonneg :
      (0 : EReal) ≤
        δ[problem.feasibleSet, problem.smoothPart,
          withTopRealPart problem.nonsmoothPart](⟨method s, method.iterates_mem_feasibleSet s⟩) :=
    linearModelTotalVariation_nonneg
      problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
      ⟨method s, method.iterates_mem_feasibleSet s⟩
  have hbot :
      δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](
        ⟨method s, method.iterates_mem_feasibleSet s⟩) ≠ ⊥ := by
    intro hbot
    simp [hbot] at hnonneg
  -- Now cast the finite `EReal` bound back to the canonical real-valued bridge `δ_real(x_s)`.
  have hreal_cast :
      (((problem.smoothPart (method s) + withTopRealPart problem.nonsmoothPart (method s)) -
            (problem.smoothPart (method r) + withTopRealPart problem.nonsmoothPart (method r)) :
          ℝ) : EReal) ≤
        ((linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method s, method.iterates_mem_feasibleSet s⟩ : ℝ) : EReal) := by
    rw [linearModelTotalVariationReal_def, EReal.coe_toReal hfinite hbot]
    exact hgap_ereal
  exact_mod_cast hreal_cast

/-- Helper for Proposition 6.44: summing the standard-weight one-step estimate on a tail interval
packages the drop into a single telescope plus the explicit square-error tail. -/
private theorem sum_standardWeightStepSize_mul_totalVariationReal_le_tailDropPlusError
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ) {T m : ℕ}
    (hmT : m ≤ T)
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤)
    (hgradient :
      ∀ t : ℕ, t ≤ T →
        method.gradient (method t) =
          InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates t))) :
    Finset.sum (Finset.Icc m T) (fun t ↦
        (2 / ((t + 2 : ℕ) : ℝ)) *
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩) ≤
      (problem.smoothPart (method m) + withTopRealPart problem.nonsmoothPart (method m)) -
        (problem.smoothPart (method (T + 1)) +
          withTopRealPart problem.nonsmoothPart (method (T + 1))) +
        Finset.sum (Finset.Icc m T) (fun t ↦
          (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
  have hpointwise :
      ∀ t ∈ Finset.Icc m T,
        (2 / ((t + 2 : ℕ) : ℝ)) *
            linearModelTotalVariationReal
              problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
              ⟨method t, method.iterates_mem_feasibleSet t⟩ ≤
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) +
            (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
    intro t ht
    exact
      standard_weight_totalVariationReal_drop_le
        method G₁ D hstep hholder hdiam hfinite t (Finset.mem_Icc.mp ht).2
        (hgradient t (Finset.mem_Icc.mp ht).2)
  have hsum :=
    Finset.sum_le_sum hpointwise
  have hdrop_telescope :
      Finset.sum (Finset.Icc m T) (fun t ↦
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1)))) =
        (problem.smoothPart (method m) + withTopRealPart problem.nonsmoothPart (method m)) -
          (problem.smoothPart (method (T + 1)) +
            withTopRealPart problem.nonsmoothPart (method (T + 1))) := by
    simpa using
      sum_Icc_sub_eq
        (fun t ↦ problem.smoothPart (method t) +
          withTopRealPart problem.nonsmoothPart (method t))
        hmT
  -- Sum the one-step inequalities and collapse the objective-drop part to the tail telescope.
  calc
    Finset.sum (Finset.Icc m T) (fun t ↦
        (2 / ((t + 2 : ℕ) : ℝ)) *
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩) ≤
      Finset.sum (Finset.Icc m T) (fun t ↦
        ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) +
          (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)))) := hsum
    _ =
      Finset.sum (Finset.Icc m T) (fun t ↦
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1)))) +
        Finset.sum (Finset.Icc m T) (fun t ↦
          (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
            rw [Finset.sum_add_distrib]
    _ =
      (problem.smoothPart (method m) + withTopRealPart problem.nonsmoothPart (method m)) -
        (problem.smoothPart (method (T + 1)) +
          withTopRealPart problem.nonsmoothPart (method (T + 1))) +
        Finset.sum (Finset.Icc m T) (fun t ↦
          (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
            rw [hdrop_telescope]

/-- Helper for Proposition 6.44: each standard-weight step controls the composite-objective gap
to any fixed future iterate by the current drop plus the explicit quadratic remainder. -/
private theorem standardWeight_futureGap_step_le
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ)
    {T t r : ℕ} (htT : t ≤ T) (htr : t < r)
    (hstep : ∀ s : ℕ, method.stepSize s = τ[standardWeight](s))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ s : ℕ, s ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method s,
          method.iterates_mem_feasibleSet s⟩) ≠ ⊤)
    (hgradient :
      ∀ s : ℕ, s ≤ T →
        method.gradient (method s) =
          InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates s))) :
    (2 / ((t + 2 : ℕ) : ℝ)) *
        (compositeObjectiveValue method t - compositeObjectiveValue method r) ≤
      (compositeObjectiveValue method t - compositeObjectiveValue method (t + 1)) +
        standardWeightErrorValue G₁ D t := by
  have hfuture :
      compositeObjectiveValue method t - compositeObjectiveValue method r ≤
        linearModelTotalVariationReal
          problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
          ⟨method t, method.iterates_mem_feasibleSet t⟩ := by
    -- Compare the future objective gap with the current total variation.
    simpa [compositeObjectiveValue] using
      (compositeObjectiveGapToFutureIterate_le_totalVariationReal
        (method := method) (T := T) (s := t) (r := r) htT (Nat.le_of_lt htr)
        (hgradient t htT) (hfinite t htT))
  have hscaled :
      (2 / ((t + 2 : ℕ) : ℝ)) *
          (compositeObjectiveValue method t - compositeObjectiveValue method r) ≤
        (2 / ((t + 2 : ℕ) : ℝ)) *
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩ := by
    exact mul_le_mul_of_nonneg_left hfuture (by positivity)
  -- Route correction: once the future gap is parked under `δ_real(x_t)`, the repaired one-step
  -- drop lemma closes the step immediately.
  exact hscaled.trans <|
    (by
      simpa [compositeObjectiveValue, standardWeightErrorValue] using
        (standard_weight_totalVariationReal_drop_le
          method G₁ D hstep hholder hdiam hfinite t htT (hgradient t htT)))

/-- Helper for Proposition 6.44: with the standard coefficients, the composite-objective gap
from `x_s` to any later iterate decays like `2 G₁ D² / (s + 1)`. -/
private theorem compositeObjectiveGapToFutureIterate_le_standardWeightRate
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ)
    {T s r : ℕ} (hspos : 1 ≤ s) (hsT : s ≤ T) (hsr : s ≤ r)
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤)
    (hgradient :
      ∀ t : ℕ, t ≤ T →
        method.gradient (method t) =
          InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates t))) :
    compositeObjectiveValue method s - compositeObjectiveValue method r ≤
      (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((s + 1 : ℕ) : ℝ) := by
  let gap : ℕ → ℝ := fun t ↦ compositeObjectiveValue method t - compositeObjectiveValue method r
  let rate : ℕ → ℝ := fun t ↦
    (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((t + 1 : ℕ) : ℝ)
  by_cases hsr_eq : s = r
  · -- The terminal iterate has zero future gap.
    subst hsr_eq
    have hrate_nonneg : 0 ≤ rate s := by
      dsimp [rate]
      positivity
    simpa [gap, rate] using hrate_nonneg
  · have hsr_lt : s < r := lt_of_le_of_ne hsr hsr_eq
    have hbase_step :=
      standardWeight_futureGap_step_le
        (method := method) (G₁ := G₁) (D := D) (T := T) (t := 0) (r := r)
        (by omega) (by omega) hstep hholder hdiam hfinite hgradient
    have hbase_gap :
        gap 1 ≤ standardWeightErrorValue G₁ D 0 := by
      -- Route correction: the `t = 0` step already seeds the induction by bounding the first
      -- future gap directly.
      dsimp [gap] at hbase_step ⊢
      nlinarith
    have hbase :
        gap 1 ≤ rate 1 := by
      have herror0_le :
          standardWeightErrorValue G₁ D 0 ≤ rate 1 := by
        have hfactor_nonneg : 0 ≤ (G₁ : ℝ) * D ^ (2 : ℕ) := by
          positivity
        dsimp [rate]
        simp [standardWeightErrorValue]
        nlinarith
      exact hbase_gap.trans herror0_le
    have hstep_rate :
        ∀ {t : ℕ}, 1 ≤ t → t < s → gap t ≤ rate t → gap (t + 1) ≤ rate (t + 1) := by
      intro t htpos hts hih
      have htT : t ≤ T := le_trans (Nat.le_of_lt hts) hsT
      have htr : t < r := lt_of_lt_of_le hts hsr
      have hfuture_step :=
        standardWeight_futureGap_step_le
          (method := method) (G₁ := G₁) (D := D) (T := T) (t := t) (r := r)
          htT htr hstep hholder hdiam hfinite hgradient
      have hcoeff_eq :
          1 - 2 / ((t + 2 : ℕ) : ℝ) = (t : ℝ) / ((t + 2 : ℕ) : ℝ) := by
        have ht2_ne : (((t + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp [ht2_ne]
        ring_nf
        norm_num [Nat.cast_add]
      have hrec :
          gap (t + 1) ≤
            ((t : ℝ) / ((t + 2 : ℕ) : ℝ)) * gap t + standardWeightErrorValue G₁ D t := by
        have hfuture_step' :
            (2 / ((t + 2 : ℕ) : ℝ)) * gap t ≤
              gap t - gap (t + 1) + standardWeightErrorValue G₁ D t := by
          simpa [gap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfuture_step
        have hrec' :
            gap (t + 1) ≤
              (1 - 2 / ((t + 2 : ℕ) : ℝ)) * gap t + standardWeightErrorValue G₁ D t := by
          nlinarith
        exact
          calc
          gap (t + 1) ≤
              (1 - 2 / ((t + 2 : ℕ) : ℝ)) * gap t + standardWeightErrorValue G₁ D t := hrec'
          _ = ((t : ℝ) / ((t + 2 : ℕ) : ℝ)) * gap t + standardWeightErrorValue G₁ D t := by
              rw [hcoeff_eq]
      have hcoeff_nonneg : 0 ≤ (t : ℝ) / ((t + 2 : ℕ) : ℝ) := by
        positivity
      have hscaled :
          ((t : ℝ) / ((t + 2 : ℕ) : ℝ)) * gap t ≤
            ((t : ℝ) / ((t + 2 : ℕ) : ℝ)) * rate t := by
        exact mul_le_mul_of_nonneg_left hih hcoeff_nonneg
      have hbound :
          ((t : ℝ) / ((t + 2 : ℕ) : ℝ)) * rate t + standardWeightErrorValue G₁ D t ≤
            rate (t + 1) := by
        have ht1_ne : (((t + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        have ht2_ne : (((t + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
        have hfactor_nonneg : 0 ≤ 2 * (G₁ : ℝ) * D ^ (2 : ℕ) := by positivity
        have hscalar :
            (t : ℝ) / ((t + 2 : ℕ) : ℝ) * (1 / ((t + 1 : ℕ) : ℝ)) +
                1 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) ≤
              1 / ((t + 2 : ℕ) : ℝ) := by
          have haux : (1 : ℝ) ≤ (((t + 1 : ℕ) : ℝ)) := by
            exact_mod_cast (show 1 ≤ t + 1 by omega)
          field_simp [ht1_ne, ht2_ne]
          have hidentity :
              (((t + 2 : ℕ) : ℝ)) * (((t + 1 : ℕ) : ℝ)) =
                (t : ℝ) * (((t + 2 : ℕ) : ℝ)) + (((t + 1 : ℕ) : ℝ)) + 1 := by
            norm_num [Nat.cast_add, Nat.cast_mul]
            ring
          nlinarith
        calc
          ((t : ℝ) / ((t + 2 : ℕ) : ℝ)) * rate t + standardWeightErrorValue G₁ D t =
              (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) *
                ((t : ℝ) / ((t + 2 : ℕ) : ℝ) * (1 / ((t + 1 : ℕ) : ℝ)) +
                  1 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
                    dsimp [rate, standardWeightErrorValue]
                    field_simp [ht1_ne, ht2_ne]
          _ ≤ (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) * (1 / ((t + 2 : ℕ) : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hscalar hfactor_nonneg
          _ = rate (t + 1) := by
                dsimp [rate]
                ring
      exact hrec.trans <| (add_le_add hscaled le_rfl).trans hbound
    have hforall :
        ∀ n : ℕ, n < s → gap (n + 1) ≤ rate (n + 1) := by
      intro n hn
      induction n with
      | zero =>
          simpa [gap, rate] using hbase
      | succ n ih =>
          have hn' : n < s := lt_trans (Nat.lt_succ_self n) hn
          have hprev : gap (n + 1) ≤ rate (n + 1) := ih hn'
          simpa [gap, rate] using
            (hstep_rate (t := n + 1) (by omega) hn hprev)
    have hs_pred_lt : s - 1 < s := Nat.pred_lt (Nat.ne_of_gt hspos)
    have hs_eq : s - 1 + 1 = s := Nat.succ_pred_eq_of_pos hspos
    simpa [gap, rate, hs_eq] using hforall (s - 1) hs_pred_lt

/-- Helper for Proposition 6.44: on any late-half interval, the sampled minimum times the late
standard-weight denominator is bounded by the boundary drop plus the square-error tail. -/
private theorem lateHalfBestValue_mul_weightSum_le_boundaryPlusTail
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ)
    {T m : ℕ} (hmT : m ≤ T)
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤)
    (hgradient :
      ∀ t : ℕ, t ≤ T →
        method.gradient (method t) =
          InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates t))) :
    bestFunctionValueUpTo
        (fun t ↦
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩)
        T *
        (Finset.sum (Finset.Icc m T) (fun t ↦ 2 / ((t + 2 : ℕ) : ℝ))) ≤
      (compositeObjectiveValue method m - compositeObjectiveValue method (T + 1)) +
        Finset.sum (Finset.Icc m T) (standardWeightErrorValue G₁ D) := by
  let values : ℕ → ℝ := fun t ↦
    linearModelTotalVariationReal
      problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
      ⟨method t, method.iterates_mem_feasibleSet t⟩
  have hbest_le :
      ∀ t ∈ Finset.Icc m T,
        bestFunctionValueUpTo values T ≤ values t := by
    intro t ht
    exact bestFunctionValueUpTo_le ⟨t, Nat.lt_succ_of_le (Finset.mem_Icc.mp ht).2⟩
  have hweighted :
      bestFunctionValueUpTo values T *
          Finset.sum (Finset.Icc m T) (fun t ↦ 2 / ((t + 2 : ℕ) : ℝ)) ≤
        Finset.sum (Finset.Icc m T) (fun t ↦
          (2 / ((t + 2 : ℕ) : ℝ)) * values t) := by
    -- Lower-bound every sampled value on the late-half interval by the sampled minimum.
    calc
      bestFunctionValueUpTo values T *
          Finset.sum (Finset.Icc m T) (fun t ↦ 2 / ((t + 2 : ℕ) : ℝ)) =
        Finset.sum (Finset.Icc m T) (fun t ↦
          bestFunctionValueUpTo values T * (2 / ((t + 2 : ℕ) : ℝ))) := by
            rw [Finset.mul_sum]
      _ =
        Finset.sum (Finset.Icc m T) (fun t ↦
          (2 / ((t + 2 : ℕ) : ℝ)) * bestFunctionValueUpTo values T) := by
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            ring
      _ ≤
        Finset.sum (Finset.Icc m T) (fun t ↦
          (2 / ((t + 2 : ℕ) : ℝ)) * values t) := by
            refine Finset.sum_le_sum fun t ht ↦ ?_
            exact mul_le_mul_of_nonneg_left (hbest_le t ht) (by positivity)
  -- Route correction: the late-half assembly is just sampled-minimum monotonicity plus the
  -- already-proved tail telescope for the weighted total variation.
  exact hweighted.trans <|
    (sum_standardWeightStepSize_mul_totalVariationReal_le_tailDropPlusError
      method G₁ D hmT hstep hholder hdiam hfinite hgradient)

/-- Helper for Proposition 6.44: telescoping adjacent logarithmic ratios recovers the total
logarithm of the endpoint ratio. -/
private theorem sum_range_log_succ_ratio_eq_log_div (a n : ℕ) (ha : 0 < a) :
    Finset.sum (Finset.range n)
        (fun k ↦ Real.log ((((a + k + 1 : ℕ) : ℝ)) / (((a + k : ℕ) : ℝ)))) =
    Real.log ((((a + n : ℕ) : ℝ)) / ((a : ℕ) : ℝ)) := by
  induction n with
  | zero =>
      have ha_ne : (((a : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
      simp [ha_ne]
  | succ n ih =>
      have ha_ne : (((a : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
      have han_ne : (((a + n : ℕ) : ℝ)) ≠ 0 := by positivity
      rw [Finset.sum_range_succ, ih]
      have hmul :
          ((((a + (n + 1) : ℕ) : ℝ)) / ((a : ℕ) : ℝ)) =
            ((((a + n : ℕ) : ℝ)) / ((a : ℕ) : ℝ)) *
              ((((a + n + 1 : ℕ) : ℝ)) / (((a + n : ℕ) : ℝ))) := by
        field_simp [ha_ne, han_ne]
        ring
      rw [hmul, Real.log_mul (by positivity) (by positivity)]

/-- Helper for Proposition 6.44: the late-half denominator for the odd interval
`{m, ..., 2m + 1}` is at least `2 log 2`. -/
private theorem lateHalfStandardWeightDenominator_ge_twoLogTwo (m : ℕ) :
    2 * Real.log 2 ≤
      Finset.sum (Finset.Icc m (2 * m + 1)) (fun t ↦ 2 / ((t + 2 : ℕ) : ℝ)) := by
  let g : ℕ → ℝ := fun k ↦ 2 / ((m + k + 2 : ℕ) : ℝ)
  have hm : m ≤ 2 * m + 1 := by omega
  have hreindex :
      Finset.sum (Finset.Icc m (2 * m + 1)) (fun t ↦ 2 / ((t + 2 : ℕ) : ℝ)) =
        Finset.sum (Finset.range (m + 2)) g := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    have hlen : 2 * m + 1 + 1 - m = m + 2 := by omega
    rw [hlen]
  have hpointwise :
      ∀ k ∈ Finset.range (m + 2),
        2 * Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) ≤ g k := by
    intro k hk
    have hpos : 0 < ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) := by
      positivity
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hrewrite :
        ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) - 1 =
          1 / (((m + k + 2 : ℕ) : ℝ)) := by
      have hdenom : (((m + k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hdenom]
      norm_num [Nat.cast_add]
    dsimp [g]
    rw [hrewrite] at hlog
    have hscaled :
        Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) +
            Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) ≤
          1 / (((m + k + 2 : ℕ) : ℝ)) + 1 / (((m + k + 2 : ℕ) : ℝ)) := by
      exact add_le_add hlog hlog
    calc
      2 * Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) =
          Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) +
            Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ))) := by ring
      _ ≤ 1 / (((m + k + 2 : ℕ) : ℝ)) + 1 / (((m + k + 2 : ℕ) : ℝ)) := hscaled
      _ = g k := by
            dsimp [g]
            ring
  have hsum_le :
      Finset.sum (Finset.range (m + 2))
          (fun k ↦ 2 * Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ)))) ≤
        Finset.sum (Finset.range (m + 2)) g := by
    exact Finset.sum_le_sum hpointwise
  have htel :
      Finset.sum (Finset.range (m + 2))
          (fun k ↦ 2 * Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ)))) =
        2 * Real.log 2 := by
    calc
      Finset.sum (Finset.range (m + 2))
          (fun k ↦ 2 * Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ)))) =
        Finset.sum (Finset.range (m + 2))
          (fun k ↦ 2 * Real.log ((((m + 2 + k + 1 : ℕ) : ℝ)) / (((m + 2 + k : ℕ) : ℝ)))) := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = 2 * Real.log ((((m + 2 + (m + 2) : ℕ) : ℝ)) / (((m + 2 : ℕ) : ℝ))) := by
            rw [← Finset.mul_sum, sum_range_log_succ_ratio_eq_log_div (m + 2) (m + 2)
              (by positivity)]
      _ = 2 * Real.log 2 := by
            have hratio :
                ((((m + 2 + (m + 2) : ℕ) : ℝ)) / (((m + 2 : ℕ) : ℝ))) = 2 := by
              have hdenom : (((m + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
              field_simp [hdenom]
              norm_num [Nat.cast_add, Nat.cast_mul]
              ring
            rw [hratio]
  -- The late-half denominator dominates the doubled logarithmic telescope term.
  rw [hreindex]
  calc
    2 * Real.log 2 =
        Finset.sum (Finset.range (m + 2))
          (fun k ↦ 2 * Real.log ((((m + k + 3 : ℕ) : ℝ)) / (((m + k + 2 : ℕ) : ℝ)))) := by
            symm
            exact htel
    _ ≤ Finset.sum (Finset.range (m + 2)) g := hsum_le

/-- Helper for Proposition 6.44: once `m ≥ 4`, the late-half quadratic tail is bounded by
`(12 / 11) G₁ D² / (m + 1)`. -/
private theorem lateHalfSquareTail_le_twelveElevenths
    (G₁ : NNReal) (D : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Finset.sum (Finset.Icc m (2 * m + 1)) (standardWeightErrorValue G₁ D) ≤
      (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 1 : ℕ) : ℝ) := by
  by_cases hm4 : 4 ≤ m
  · have hmT : m ≤ 2 * m + 1 := by omega
    have hfactor_nonneg : 0 ≤ 2 * (G₁ : ℝ) * D ^ (2 : ℕ) := by positivity
    have hpointwise :
        ∀ t ∈ Finset.Icc m (2 * m + 1),
          standardWeightErrorValue G₁ D t ≤
            (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) *
              (1 / ((t + 1 : ℕ) : ℝ) - 1 / ((t + 2 : ℕ) : ℝ)) := by
      intro t ht
      have ht1 : (((t + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have ht2 : (((t + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hrecip :
          1 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) ≤
            1 / ((t + 1 : ℕ) : ℝ) - 1 / ((t + 2 : ℕ) : ℝ) := by
        have htelescoping :
            1 / ((t + 1 : ℕ) : ℝ) - 1 / ((t + 2 : ℕ) : ℝ) =
              1 / ((((t + 1 : ℕ) : ℝ)) * (((t + 2 : ℕ) : ℝ))) := by
          field_simp [ht1, ht2]
          ring_nf
          norm_num [Nat.cast_add]
        rw [htelescoping]
        have ht1_le : (((t + 1 : ℕ) : ℝ)) ≤ (((t + 2 : ℕ) : ℝ)) := by
          exact_mod_cast (Nat.le_succ _)
        have hsquare_ge :
            ((((t + 1 : ℕ) : ℝ)) * (((t + 2 : ℕ) : ℝ))) ≤
              ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ)) := by
          nlinarith
        have hprod_pos : 0 < ((((t + 1 : ℕ) : ℝ)) * (((t + 2 : ℕ) : ℝ))) := by
          positivity
        exact one_div_le_one_div_of_le hprod_pos hsquare_ge
      -- Compare the reciprocal-square tail term pointwise with a telescoping reciprocal gap.
      simpa [standardWeightErrorValue, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hrecip hfactor_nonneg
    have hsum :=
      Finset.sum_le_sum hpointwise
    have htel :
        Finset.sum (Finset.Icc m (2 * m + 1))
            (fun t ↦ 1 / ((t + 1 : ℕ) : ℝ) - 1 / ((t + 2 : ℕ) : ℝ)) =
          1 / ((m + 1 : ℕ) : ℝ) - 1 / ((2 * m + 3 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, add_assoc] using
        (sum_Icc_sub_eq (fun t ↦ 1 / ((t + 1 : ℕ) : ℝ)) hmT)
    have htail :
        1 / ((m + 1 : ℕ) : ℝ) - 1 / ((2 * m + 3 : ℕ) : ℝ) ≤
          6 / (11 * ((m + 1 : ℕ) : ℝ)) := by
      have hm' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
      have hm1_pos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
      have hm3_pos : 0 < (((2 * m + 3 : ℕ) : ℝ)) := by positivity
      have hnum :
          (((m + 2 : ℕ) : ℝ)) ≤
            (6 / 11 : ℝ) * (((2 * m + 3 : ℕ) : ℝ)) := by
        have hnum' :
            (11 : ℝ) * (((m + 2 : ℕ) : ℝ)) ≤ 6 * (((2 * m + 3 : ℕ) : ℝ)) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          nlinarith [hm']
        nlinarith
      calc
        1 / ((m + 1 : ℕ) : ℝ) - 1 / ((2 * m + 3 : ℕ) : ℝ) =
            (((m + 2 : ℕ) : ℝ)) /
              ((((m + 1 : ℕ) : ℝ)) * (((2 * m + 3 : ℕ) : ℝ))) := by
                field_simp [hm1_pos.ne', hm3_pos.ne']
                norm_num [Nat.cast_add, Nat.cast_mul]
                ring
        _ ≤
            (((6 / 11 : ℝ) * (((2 * m + 3 : ℕ) : ℝ))) /
              ((((m + 1 : ℕ) : ℝ)) * (((2 * m + 3 : ℕ) : ℝ)))) := by
                exact div_le_div_of_nonneg_right hnum (by positivity)
        _ = 6 / (11 * ((m + 1 : ℕ) : ℝ)) := by
              field_simp [hm1_pos.ne', hm3_pos.ne']

    -- Telescope the reciprocal gaps and then close the remaining scalar inequality.
    calc
      Finset.sum (Finset.Icc m (2 * m + 1)) (standardWeightErrorValue G₁ D) ≤
          Finset.sum (Finset.Icc m (2 * m + 1)) (fun t ↦
            (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) *
              (1 / ((t + 1 : ℕ) : ℝ) - 1 / ((t + 2 : ℕ) : ℝ))) := hsum
      _ =
          (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) *
            (1 / ((m + 1 : ℕ) : ℝ) - 1 / ((2 * m + 3 : ℕ) : ℝ)) := by
              rw [← Finset.mul_sum, htel]
      _ ≤
          (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) * (6 / (11 * ((m + 1 : ℕ) : ℝ))) := by
              exact mul_le_mul_of_nonneg_left htail hfactor_nonneg
      _ = (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 1 : ℕ) : ℝ) := by
            field_simp
            ring
  · have hm_le_three : m ≤ 3 := by omega
    have hfactor_nonneg : 0 ≤ (G₁ : ℝ) * D ^ (2 : ℕ) := by positivity
    interval_cases m
    · have hconst :
          (Finset.sum (Finset.Icc 1 3) fun t ↦ 2 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) =
            2 / (3 : ℝ) ^ (2 : ℕ) + 2 / (4 : ℝ) ^ (2 : ℕ) + 2 / (5 : ℝ) ^ (2 : ℕ) := by
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
        norm_num
      have hconst_le :
          2 / (3 : ℝ) ^ (2 : ℕ) + 2 / (4 : ℝ) ^ (2 : ℕ) + 2 / (5 : ℝ) ^ (2 : ℕ) ≤ 6 / 11 := by
        norm_num
      calc
        Finset.sum (Finset.Icc 1 3) (standardWeightErrorValue G₁ D) =
            (G₁ : ℝ) * D ^ (2 : ℕ) *
              Finset.sum (Finset.Icc 1 3) (fun t ↦ 2 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun t ht ↦ ?_
                dsimp [standardWeightErrorValue]
                ring
        _ =
            (G₁ : ℝ) * D ^ (2 : ℕ) *
              (2 / (3 : ℝ) ^ (2 : ℕ) + 2 / (4 : ℝ) ^ (2 : ℕ) + 2 / (5 : ℝ) ^ (2 : ℕ)) := by
              rw [hconst]
        _ ≤ (G₁ : ℝ) * D ^ (2 : ℕ) * (6 / 11 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hconst_le hfactor_nonneg
        _ = (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / 2 := by ring
    · have hconst :
          (Finset.sum (Finset.Icc 2 5) fun t ↦ 2 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) =
            2 / (4 : ℝ) ^ (2 : ℕ) + 2 / (5 : ℝ) ^ (2 : ℕ) + 2 / (6 : ℝ) ^ (2 : ℕ) +
              2 / (7 : ℝ) ^ (2 : ℕ) := by
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
          Finset.sum_Icc_succ_top (by omega)]
        norm_num
      have hconst_le :
          2 / (4 : ℝ) ^ (2 : ℕ) + 2 / (5 : ℝ) ^ (2 : ℕ) + 2 / (6 : ℝ) ^ (2 : ℕ) +
              2 / (7 : ℝ) ^ (2 : ℕ) ≤ 4 / 11 := by
        norm_num
      calc
        Finset.sum (Finset.Icc 2 5) (standardWeightErrorValue G₁ D) =
            (G₁ : ℝ) * D ^ (2 : ℕ) *
              Finset.sum (Finset.Icc 2 5) (fun t ↦ 2 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun t ht ↦ ?_
                dsimp [standardWeightErrorValue]
                ring
        _ =
            (G₁ : ℝ) * D ^ (2 : ℕ) *
              (2 / (4 : ℝ) ^ (2 : ℕ) + 2 / (5 : ℝ) ^ (2 : ℕ) + 2 / (6 : ℝ) ^ (2 : ℕ) +
                2 / (7 : ℝ) ^ (2 : ℕ)) := by
              rw [hconst]
        _ ≤ (G₁ : ℝ) * D ^ (2 : ℕ) * (4 / 11 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hconst_le hfactor_nonneg
        _ = (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / 3 := by ring
    · have hconst :
          (Finset.sum (Finset.Icc 3 7) fun t ↦ 2 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) =
            2 / (5 : ℝ) ^ (2 : ℕ) + 2 / (6 : ℝ) ^ (2 : ℕ) + 2 / (7 : ℝ) ^ (2 : ℕ) +
              2 / (8 : ℝ) ^ (2 : ℕ) + 2 / (9 : ℝ) ^ (2 : ℕ) := by
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
          Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
        norm_num
      have hconst_le :
          2 / (5 : ℝ) ^ (2 : ℕ) + 2 / (6 : ℝ) ^ (2 : ℕ) + 2 / (7 : ℝ) ^ (2 : ℕ) +
              2 / (8 : ℝ) ^ (2 : ℕ) + 2 / (9 : ℝ) ^ (2 : ℕ) ≤ 3 / 11 := by
        norm_num
      calc
        Finset.sum (Finset.Icc 3 7) (standardWeightErrorValue G₁ D) =
            (G₁ : ℝ) * D ^ (2 : ℕ) *
              Finset.sum (Finset.Icc 3 7) (fun t ↦ 2 / ((((t + 2 : ℕ) : ℝ)) ^ (2 : ℕ))) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun t ht ↦ ?_
                dsimp [standardWeightErrorValue]
                ring
        _ =
            (G₁ : ℝ) * D ^ (2 : ℕ) *
              (2 / (5 : ℝ) ^ (2 : ℕ) + 2 / (6 : ℝ) ^ (2 : ℕ) + 2 / (7 : ℝ) ^ (2 : ℕ) +
                2 / (8 : ℝ) ^ (2 : ℕ) + 2 / (9 : ℝ) ^ (2 : ℕ)) := by
              rw [hconst]
        _ ≤ (G₁ : ℝ) * D ^ (2 : ℕ) * (3 / 11 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hconst_le hfactor_nonneg
        _ = (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / 4 := by ring

/-- Helper for Proposition 6.44: the elementary bound `log 2 ≤ 3 / 4` is enough to close the
finite small-`T` branches after the exact rational estimates are evaluated. -/
private theorem logTwo_le_threeQuarters : Real.log 2 ≤ 3 / 4 := by
  -- A library decimal upper bound already puts `log 2` safely below `3 / 4`.
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  nlinarith

/-- Proposition 6.44: let `T ≥ 1` be odd. Along the Chapter 6 conditional-gradient scheme, if the
step sizes are the standard coefficients `τ_t = τ[standardWeight](t) = 2 / (t + 2)`, the smooth
part has `ν = 1` Hölder gradient on the feasible set with constant `G₁`, the feasible set has
diameter bounded by `D`, the chosen dual field agrees with the ambient gradient along the first
`T + 1` iterates, and the total variations along the first `T + 1` iterates are finite, then the
sampled minimum total variation
`δ_T^* = bestFunctionValueUpTo
  (fun t ↦
    linearModelTotalVariationReal problem.feasibleSet problem.smoothPart
      (withTopRealPart problem.nonsmoothPart) ⟨method t, method.iterates_mem_feasibleSet t⟩) T`
satisfies
`δ_T^* ≤ (34 / (11 log 2)) G₁ D^2 / (T + 1)`. -/
theorem bestFunctionValueUpTo_totalVariationReal_le_standard_weight_rate_nu_one
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ) {T : ℕ}
    (hTpos : 1 ≤ T) (hTodd : Odd T)
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hgradient :
      ∀ t : ℕ, t ≤ T →
        method.gradient (method t) =
          InnerProductSpace.toDualMap ℝ E (gradient problem.smoothPart (method.iterates t)))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤) :
    bestFunctionValueUpTo
        (fun t ↦
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩)
        T ≤
      (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((T + 1 : ℕ) : ℝ) := by
  rcases hTodd with ⟨m, rfl⟩
  cases m with
  | zero =>
      -- Route correction: the first odd horizon `T = 1` is easiest to close directly.
      let values : ℕ → ℝ := fun t ↦
        linearModelTotalVariationReal
          problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
          ⟨method t, method.iterates_mem_feasibleSet t⟩
      have hbest_le :
          bestFunctionValueUpTo values 1 ≤ values 1 := by
        exact bestFunctionValueUpTo_le ⟨1, by decide⟩
      have hgap12_step :=
        standardWeight_futureGap_step_le
          (method := method) (G₁ := G₁) (D := D) (T := 1) (t := 0) (r := 2)
          (by omega) (by omega) hstep hholder hdiam hfinite hgradient
      have hgap12 :
          compositeObjectiveValue method 1 - compositeObjectiveValue method 2 ≤
            standardWeightErrorValue G₁ D 0 := by
        -- The `t = 0` step already controls the next future gap.
        nlinarith [hgap12_step]
      have hdrop1 :=
        standard_weight_totalVariationReal_drop_le
          (method := method) (G₁ := G₁) (D := D) (T := 1)
          hstep hholder hdiam hfinite 1 (by omega) (hgradient 1 (by omega))
      have hvalue1 :
          values 1 ≤ (13 / 12 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) := by
        -- Use the `t = 1` real drop bound together with the previous `F₁ - F₂` estimate.
        have hdrop1' :
            (2 / 3 : ℝ) * values 1 ≤
              compositeObjectiveValue method 1 - compositeObjectiveValue method 2 +
                standardWeightErrorValue G₁ D 1 := by
          simpa [values, compositeObjectiveValue] using hdrop1
        have hstep_bound :
            values 1 ≤
              (3 / 2 : ℝ) *
                (compositeObjectiveValue method 1 - compositeObjectiveValue method 2 +
                  standardWeightErrorValue G₁ D 1) := by
          nlinarith [hdrop1']
        have hgap_bound :
            compositeObjectiveValue method 1 - compositeObjectiveValue method 2 +
                standardWeightErrorValue G₁ D 1 ≤
              (13 / 18 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) := by
          simp [standardWeightErrorValue] at hgap12 ⊢
          nlinarith [hgap12]
        have hscaled :
            (3 / 2 : ℝ) *
                (compositeObjectiveValue method 1 - compositeObjectiveValue method 2 +
                  standardWeightErrorValue G₁ D 1) ≤
              (3 / 2 : ℝ) * ((13 / 18 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hgap_bound (by positivity)
        calc
          values 1 ≤
              (3 / 2 : ℝ) *
                (compositeObjectiveValue method 1 - compositeObjectiveValue method 2 +
                  standardWeightErrorValue G₁ D 1) := hstep_bound
          _ ≤ (3 / 2 : ℝ) * ((13 / 18 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ)) := hscaled
          _ = (13 / 12 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) := by ring
      have hconst :
          (13 / 12 : ℝ) ≤ (34 / (11 * Real.log 2)) / 2 := by
        have hlog_pos : 0 < 11 * Real.log 2 := by
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
          nlinarith
        have hconst' : (13 / 12 : ℝ) ≤ 17 / (11 * Real.log 2) := by
          refine (le_div_iff₀ hlog_pos).2 ?_
          nlinarith [logTwo_le_threeQuarters]
        have hrewrite :
            17 / (11 * Real.log 2) = (34 / (11 * Real.log 2)) / 2 := by
          have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
          field_simp [hlog2_ne]
          ring
        simpa [hrewrite] using hconst'
      have hfactor_nonneg : 0 ≤ (G₁ : ℝ) * D ^ (2 : ℕ) := by
        positivity
      have htarget1 :
          (13 / 12 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) ≤
            ((34 / (11 * Real.log 2)) / 2) * ((G₁ : ℝ) * D ^ (2 : ℕ)) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hconst hfactor_nonneg
      have htarget_eq :
          ((34 / (11 * Real.log 2)) / 2) * ((G₁ : ℝ) * D ^ (2 : ℕ)) =
            (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((1 + 1 : ℕ) : ℝ) := by
        norm_num
        ring
      calc
        bestFunctionValueUpTo values 1 ≤ values 1 := hbest_le
        _ ≤ (13 / 12 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) := hvalue1
        _ ≤ ((34 / (11 * Real.log 2)) / 2) * ((G₁ : ℝ) * D ^ (2 : ℕ)) := htarget1
        _ = (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((1 + 1 : ℕ) : ℝ) :=
            htarget_eq
  | succ m =>
      let values : ℕ → ℝ := fun t ↦
        linearModelTotalVariationReal
          problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
          ⟨method t, method.iterates_mem_feasibleSet t⟩
      let best : ℝ := bestFunctionValueUpTo values (2 * m + 3)
      let denom : ℝ :=
        Finset.sum (Finset.Icc (m + 1) (2 * m + 3)) (fun t ↦ 2 / ((t + 2 : ℕ) : ℝ))
      have hlate :
          best * denom ≤
            (compositeObjectiveValue method (m + 1) - compositeObjectiveValue method (2 * m + 4)) +
              Finset.sum (Finset.Icc (m + 1) (2 * m + 3)) (standardWeightErrorValue G₁ D) := by
        -- The late-half weighted sum is already available once the standard-weight drop helpers
        -- are in place.
        simpa [values, best, denom] using
          (lateHalfBestValue_mul_weightSum_le_boundaryPlusTail
            (method := method) (G₁ := G₁) (D := D) (T := 2 * m + 3) (m := m + 1)
            (by omega) hstep hholder hdiam hfinite hgradient)
      have hboundary :
          compositeObjectiveValue method (m + 1) - compositeObjectiveValue method (2 * m + 4) ≤
            (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((m + 2 : ℕ) : ℝ) := by
        -- The repaired future-gap rate is consumed exactly at the late-half boundary point.
        simpa [Nat.cast_add, add_assoc] using
          (compositeObjectiveGapToFutureIterate_le_standardWeightRate
            (method := method) (G₁ := G₁) (D := D)
            (T := 2 * m + 3) (s := m + 1) (r := 2 * m + 4)
            (by omega) (by omega) (by omega)
            hstep hholder hdiam hfinite hgradient)
      have htail :
          Finset.sum (Finset.Icc (m + 1) (2 * m + 3)) (standardWeightErrorValue G₁ D) ≤
            (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ) := by
        simpa [Nat.cast_add, add_assoc] using
          (lateHalfSquareTail_le_twelveElevenths (G₁ := G₁) (D := D) (m := m + 1)
            (by omega))
      have hcombine :
          best * denom ≤
            (34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ) := by
        have hsum_bound :
            compositeObjectiveValue method (m + 1) - compositeObjectiveValue method (2 * m + 4) +
                Finset.sum (Finset.Icc (m + 1) (2 * m + 3)) (standardWeightErrorValue G₁ D) ≤
              (34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ) := by
          calc
            compositeObjectiveValue method (m + 1) - compositeObjectiveValue method (2 * m + 4) +
                Finset.sum (Finset.Icc (m + 1) (2 * m + 3)) (standardWeightErrorValue G₁ D) ≤
              (2 * (G₁ : ℝ) * D ^ (2 : ℕ)) / ((m + 2 : ℕ) : ℝ) +
                (12 / 11) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ) := by
                  exact add_le_add hboundary htail
            _ = (34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ) := by
                  ring
        exact hlate.trans hsum_bound
      have hdenom_lower : 2 * Real.log 2 ≤ denom := by
        simpa [denom] using lateHalfStandardWeightDenominator_ge_twoLogTwo (m + 1)
      have h2log_pos : 0 < 2 * Real.log 2 := by
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
        nlinarith
      have hdenom_pos : 0 < denom := lt_of_lt_of_le h2log_pos hdenom_lower
      have hdiv :
          best ≤
            ((34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ)) / denom := by
        refine (le_div_iff₀ hdenom_pos).2 ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcombine
      have hdenom_inv :
          1 / denom ≤ 1 / (2 * Real.log 2) := by
        simpa using one_div_le_one_div_of_le h2log_pos hdenom_lower
      have hnumerator_nonneg :
          0 ≤ (34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ) := by
        positivity
      have hcompare :
          ((34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ)) / denom ≤
            ((34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ)) /
              (2 * Real.log 2) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hdenom_inv hnumerator_nonneg
      have hcast :
          (((2 * m + 4 : ℕ) : ℝ)) = 2 * (((m + 2 : ℕ) : ℝ)) := by
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      have htarget_eq :
          ((34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ)) /
              (2 * Real.log 2) =
            (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((2 * m + 4 : ℕ) : ℝ) := by
        rw [hcast]
        have hm2_ne : (((m + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
        have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
        field_simp [hm2_ne, hlog2_ne]
      calc
        bestFunctionValueUpTo values (2 * m + 3) = best := by rfl
        _ ≤ ((34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ)) / denom := hdiv
        _ ≤
            ((34 / 11 : ℝ) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((m + 2 : ℕ) : ℝ)) /
              (2 * Real.log 2) := hcompare
        _ =
            (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((2 * m + 4 : ℕ) : ℝ) :=
              htarget_eq

end

end ConditionalGradientContraction
