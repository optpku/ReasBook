/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_54
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.12 lies in the Chapter 6 conditional-gradient / weighted upper-bound domain.

Sampled owner-style declarations:
- `initialLinearizationGap` in `Definition_6_54`, the source-facing owner of the initial quantity
  `V₀`;
- `linearOptimizationOracleErrorBound` in `Definition_6_54`, the Chapter 6 owner of the
  cumulative error term `B_{ν,t}`;
- `LinearOracleCompositeMethod` in `Algorithm_6_4`, the chapter owner of the iterate and
  oracle-point data for method `(6.4.12)`;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the ambient
  extended-valued bridge/view owner that `Definition_6_54` specializes away from on this theorem
  surface.

Best owner abstraction:
- source-facing: the weighted composite upper bound with
  `initialLinearizationGap Q f Ψ (method 0)` as the initial quantity;
- core/canonical: `LinearOracleCompositeMethod` together with
  `linearOptimizationOracleErrorBound`;
- bridge/view: the ambient extended-regularizer gap value, which should not appear in the theorem
  statement.

Primitive data:
- the feasible set `Q`, objective `f`, subtype regularizer `Ψ`, and method data;
- convexity of the canonical ambient extension `Function.extend Subtype.val Ψ 0` on `Q`, the
  owner abstraction that expresses convexity of the subtype regularizer along feasible segments;
- the weight sequence `a`, Hölder data `ν`, `Gν`, `D`, and the Chapter 6 hypotheses on `a`,
  `τ_t`, and the `(6.4.3)`-style error term.

Derived API:
- the weighted affine-linearization upper bound at time `t`;
- the canonical Chapter 6 error term
  `linearOptimizationOracleErrorBound (initialLinearizationGap Q f Ψ (method 0)) a Gν D ν t`.

Source/core/bridge triage:
- source-facing: this weighted estimate for the composite conditional-gradient method;
- core/canonical: the Chapter 6 owners `initialLinearizationGap` and
  `linearOptimizationOracleErrorBound`;
- bridge/view: `ConditionalGradientContraction.linearizedCompositeGap`, used upstream only to
  justify `initialLinearizationGap` and intentionally absent from the theorem surface.
-/

-- Proof sketch: argue by induction on `t`. For the induction step, combine convexity of `f`
-- on `Q` and convexity of the ambient extension `Function.extend Subtype.val Ψ 0` on `Q` with
-- the update
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t`, use the oracle minimization property at `v_t`, and then
-- insert the assumed `(6.4.3)`-style Hölder error bound to absorb the residual term into the
-- Chapter 6 owner `linearOptimizationOracleErrorBound`, initialized by the source-facing
-- constrained linearization-gap owner `initialLinearizationGap` at the primitive starting point
-- `x₀ = method.x0`.
/-- Helper for Theorem 6.12: the accumulated weights satisfy the one-step recursion
`A_{t+1} = A_t + a_{t+1}`. -/
lemma accumulatedWeights_succ
    (a : ℕ → ℝ) (t : ℕ) :
    accumulatedWeights a (t + 1) = A[a](t) + a (t + 1) := by
  -- Expand the defining finite sums and isolate the new last term.
  rw [accumulatedWeights_apply, accumulatedWeights_apply, Finset.sum_range_succ]

/-- Helper for Theorem 6.12: positivity of the weights propagates to positivity of the
accumulated sums `A_t`. -/
lemma accumulatedWeights_pos
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t) :
    ∀ t : ℕ, 0 < A[a](t) := by
  intro t
  induction t with
  | zero =>
      -- At time `0`, the accumulated weight is exactly `a₀`.
      simpa [accumulatedWeights_apply] using ha_pos 0
  | succ t ih =>
      -- The recursion adds the positive weight `a_{t+1}` to the positive previous sum.
      rw [accumulatedWeights_succ]
      linarith [ih, ha_pos (t + 1)]

/-- Helper for Theorem 6.12: the Chapter 6 oracle-error term satisfies its defining one-step
recursion. -/
lemma linearOptimizationOracleErrorBound_succ
    (V0 : ℝ) (a : ℕ → ℝ) (Gν D ν : ℝ) (t : ℕ) :
    linearOptimizationOracleErrorBound V0 a Gν D ν (t + 1) =
      linearOptimizationOracleErrorBound V0 a Gν D ν t +
        (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
          Gν * Real.rpow D (1 + ν) := by
  -- Expand the finite interval sum and peel off the top index `t + 1`.
  rw [linearOptimizationOracleErrorBound_def, linearOptimizationOracleErrorBound_def,
    Finset.sum_Icc_succ_top (show 1 ≤ t + 1 by omega)]
  ring

/-- Helper for Theorem 6.12: every oracle-objective drop at the starting point is bounded by the
initial linearization gap `V₀`. -/
lemma oracle_objective_gap_le_initialLinearizationGap
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (method : LinearOracleCompositeMethod Q f Ψ) (x : Q) :
    linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q method.x0)) Ψ method.x0 -
      linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q method.x0)) Ψ x ≤
      initialLinearizationGap Q f Ψ method.x0 := by
  -- Rewrite `V₀` as the supremum of all oracle-objective drops from the starting point.
  rw [initialLinearizationGap_eq_oracleObjectiveGapSup]
  refine le_csSup ?_ ?_
  · -- The oracle point at time `0` gives an upper bound on every such drop.
    refine ⟨linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q method.x0)) Ψ method.x0 -
      linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q method.x0)) Ψ
        (method.oraclePoint 0), ?_⟩
    rintro _ ⟨y, rfl⟩
    simpa using sub_le_sub_left
      (method.oraclePoint_linearOptimizationOracleObjective_le 0 y)
      (linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q method.x0)) Ψ method.x0)
  · exact ⟨x, rfl⟩

/-- Helper for Theorem 6.12: the initial weighted bound at `t = 0` is exactly the starting
oracle-objective gap estimate controlled by `initialLinearizationGap`. -/
lemma weighted_objective_upper_bound_base_case
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (method : LinearOracleCompositeMethod Q f Ψ)
    (a : ℕ → ℝ)
    (ν Gν D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (x : Q) :
    A[a](0) * (f (method 0) + Ψ (method 0)) ≤
      a 0 *
          (f (method 0) +
            inner ℝ (gradientWithin f Q (method 0)) ((x : E) - method 0) +
            Ψ x) +
        linearOptimizationOracleErrorBound
          (initialLinearizationGap Q f Ψ method.x0) a Gν D ν 0 := by
  have ha0_nonneg : 0 ≤ a 0 := (ha_pos 0).le
  have hgap :=
    mul_le_mul_of_nonneg_left
      (oracle_objective_gap_le_initialLinearizationGap method x)
      ha0_nonneg
  -- Rewrite the base inequality into the scaled oracle-objective gap at `x₀`.
  rw [accumulatedWeights_apply]
  simp [LinearOracleCompositeMethod.iterates_zero, linearOptimizationOracleErrorBound_def]
  rw [linearOptimizationOracleObjective_apply, linearOptimizationOracleObjective_apply] at hgap
  simp [InnerProductSpace.toDualMap_apply] at hgap
  have hinner :
      inner ℝ (gradientWithin f Q method.x0) ((x : E) - method.x0) =
        inner ℝ (gradientWithin f Q method.x0) (x : E) -
          inner ℝ (gradientWithin f Q method.x0) method.x0 := by
    rw [inner_sub_right]
  -- Normalize the affine displacement at `x` and then close by linear arithmetic.
  rw [hinner]
  linarith

/-- Helper for Theorem 6.12: the affine model at `x_t` is controlled by the next affine model up
to the one-step Hölder increment. -/
lemma affine_model_le_next_affine_model_add_holder_increment
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (method : LinearOracleCompositeMethod Q f Ψ)
    (ν Gν D : ℝ)
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    f (method t) +
        inner ℝ (gradientWithin f Q (method t)) ((x : E) - method t) ≤
      f (method (t + 1)) +
        inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
        (Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν) := by
  let gNext := gradientWithin f Q (method (t + 1))
  let gCurr := gradientWithin f Q (method t)
  let delta :=
    (Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)
  have hτ_pos : 0 < method.stepSize t := (method.stepSize_mem_Ioc t).1
  have hτ_nonneg : 0 ≤ method.stepSize t := hτ_pos.le
  have hτ_le_one : method.stepSize t ≤ 1 := (method.stepSize_mem_Ioc t).2
  have h_one_sub_nonneg : 0 ≤ 1 - method.stepSize t := sub_nonneg.mpr hτ_le_one
  have hdiff :
      DifferentiableOn ℝ f Q :=
    fun y hy ↦ (method.hasGradientWithinAt ⟨y, hy⟩).differentiableWithinAt
  have hmono :=
    hf_convex.gradient_monotone hdiff
      (method.iterates_mem_feasibleSet (t + 1))
      (method.iterates_mem_feasibleSet t)
  have hstep_disp :
      ((method (t + 1) : E) - method t) =
        method.stepSize t • ((method.oraclePoint t : E) - method t) := by
    -- The iterate update isolates the scalar step size in front of the oracle displacement.
    calc
      ((method (t + 1) : E) - method t)
          = ((1 - method.stepSize t) • (method t : E) +
                method.stepSize t • (method.oraclePoint t : E)) -
              method t := by
                rw [LinearOracleCompositeMethod.iterates_succ]
      _ = method.stepSize t • ((method.oraclePoint t : E) - method t) := by
            simp [sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm,
              add_comm]
  have hmonotone_scaled :
      0 ≤ method.stepSize t * inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method t) := by
    -- Rewrite the displacement `x_{t+1} - x_t` using the explicit step formula.
    rw [hstep_disp] at hmono
    simpa [inner_smul_right] using hmono
  have hmonotone :
      0 ≤ inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method t) := by
    by_contra hneg
    have hneg_scaled :
        method.stepSize t * inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method t) < 0 := by
      exact mul_neg_of_pos_of_neg hτ_pos (lt_of_not_ge hneg)
    linarith
  have hholder_raw := h6043 t x
  have hholder :
      inner ℝ (gNext - gCurr) ((x : E) - method.oraclePoint t) ≥ -delta := by
    simpa [gNext, gCurr, delta] using hholder_raw
  have hstep :
      f (method (t + 1)) ≥
        f (method t) + inner ℝ gCurr ((method (t + 1) : E) - method t) := by
    -- The convex tangent plane at `x_t` lower-bounds the next iterate.
    exact
      hf_convex.lower_tangent_plane_of_hasGradientWithinAt
        (method t) (method.iterates_mem_feasibleSet t) gCurr
        (method.hasGradientWithinAt (method t))
        (method (t + 1)) (method.iterates_mem_feasibleSet (t + 1))
  have horacle_disp :
      ((method.oraclePoint t : E) - method (t + 1)) =
        (1 - method.stepSize t) • ((method.oraclePoint t : E) - method t) := by
    -- Comparing the oracle point with the next iterate isolates the residual `1 - τ_t`.
    calc
      ((method.oraclePoint t : E) - method (t + 1))
          = ((method.oraclePoint t : E) - method t) -
              ((method (t + 1) : E) - method t) := by
                abel_nf
      _ = ((method.oraclePoint t : E) - method t) -
            method.stepSize t • ((method.oraclePoint t : E) - method t) := by
              rw [hstep_disp]
      _ = (1 - method.stepSize t) • ((method.oraclePoint t : E) - method t) := by
            let d : E := (method.oraclePoint t : E) - method t
            show d - method.stepSize t • d = (1 - method.stepSize t) • d
            simpa using (sub_smul (1 : ℝ) (method.stepSize t) d).symm
  have hrewrite :
      (x : E) - method (t + 1) =
        ((x : E) - method.oraclePoint t) +
          (1 - method.stepSize t) • ((method.oraclePoint t : E) - method t) := by
    -- Split the displacement through the oracle point and then rewrite the remaining tail.
    calc
      (x : E) - method (t + 1)
          = ((x : E) - method.oraclePoint t) +
              ((method.oraclePoint t : E) - method (t + 1)) := by
                abel_nf
      _ = ((x : E) - method.oraclePoint t) +
            (1 - method.stepSize t) • ((method.oraclePoint t : E) - method t) := by
              rw [horacle_disp]
  have hpair :
      inner ℝ (gNext - gCurr) ((x : E) - method (t + 1)) ≥ -delta := by
    rw [hrewrite, inner_add_right, inner_smul_right]
    have hscaled_mono :
        0 ≤
          (1 - method.stepSize t) *
            inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method t) :=
      mul_nonneg h_one_sub_nonneg hmonotone
    linarith
  have hcurr :
      inner ℝ gCurr ((x : E) - method t) =
        inner ℝ gCurr ((x : E) - method (t + 1)) +
          inner ℝ gCurr ((method (t + 1) : E) - method t) := by
    calc
      inner ℝ gCurr ((x : E) - method t)
          = inner ℝ gCurr
              (((x : E) - method (t + 1)) + ((method (t + 1) : E) - method t)) := by
                congr 2
                abel_nf
      _ = inner ℝ gCurr ((x : E) - method (t + 1)) +
            inner ℝ gCurr ((method (t + 1) : E) - method t) := by
              rw [inner_add_right]
  have hpair' :
      inner ℝ gCurr ((x : E) - method (t + 1)) ≤
        inner ℝ gNext ((x : E) - method (t + 1)) + delta := by
    have hsub :
        inner ℝ (gNext - gCurr) ((x : E) - method (t + 1)) =
          inner ℝ gNext ((x : E) - method (t + 1)) -
            inner ℝ gCurr ((x : E) - method (t + 1)) := by
      rw [inner_sub_left]
    rw [hsub] at hpair
    linarith
  -- Route correction: rewrite the next affine model as the old one plus the gradient-difference
  -- pairing, and then control that pairing by `h6043` and gradient monotonicity.
  calc
    f (method t) + inner ℝ gCurr ((x : E) - method t)
        ≤ f (method (t + 1)) +
            inner ℝ gCurr ((x : E) - method (t + 1)) := by
              rw [hcurr]
              linarith
    _ ≤ f (method (t + 1)) +
          inner ℝ gNext ((x : E) - method (t + 1)) + delta := by
            linarith

/-- Helper for Theorem 6.12: the oracle term at time `t` can be rewritten directly in the affine
model at `x_{t+1}`, and the only loss is the single Hölder increment from `(6.4.3)`. -/
lemma oracle_point_term_le_next_affine_model_add_holder_increment
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (method : LinearOracleCompositeMethod Q f Ψ)
    (ν Gν D : ℝ)
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    f (method (t + 1)) +
        inner ℝ (gradientWithin f Q (method (t + 1)))
          ((method.oraclePoint t : E) - method (t + 1)) +
        Ψ (method.oraclePoint t) ≤
      f (method (t + 1)) +
        inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
        Ψ x +
        (Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν) := by
  let gCurr := gradientWithin f Q (method t)
  let gNext := gradientWithin f Q (method (t + 1))
  let delta := (Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)
  have horacle := method.oraclePoint_linearOptimizationOracleObjective_le t x
  rw [linearOptimizationOracleObjective_apply, linearOptimizationOracleObjective_apply] at horacle
  simp [InnerProductSpace.toDualMap_apply] at horacle
  have horacle_shift :
      inner ℝ gCurr ((method.oraclePoint t : E) - method (t + 1)) + Ψ (method.oraclePoint t) ≤
        inner ℝ gCurr ((x : E) - method (t + 1)) + Ψ x := by
    -- Translate the oracle inequality by the common base point `x_{t+1}`.
    rw [inner_sub_right, inner_sub_right]
    linarith
  have hholder := h6043 t x
  have hholder_shift :
      inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method (t + 1)) ≤
        inner ℝ (gNext - gCurr) ((x : E) - method (t + 1)) + delta := by
    -- The gradient-difference correction only pays the single `(6.4.3)` remainder.
    have hholder' :
        inner ℝ (gNext - gCurr) (method.oraclePoint t : E) ≤
          inner ℝ (gNext - gCurr) (x : E) + delta := by
      rw [inner_sub_right] at hholder
      simpa [gNext, gCurr, delta] using hholder
    rw [inner_sub_right, inner_sub_right]
    linarith
  have hgrad_split : gCurr + (gNext - gCurr) = gNext := by
    dsimp [gNext, gCurr]
    abel_nf
  have hleft :
      inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) =
        inner ℝ gCurr ((method.oraclePoint t : E) - method (t + 1)) +
          inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method (t + 1)) := by
    calc
      inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1))
          = inner ℝ (gCurr + (gNext - gCurr)) ((method.oraclePoint t : E) - method (t + 1)) := by
              rw [hgrad_split]
      _ = inner ℝ gCurr ((method.oraclePoint t : E) - method (t + 1)) +
            inner ℝ (gNext - gCurr) ((method.oraclePoint t : E) - method (t + 1)) := by
              rw [inner_add_left]
  have hright :
      inner ℝ gNext ((x : E) - method (t + 1)) =
        inner ℝ gCurr ((x : E) - method (t + 1)) +
          inner ℝ (gNext - gCurr) ((x : E) - method (t + 1)) := by
    calc
      inner ℝ gNext ((x : E) - method (t + 1))
          = inner ℝ (gCurr + (gNext - gCurr)) ((x : E) - method (t + 1)) := by
              rw [hgrad_split]
      _ = inner ℝ gCurr ((x : E) - method (t + 1)) +
            inner ℝ (gNext - gCurr) ((x : E) - method (t + 1)) := by
              rw [inner_add_left]
  -- Route correction: shift the gradient change inside the oracle comparison so the Hölder term
  -- is counted exactly once.
  rw [hleft, hright]
  linarith

/-- Helper for Theorem 6.12: the successor step first closes at the normalized scale `τ_t`,
before any `A_t`-rescaling. -/
lemma weighted_objective_step_normalized
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ_convex : ConvexOn ℝ Q (Function.extend Subtype.val Ψ 0))
    (method : LinearOracleCompositeMethod Q f Ψ)
    (ν Gν D : ℝ)
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    f (method (t + 1)) + Ψ (method (t + 1)) ≤
      (1 - method.stepSize t) * (f (method t) + Ψ (method t)) +
        method.stepSize t *
          (f (method (t + 1)) +
            inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
            Ψ x +
            (Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)) := by
  let τ := method.stepSize t
  let gNext := gradientWithin f Q (method (t + 1))
  let delta := (Real.rpow τ ν) * Gν * Real.rpow D (1 + ν)
  have hτ_pos : 0 < τ := (method.stepSize_mem_Ioc t).1
  have hτ_nonneg : 0 ≤ τ := hτ_pos.le
  have hτ_le_one : τ ≤ 1 := (method.stepSize_mem_Ioc t).2
  have h_one_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_le_one
  have hsum : (1 - τ) + τ = 1 := by
    dsimp [τ]
    ring
  have hΨ_raw :
      (Function.extend Subtype.val Ψ 0)
          ((1 - τ) • (method t : E) + τ • (method.oraclePoint t : E)) ≤
        (1 - τ) * (Function.extend Subtype.val Ψ 0) (method t : E) +
          τ * (Function.extend Subtype.val Ψ 0) (method.oraclePoint t : E) := by
    -- Convexity of the ambient extension gives the regularizer step at the natural `τ_t` scale.
    exact hΨ_convex.2 (method.iterates_mem_feasibleSet t) (method.oraclePoint_mem_feasibleSet t)
      h_one_sub_nonneg hτ_nonneg hsum
  have hΨ_step :
      Ψ (method (t + 1)) ≤
        (1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t) := by
    -- Rewrite the convexity bound back from the ambient extension to the subtype regularizer.
    have hiter :
        ((1 - τ) • (method t : E) + τ • (method.oraclePoint t : E)) =
          method (t + 1) := by
      simpa [τ] using (LinearOracleCompositeMethod.iterates_succ (method := method) t).symm
    rw [hiter, Function.extend_val_apply (method.iterates_mem_feasibleSet (t + 1)),
      Function.extend_val_apply (method.iterates_mem_feasibleSet t),
      Function.extend_val_apply (method.oraclePoint_mem_feasibleSet t)] at hΨ_raw
    simpa using hΨ_raw
  have htangent :
      f (method t) ≥
        f (method (t + 1)) +
          inner ℝ gNext ((method t : E) - method (t + 1)) := by
    -- Support the convex function `f` at the successor point `x_{t+1}`.
    exact
      hf_convex.lower_tangent_plane_of_hasGradientWithinAt
        (method (t + 1)) (method.iterates_mem_feasibleSet (t + 1)) gNext
        (method.hasGradientWithinAt (method (t + 1)))
        (method t) (method.iterates_mem_feasibleSet t)
  have horacle :=
    oracle_point_term_le_next_affine_model_add_holder_increment
      (method := method) (ν := ν) (Gν := Gν) (D := D) h6043 t x
  have horacle_scaled :
      τ *
          (f (method (t + 1)) +
            inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) +
            Ψ (method.oraclePoint t)) ≤
        τ *
          (f (method (t + 1)) +
            inner ℝ gNext ((x : E) - method (t + 1)) +
            Ψ x +
            delta) := by
    -- The oracle bridge is paid only once, then scaled by `τ_t`.
    simpa [τ, gNext, delta] using mul_le_mul_of_nonneg_left horacle hτ_nonneg
  let d : E := (method.oraclePoint t : E) - method t
  have hiter :
      (method (t + 1) : E) =
        (1 - τ) • (method t : E) + τ • (method.oraclePoint t : E) := by
    simpa [τ] using (LinearOracleCompositeMethod.iterates_succ (method := method) t)
  have hprev_disp :
      ((method t : E) - method (t + 1)) = -τ • d := by
    -- Rewrite the predecessor displacement using the explicit convex-combination step.
    rw [hiter]
    dsimp [d]
    simp [sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
  have horacle_disp :
      ((method.oraclePoint t : E) - method (t + 1)) = (1 - τ) • d := by
    -- The oracle-point displacement is the residual `(1 - τ_t)` fraction of the same direction.
    rw [hiter]
    dsimp [d]
    simp [sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
  have hcancel_vec :
      (1 - τ) • ((method t : E) - method (t + 1)) +
        τ • ((method.oraclePoint t : E) - method (t + 1)) = 0 := by
    -- The two displacement directions cancel because `x_{t+1}` is their `τ_t`-average.
    rw [hprev_disp, horacle_disp]
    calc
      (1 - τ) • (-τ • d) + τ • ((1 - τ) • d) =
          ((1 - τ) * (-τ) + τ * (1 - τ)) • d := by
            rw [smul_smul, smul_smul, add_smul]
      _ = (0 : ℝ) • d := by
            have hcoeff : ((1 - τ) * (-τ) + τ * (1 - τ) : ℝ) = 0 := by ring
            rw [hcoeff]
      _ = 0 := by simp
  have hcancel :
      (1 - τ) * inner ℝ gNext ((method t : E) - method (t + 1)) +
        τ * inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) = 0 := by
    -- Push the cancellation through the inner product to remove the intermediate oracle point.
    have hcancel_inner := congrArg (fun z : E ↦ inner ℝ gNext z) hcancel_vec
    simpa [inner_add_right, inner_smul_right] using hcancel_inner
  have hsplit :
      f (method (t + 1)) =
        (1 - τ) *
            (f (method (t + 1)) +
              inner ℝ gNext ((method t : E) - method (t + 1))) +
          τ *
            (f (method (t + 1)) +
              inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1))) := by
    -- Rewrite `f(x_{t+1})` into the two weighted pieces whose pairings cancel exactly.
    linarith
  have hprev_scaled :
      (1 - τ) *
          (f (method (t + 1)) +
            inner ℝ gNext ((method t : E) - method (t + 1)) +
            Ψ (method t)) ≤
        (1 - τ) * (f (method t) + Ψ (method t)) := by
    -- The previous iterate contribution is controlled by the tangent plane at `x_{t+1}`.
    have hprev :
        f (method (t + 1)) +
            inner ℝ gNext ((method t : E) - method (t + 1)) +
            Ψ (method t) ≤
          f (method t) + Ψ (method t) := by
      linarith
    exact mul_le_mul_of_nonneg_left hprev h_one_sub_nonneg
  have hnormalized :
      f (method (t + 1)) + Ψ (method (t + 1)) ≤
        (1 - τ) *
            (f (method (t + 1)) +
              inner ℝ gNext ((method t : E) - method (t + 1)) +
              Ψ (method t)) +
          τ *
            (f (method (t + 1)) +
              inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) +
              Ψ (method.oraclePoint t)) := by
    -- First combine convexity of `Ψ` with the exact decomposition of `f(x_{t+1})`.
    calc
      f (method (t + 1)) + Ψ (method (t + 1)) ≤
          f (method (t + 1)) +
            ((1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t)) := by
              linarith
      _ =
          ((1 - τ) *
              (f (method (t + 1)) +
                inner ℝ gNext ((method t : E) - method (t + 1))) +
            τ *
              (f (method (t + 1)) +
                inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)))) +
            ((1 - τ) * Ψ (method t) + τ * Ψ (method.oraclePoint t)) := by
              nth_rw 1 [hsplit]
      _ =
          (1 - τ) *
              (f (method (t + 1)) +
                inner ℝ gNext ((method t : E) - method (t + 1)) +
                Ψ (method t)) +
            τ *
              (f (method (t + 1)) +
                inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) +
                Ψ (method.oraclePoint t)) := by
              ring
  -- Route correction: close the normalized step before touching the `A_t`-rescaling algebra.
  calc
    f (method (t + 1)) + Ψ (method (t + 1)) ≤
        (1 - τ) *
            (f (method (t + 1)) +
              inner ℝ gNext ((method t : E) - method (t + 1)) +
              Ψ (method t)) +
          τ *
            (f (method (t + 1)) +
              inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) +
              Ψ (method.oraclePoint t)) := hnormalized
    _ ≤ (1 - τ) * (f (method t) + Ψ (method t)) +
          τ *
            (f (method (t + 1)) +
              inner ℝ gNext ((method.oraclePoint t : E) - method (t + 1)) +
              Ψ (method.oraclePoint t)) := by
            linarith
    _ ≤ (1 - τ) * (f (method t) + Ψ (method t)) +
          τ *
            (f (method (t + 1)) +
              inner ℝ gNext ((x : E) - method (t + 1)) +
              Ψ x +
              delta) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left horacle_scaled ((1 - τ) * (f (method t) + Ψ (method t)))
    _ = (1 - method.stepSize t) * (f (method t) + Ψ (method t)) +
          method.stepSize t *
            (f (method (t + 1)) +
              inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
              Ψ x +
              (Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)) := by
            rfl

/-- Helper for Theorem 6.12: multiplying the normalized convex combination by `A_{t+1}` yields
the successor weighted average identity. -/
lemma successor_weighted_average_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t)
    (t : ℕ) (u v : ℝ) :
    accumulatedWeights a (t + 1) *
        ((1 - weightCoefficient a t) * u + weightCoefficient a t * v) =
      accumulatedWeights a t * u + a (t + 1) * v := by
  have hA_ne : accumulatedWeights a (t + 1) ≠ 0 :=
    (accumulatedWeights_pos a ha_pos (t + 1)).ne'
  -- Rewrite `τ_t` as `a_{t+1} / A_{t+1}` and clear the single denominator.
  rw [weightCoefficient_apply]
  field_simp [hA_ne]
  rw [accumulatedWeights_succ]
  ring

/-- Helper for Theorem 6.12: the weighted Hölder remainder rescales from `τ_t^(1 + ν)` to the
displayed Chapter 6 increment written with `a_{t+1}` and `A_{t+1}`. -/
lemma weight_coefficient_holder_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t)
    (ν Gν D : ℝ) (t : ℕ) :
    accumulatedWeights a (t + 1) *
        (weightCoefficient a t *
          ((Real.rpow (weightCoefficient a t) ν) * Gν * Real.rpow D (1 + ν))) =
      (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
        Gν * Real.rpow D (1 + ν) := by
  have ha_nonneg : 0 ≤ a (t + 1) := (ha_pos (t + 1)).le
  have hA_pos : 0 < accumulatedWeights a (t + 1) := accumulatedWeights_pos a ha_pos (t + 1)
  have hA_nonneg : 0 ≤ accumulatedWeights a (t + 1) := hA_pos.le
  have hA_rpow_ne : Real.rpow (accumulatedWeights a (t + 1)) ν ≠ 0 :=
    (Real.rpow_pos_of_pos hA_pos ν).ne'
  have hτ_pos : 0 < weightCoefficient a t := by
    rw [weightCoefficient_apply]
    exact div_pos (ha_pos (t + 1)) hA_pos
  have hτ_pow :
      weightCoefficient a t * Real.rpow (weightCoefficient a t) ν =
        Real.rpow (weightCoefficient a t) (1 + ν) := by
    -- Merge the linear `τ_t` factor with `τ_t^ν` before replacing `τ_t`.
    simpa [Real.rpow_one] using (Real.rpow_add hτ_pos 1 ν).symm
  have hA_pow :
      Real.rpow (accumulatedWeights a (t + 1)) (1 + ν) =
        accumulatedWeights a (t + 1) * Real.rpow (accumulatedWeights a (t + 1)) ν := by
    -- Factor the positive power `A_{t+1}^{1 + ν}` into `A_{t+1} * A_{t+1}^ν`.
    simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using
      (Real.rpow_add hA_pos 1 ν)
  have hdiv :
      Real.rpow (a (t + 1) / accumulatedWeights a (t + 1)) (1 + ν) =
        Real.rpow (a (t + 1)) (1 + ν) /
          Real.rpow (accumulatedWeights a (t + 1)) (1 + ν) := by
    simpa using Real.div_rpow ha_nonneg hA_nonneg (1 + ν)
  -- Convert the `τ_t`-version of the Hölder term into the textbook `a_{t+1}` / `A_{t+1}` form.
  calc
    accumulatedWeights a (t + 1) *
        (weightCoefficient a t *
          ((Real.rpow (weightCoefficient a t) ν) * Gν * Real.rpow D (1 + ν))) =
      accumulatedWeights a (t + 1) *
        (Real.rpow (weightCoefficient a t) (1 + ν) * Gν * Real.rpow D (1 + ν)) := by
          rw [← hτ_pow]
          ring
    _ =
      accumulatedWeights a (t + 1) *
        ((Real.rpow (a (t + 1)) (1 + ν) /
            Real.rpow (accumulatedWeights a (t + 1)) (1 + ν)) *
          Gν * Real.rpow D (1 + ν)) := by
            rw [weightCoefficient_apply, hdiv]
    _ =
      accumulatedWeights a (t + 1) *
        ((Real.rpow (a (t + 1)) (1 + ν) /
            (accumulatedWeights a (t + 1) * Real.rpow (accumulatedWeights a (t + 1)) ν)) *
          Gν * Real.rpow D (1 + ν)) := by
            rw [hA_pow]
    _ =
      (Real.rpow (a (t + 1)) (1 + ν) /
          Real.rpow (accumulatedWeights a (t + 1)) ν) *
        Gν * Real.rpow D (1 + ν) := by
          field_simp [hA_pos.ne', hA_rpow_ne]

/-- Helper for Theorem 6.12: one step of method `(6.4.12)` satisfies the weighted affine-model
estimate whose error is exactly the new Chapter 6 increment, already written with the successor
affine model at `x_{t+1}`. -/
lemma weighted_objective_step_bound
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ_convex : ConvexOn ℝ Q (Function.extend Subtype.val Ψ 0))
    (method : LinearOracleCompositeMethod Q f Ψ)
    (a : ℕ → ℝ) (ν Gν D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    accumulatedWeights a (t + 1) * (f (method (t + 1)) + Ψ (method (t + 1))) ≤
      A[a](t) * (f (method t) + Ψ (method t)) +
        a (t + 1) *
          (f (method (t + 1)) +
            inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
            Ψ x) +
        (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
          Gν * Real.rpow D (1 + ν) := by
  let u := f (method t) + Ψ (method t)
  let v :=
    f (method (t + 1)) +
      inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
      Ψ x
  let delta :=
    (Real.rpow (τ[a](t)) ν) * Gν * Real.rpow D (1 + ν)
  have hA_pos : 0 < accumulatedWeights a (t + 1) := accumulatedWeights_pos a ha_pos (t + 1)
  have hA_nonneg : 0 ≤ accumulatedWeights a (t + 1) := hA_pos.le
  have hnormalized :=
    weighted_objective_step_normalized
      (hf_convex := hf_convex) (hΨ_convex := hΨ_convex)
      (method := method) (ν := ν) (Gν := Gν) (D := D) h6043 t x
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hA_nonneg
  -- Rewrite the scaled normalized step using the explicit coefficient `τ[a](t)`.
  rw [h_step t] at hscaled
  have hsplit :
      accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * (v + delta)) =
        accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * v) +
          accumulatedWeights a (t + 1) * (τ[a](t) * delta) := by
    -- Separate the affine contribution from the single Hölder remainder before rescaling.
    ring
  rw [show f (method t) + Ψ (method t) = u by rfl,
    show
      f (method (t + 1)) +
          inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
          Ψ x +
          (Real.rpow (τ[a](t)) ν) * Gν * Real.rpow D (1 + ν) =
        v + delta by rfl] at hscaled
  rw [hsplit] at hscaled
  rw [successor_weighted_average_rescaling (a := a) ha_pos t u v,
    weight_coefficient_holder_rescaling (a := a) ha_pos ν Gν D t] at hscaled
  simpa [u, v, delta]
    using hscaled
/-- Theorem 6.12: along method `(6.4.12)`, if `f` is convex on `Q`, the canonical ambient
extension of the regularizer `Ψ` is convex on `Q`, the coefficients satisfy
`A_t = ∑_{k=0}^t a_k` and `τ_t = a_{t+1} / A_{t+1}`, and the `(6.4.3)` Hölder-gradient error term
is bounded by `G_ν D^(1 + ν)`, then for every iteration `t` and feasible point `x` the weighted
composite objective at `x_t` is bounded by the sum of the affine linearizations at `x` plus the
Chapter 6 error term `linearOptimizationOracleErrorBound V₀ a G_ν D ν t`, where
`V₀ = initialLinearizationGap Q f Ψ x₀` and `x₀ = method.x0`. -/
theorem weighted_objective_upper_bound_of_linear_oracle_composite_method
    {Q : Set E} {f : E → ℝ} {Ψ : Q → ℝ}
    (hf_convex : ConvexOn ℝ Q f)
    (hΨ_convex : ConvexOn ℝ Q (Function.extend Subtype.val Ψ 0))
    (method : LinearOracleCompositeMethod Q f Ψ)
    (a : ℕ → ℝ) (ν Gν D : ℝ)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (h6043 :
      ∀ t : ℕ, ∀ x : Q,
        inner ℝ
            (gradientWithin f Q (method (t + 1)) - gradientWithin f Q (method t))
            ((x : E) - method.oraclePoint t) ≥
          -((Real.rpow (method.stepSize t) ν) * Gν * Real.rpow D (1 + ν)))
    (t : ℕ) (x : Q) :
    A[a](t) * (f (method t) + Ψ (method t)) ≤
      (Finset.sum (Finset.range (t + 1)) fun k ↦
        a k *
          (f (method k) +
            inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
            Ψ x)) +
        linearOptimizationOracleErrorBound
          (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t := by
  induction t with
  | zero =>
      -- The initial stage is exactly the starting oracle-gap estimate packaged above.
      simpa using
        weighted_objective_upper_bound_base_case
          (method := method) (a := a) (ν := ν) (Gν := Gν) (D := D) ha_pos x
  | succ t ih =>
      have hstep :=
        weighted_objective_step_bound
          (hf_convex := hf_convex) (hΨ_convex := hΨ_convex)
          (method := method) (a := a) (ν := ν) (Gν := Gν) (D := D)
          (ha_pos := ha_pos) (h_step := h_step) h6043 t x
      have hcombine :
          A[a](t) * (f (method t) + Ψ (method t)) +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
                Gν * Real.rpow D (1 + ν) ≤
            (Finset.sum (Finset.range (t + 1)) fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)) +
              linearOptimizationOracleErrorBound
                (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
                Gν * Real.rpow D (1 + ν) := by
        -- Add the induction hypothesis to the successor affine term and the new error increment.
        linarith
      calc
        accumulatedWeights a (t + 1) * (f (method (t + 1)) + Ψ (method (t + 1))) ≤
            accumulatedWeights a t * (f (method t) + Ψ (method t)) +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
                Gν * Real.rpow D (1 + ν) := hstep
        _ ≤
            (Finset.sum (Finset.range (t + 1)) fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)) +
              linearOptimizationOracleErrorBound
                (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t +
              a (t + 1) *
                (f (method (t + 1)) +
                  inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                  Ψ x) +
              (Real.rpow (a (t + 1)) (1 + ν) / Real.rpow (accumulatedWeights a (t + 1)) ν) *
                Gν * Real.rpow D (1 + ν) := hcombine
        _ =
            (Finset.sum (Finset.range ((t + 1) + 1)) fun k ↦
                a k *
                  (f (method k) +
                    inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                    Ψ x)) +
              linearOptimizationOracleErrorBound
                (initialLinearizationGap Q f Ψ method.x0) a Gν D ν (t + 1) := by
              have hsum_succ :
                  (Finset.sum (Finset.range (t + 1)) fun k ↦
                      a k *
                        (f (method k) +
                          inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                          Ψ x)) +
                    a (t + 1) *
                      (f (method (t + 1)) +
                        inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                        Ψ x) =
                    Finset.sum (Finset.range ((t + 1) + 1)) fun k ↦
                      a k *
                        (f (method k) +
                          inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                          Ψ x) := by
                simp [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]
              calc
                (Finset.sum (Finset.range (t + 1)) fun k ↦
                    a k *
                      (f (method k) +
                        inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                        Ψ x)) +
                  linearOptimizationOracleErrorBound
                    (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t +
                  a (t + 1) *
                    (f (method (t + 1)) +
                      inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                      Ψ x) +
                  (Real.rpow (a (t + 1)) (1 + ν) /
                      Real.rpow (accumulatedWeights a (t + 1)) ν) *
                    Gν * Real.rpow D (1 + ν) =
                  ((Finset.sum (Finset.range (t + 1)) fun k ↦
                      a k *
                        (f (method k) +
                          inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                          Ψ x)) +
                    a (t + 1) *
                      (f (method (t + 1)) +
                        inner ℝ (gradientWithin f Q (method (t + 1))) ((x : E) - method (t + 1)) +
                        Ψ x)) +
                  (linearOptimizationOracleErrorBound
                    (initialLinearizationGap Q f Ψ method.x0) a Gν D ν t +
                    (Real.rpow (a (t + 1)) (1 + ν) /
                        Real.rpow (accumulatedWeights a (t + 1)) ν) *
                      Gν * Real.rpow D (1 + ν)) := by
                        ac_rfl
                _ =
                  (Finset.sum (Finset.range ((t + 1) + 1)) fun k ↦
                      a k *
                        (f (method k) +
                          inner ℝ (gradientWithin f Q (method k)) ((x : E) - method k) +
                          Ψ x)) +
                    linearOptimizationOracleErrorBound
                      (initialLinearizationGap Q f Ψ method.x0) a Gν D ν (t + 1) := by
                        rw [hsum_succ, linearOptimizationOracleErrorBound_succ]
