/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "PosMat" => { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G }
local notation "ConstraintVec" => { d : E // d ≠ 0 }

/- Theorem 7.11 lies in the chapter's relative-scale minimax / recursive outer-iterate /
first-stopping-time domain.

Sampled owner-style declarations:
- `iterativeSmoothingParameter`, `iterativeSmoothingStoppingTime`, and
  `iterativeSmoothingOutputPoint` in `Algorithm_7_9.lean`;
- `iterativeSmoothingBlockLength` in `Algorithm_7_9.lean`, the canonical owner of the per-stage
  lower-level work budget;
- `relativeScaleSubgradientApproximationTotalLowerLevelSteps` in `Theorem_7_3.lean` and
  `schemeSNRestartingTotalLowerLevelSteps` in `Theorem_7_5.lean`, the nearby chapter pattern for
  deriving total lower-level work from canonical stopping data;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for the terminal relative
  accuracy conclusion.

Best owner abstraction:
- source-facing: Theorem 7.11's stopping-time, terminal-value, and total-work bounds for the
  Algorithm 7.9 relative-scale scheme;
- core/canonical: the Algorithm 7.9 owners
  `xHat : ℕ → E`, `iterativeSmoothingParameter a δ`,
  `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`,
  `iterativeSmoothingStoppingTime hTerminate`, and
  `iterativeSmoothingBlockLength (m : ℕ) n δ γ`;
- bridge/view: the derived total lower-level work
  `iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate`.

Primitive data:
- the lower-level subroutine `S`, the family `a`, and the geometric data `d : ConstraintVec`
  and `G`;
- an explicit Algorithm 7.9 outer iterate `xHat` together with the auxiliary hypotheses that it
  starts at `x₀`, has positive stagewise smoothing parameters, and satisfies the recursive update
  rule;
- the termination witness `hTerminate` for the canonical first accepted outer stage;
- the feasible-set lower bound and the feasibility of the generated canonical orbit.

Derived API:
- the recursive orbit `x̂_t`;
- the smoothing parameter at stage `t`, namely
  `iterativeSmoothingParameter a δ (xHat t)`;
- the textbook stopping time `T`;
- the accepted output point `\hat x_T`;
- the total lower-level work up to `T`;
- the helper-level initial-value and terminal-relative-gap bridges used in the proof route.

Source/core/bridge triage:
- source-facing: the three bounds asserted by Theorem 7.11;
- core/canonical: the Algorithm 7.9 iterate, smoothing, stopping-time, and output owners;
- bridge/view: the total-work product `T * \tilde N`.

This file now uses the refined source-facing owner directly: the explicit outer iterate `xHat`,
with the stagewise positivity and recursive update information kept as ordinary hypotheses rather
than hidden behind a typeclass wrapper, together with the canonical stopping-time API derived from
that iterate.
-/

/-- The total number of lower-level steps used by Algorithm 7.9 up to its canonical stopping
time, assuming that each outer stage uses the canonical block length
`iterativeSmoothingBlockLength (m : ℕ) n δ γ`. -/
def iterativeSmoothingTotalLowerLevelSteps
    (δ γ : ℝ) {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) : ℕ :=
  iterativeSmoothingStoppingTime hTerminate *
    iterativeSmoothingBlockLength (m : ℕ) n δ γ

/-- Expanding `iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate` gives the product of the
canonical stopping time and the canonical block length. -/
theorem iterativeSmoothingTotalLowerLevelSteps_def
    (δ γ : ℝ) {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate =
      iterativeSmoothingStoppingTime hTerminate *
        iterativeSmoothingBlockLength (m : ℕ) n δ γ :=
  rfl

section Complexity

variable
  {S : (E → ℝ) → ℝ → Set E → PosMat → E → ℕ → E}
  {a : Fin (m : ℕ) → E} {d : ConstraintVec} {G : PosMat}
  {δ γ fStar : ℝ} {feasibleSet : Set E} {xHat : ℕ → E}

variable
  (hZero : xHat 0 = iterativeSmoothingInitialPoint d G)
  (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
  (hSucc :
    ∀ t : ℕ,
      xHat (t + 1) =
        iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t))

variable (hTerminate : iterativeSmoothingTerminates a xHat)

local notation "x̂" => xHat
local notation "F" => maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
local notation "s" => iterativeSmoothingStoppingIndex hTerminate
local notation "T" => iterativeSmoothingStoppingTime hTerminate
local notation "x̂T" => iterativeSmoothingOutputPoint hTerminate

/-- Helper for Theorem 7.11: every value of the max-type objective along the iterative-smoothing
orbit is nonnegative. -/
lemma iterativeSmoothing_objective_nonneg (t : ℕ) :
    0 ≤ F (x̂ t) := by
  -- Compare the objective with any concrete absolute-value component.
  rw [maxTypeObjective_apply]
  exact
    (abs_nonneg (inner ℝ (a 0) (x̂ t))).trans
      (Finset.le_sup' (fun i : Fin (m : ℕ) ↦ |inner ℝ (a i) (x̂ t)|) (Finset.mem_univ 0))

/-- Helper for Theorem 7.11: stagewise positivity of the smoothing parameter forces the initial
max-type objective value to be strictly positive. -/
lemma iterativeSmoothing_initial_objective_pos_of_parameter_pos
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (x̂ t)) :
    0 < F (x̂ 0) := by
  -- If the initial objective vanished, the defining formula would give `μ₀ = 0`.
  have hobjective_ne_zero : F (x̂ 0) ≠ 0 := by
    intro hobjective_zero
    have hparameter_zero : iterativeSmoothingParameter a δ (x̂ 0) = 0 := by
      rw [iterativeSmoothingParameter_eq]
      simp [hobjective_zero]
    exact (ne_of_gt (hParameterPos 0)) hparameter_zero
  -- Nonnegativity then upgrades nonvanishing to strict positivity.
  exact
    lt_of_le_of_ne (iterativeSmoothing_objective_nonneg 0)
      (by simpa [eq_comm] using hobjective_ne_zero)

/-- Helper for Theorem 7.11: before the first accepted stage, the objective decays geometrically
with the canonical factor `1 / e`. -/
lemma iterativeSmoothing_preterminal_objective_le_exp_neg_mul_initial :
    ∀ {t : ℕ}, t ≤ s → F (x̂ t) ≤ Real.exp (-(t : ℝ)) * F (x̂ 0)
  | 0, _ => by
      -- The envelope is exact at the initial stage.
      simp
  | t + 1, ht => by
      -- The minimality of the stopping index gives one more contraction step.
      have ht_lt : t < s := Nat.lt_of_succ_le ht
      have hstep :
          F (x̂ (t + 1)) ≤ iterativeSmoothingStoppingFactor * F (x̂ t) :=
        (iterativeSmoothingStoppingIndex_min hTerminate ht_lt).le
      -- The induction hypothesis controls the previous stage.
      have hprev :
          F (x̂ t) ≤ Real.exp (-(t : ℝ)) * F (x̂ 0) :=
        iterativeSmoothing_preterminal_objective_le_exp_neg_mul_initial
          (Nat.le_of_lt_succ ht)
      have hscaled :
          iterativeSmoothingStoppingFactor * F (x̂ t) ≤
            iterativeSmoothingStoppingFactor * (Real.exp (-(t : ℝ)) * F (x̂ 0)) := by
        exact
          mul_le_mul_of_nonneg_left hprev (by
            rw [iterativeSmoothingStoppingFactor_def]
            positivity)
      refine hstep.trans ?_
      calc
        iterativeSmoothingStoppingFactor * (Real.exp (-(t : ℝ)) * F (x̂ 0))
            = (Real.exp (-1) * Real.exp (-(t : ℝ))) * F (x̂ 0) := by
                simp [iterativeSmoothingStoppingFactor_def, div_eq_mul_inv, Real.exp_neg,
                  mul_assoc]
        _ = Real.exp ((-1 : ℝ) + -(t : ℝ)) * F (x̂ 0) := by
              rw [← Real.exp_add]
        _ = Real.exp (-((t + 1 : ℕ) : ℝ)) * F (x̂ 0) := by
              congr 1
              norm_num [Nat.cast_add]

/-- Helper for Theorem 7.11: the canonical block length is bounded above by its unfloored real
expression in the positive-parameter regime. -/
lemma iterativeSmoothingBlockLength_le_unfloored
    (hδ : 0 < δ) (hScale_pos : 0 < γ * Real.sqrt (n : ℝ)) :
    (iterativeSmoothingBlockLength (m : ℕ) n δ γ : ℝ) ≤
      2 * Real.exp 1 * γ *
        Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) := by
  -- The scale hypothesis forces `γ` to be positive because the square-root factor is nonnegative.
  have hγ_pos : 0 < γ := by
    by_contra hγ_nonpos
    have hγ_nonpos' : γ ≤ 0 := le_of_not_gt hγ_nonpos
    have hprod_nonpos : γ * Real.sqrt (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hγ_nonpos' (Real.sqrt_nonneg _)
    linarith
  -- The logarithmic factor is positive since `m ≥ 1`.
  have hm_one_le : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt m.pos)
  have hlog_pos : 0 < Real.log (2 * (m : ℝ)) := by
    refine Real.log_pos ?_
    nlinarith
  have hsqrt_arg_nonneg :
      0 ≤ 2 * (n : ℝ) * Real.log (2 * (m : ℝ)) := by
    exact mul_nonneg (by positivity) hlog_pos.le
  have hone_add_inv_pos : 0 < 1 + 1 / δ := by
    have hinv_pos : 0 < 1 / δ := one_div_pos.mpr hδ
    linarith
  have hexpr_nonneg :
      0 ≤ 2 * Real.exp 1 * γ *
        Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) := by
    refine mul_nonneg ?_ hone_add_inv_pos.le
    exact mul_nonneg (mul_nonneg (by positivity) hγ_pos.le) (Real.sqrt_nonneg _)
  -- `Nat.floor` is always bounded above by the real it floors.
  simpa [iterativeSmoothingBlockLength_def] using Nat.floor_le hexpr_nonneg

-- Proof sketch: for every `t < iterativeSmoothingStoppingIndex hTerminate`,
-- `iterativeSmoothingStoppingIndex_min hTerminate` gives
-- `F (x̂ (t + 1)) < (1 / e) * F (x̂ t)`, so the canonical orbit decays geometrically before the
-- accepted stage. Compare the feasible preterminal iterate `x̂ s` with `fStar`, combine this with
-- the initial estimate `F (x̂ 0) ≤ γ √n fStar`, and obtain
-- `(T : ℝ) ≤ 1 + log (γ √n)`.
--
-- Route correction: the source-faithful proof needs stagewise positivity of the smoothing
-- parameter in order to rule out `F (x̂ 0) = 0`. The public stopping-time and total-work bounds
-- therefore keep that ambient hypothesis explicit, and the helper below records the core route.
/-- Helper for Theorem 7.11: once the initial objective is known to be positive, the source
stopping-time argument yields the logarithmic bound. -/
lemma iterativeSmoothing_stoppingTime_le_of_initial_objective_pos
    (hInitial_objective_pos : 0 < F (x̂ 0))
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ x : E, x ∈ feasibleSet → fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (T : ℝ) ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := by
  -- The initial upper bound and positive scale force the optimal value to be positive.
  have hfStar_pos : 0 < fStar := by
    have hprod_pos : 0 < γ * Real.sqrt (n : ℝ) * fStar :=
      lt_of_lt_of_le hInitial_objective_pos hInitial_value_le
    have hprod_pos' : 0 < fStar * (γ * Real.sqrt (n : ℝ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hprod_pos
    exact pos_of_mul_pos_left hprod_pos' hScale_pos.le
  -- Compare the feasible preterminal objective with the exponential envelope.
  have hs_ge : fStar ≤ F (x̂ s) :=
    hOptimal_value_le_of_feasible (x̂ s) hPreterminal_feasible
  have hs_decay :
      F (x̂ s) ≤ Real.exp (-(s : ℝ)) * F (x̂ 0) :=
    iterativeSmoothing_preterminal_objective_le_exp_neg_mul_initial le_rfl
  have hs_scaled :
      F (x̂ s) ≤ Real.exp (-(s : ℝ)) * (γ * Real.sqrt (n : ℝ) * fStar) := by
    refine hs_decay.trans ?_
    have hmul :=
      mul_le_mul_of_nonneg_left hInitial_value_le (Real.exp_nonneg (-(s : ℝ)))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hfStar_le_scaled :
      fStar ≤ Real.exp (-(s : ℝ)) * (γ * Real.sqrt (n : ℝ) * fStar) :=
    hs_ge.trans hs_scaled
  -- Multiply by `exp s` to cancel the decay factor and recover the logarithmic argument.
  have hscaled_by_exp :
      Real.exp (s : ℝ) * fStar ≤
        γ * Real.sqrt (n : ℝ) * fStar := by
    have hmul :=
      mul_le_mul_of_nonneg_left hfStar_le_scaled (Real.exp_nonneg (s : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm, ← Real.exp_add] using hmul
  have hexp_le :
      Real.exp (s : ℝ) ≤ γ * Real.sqrt (n : ℝ) := by
    exact le_of_mul_le_mul_right hscaled_by_exp hfStar_pos
  have hs_le_log :
      (s : ℝ) ≤ Real.log (γ * Real.sqrt (n : ℝ)) :=
    (Real.le_log_iff_exp_le hScale_pos).2 hexp_le
  -- Finally use `T = s + 1`.
  calc
    (T : ℝ) = (s : ℝ) + 1 := by
      simp [iterativeSmoothingStoppingTime]
    _ ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := by
      linarith [hs_le_log]

/-- Helper for Theorem 7.11: with explicit stagewise parameter positivity, the stopping time is
bounded by `1 + log (γ √n)`. -/
lemma iterativeSmoothing_stoppingTime_le_of_parameter_pos
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ x : E, x ∈ feasibleSet → fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (T : ℝ) ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := by
  -- The stagewise parameter positivity supplies the positive initial objective required by the
  -- source-faithful logarithmic estimate.
  have hInitial_objective_pos :
      0 < F (x̂ 0) :=
    iterativeSmoothing_initial_objective_pos_of_parameter_pos hParameterPos
  exact
    iterativeSmoothing_stoppingTime_le_of_initial_objective_pos
      hInitial_objective_pos hScale_pos hPreterminal_feasible hOptimal_value_le_of_feasible
      hInitial_value_le

/-- Theorem 7.11 (1): if the generated points are feasible, feasible points have value at least
`f*`, the initial value satisfies `f(\hat x_0) ≤ γ √n f*`, and the stagewise smoothing
parameters are positive, then the stopping time is bounded by `1 + log (γ √n)` once the scale
parameter is positive. -/
theorem iterativeSmoothing_stoppingTime_le
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ x : E, x ∈ feasibleSet → fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (T : ℝ) ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := by
  -- The public theorem only needs the preterminal feasibility hypothesis required by the helper.
  have hPreterminal_feasible : x̂ s ∈ feasibleSet :=
    hGenerated_feasible s
  -- Reuse the source-faithful logarithmic stopping-time estimate proved above.
  exact
    iterativeSmoothing_stoppingTime_le_of_parameter_pos
      hParameterPos hScale_pos hPreterminal_feasible hOptimal_value_le_of_feasible
      hInitial_value_le

-- Semantic search did not reveal a reusable mathlib rearrangement for this chapter-specific
-- terminal relative-gap inequality, so the algebraic bridge stays local.
-- Proof sketch: multiply the terminal relative-gap estimate by `1 + δ`, use `0 < 1 + δ`, and
-- rearrange the resulting linear inequality to isolate `F x̂T`.
/-- Helper for Theorem 7.11: a terminal relative-gap inequality implies the corresponding
`(1 + δ) f*` upper bound. -/
lemma iterativeSmoothing_outputPoint_value_le_of_relative_gap
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      F x̂T - fStar ≤ (δ / (1 + δ)) * F x̂T) :
    F x̂T ≤ (1 + δ) * fStar := by
  have hOne_add_δ : 0 < 1 + δ := by
    linarith
  -- Clear the denominator in the relative-gap inequality.
  have hMul :
      (F x̂T - fStar) * (1 + δ) ≤ δ * F x̂T := by
    have hScaled :=
      mul_le_mul_of_nonneg_right hTerminal_relative_gap hOne_add_δ.le
    have hOne_add_δ_ne : (1 + δ) ≠ 0 := ne_of_gt hOne_add_δ
    simpa [div_eq_mul_inv, hOne_add_δ_ne, mul_assoc, mul_left_comm, mul_comm] using hScaled
  -- The remaining step is a linear rearrangement.
  nlinarith [hMul]

-- Proof sketch: apply the accepted-stage relative-gap guarantee at the first accepted stage `s`,
-- then rewrite the resulting step output as the canonical output point `x̂T` via the recursive
-- equation.
/-- Helper for Theorem 7.11: an accepted-stage relative-gap estimate on each canonical step
output specializes to the canonical output point `\hat x_T`. -/
lemma iterativeSmoothing_outputPoint_relative_gap_of_stopping_rule
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (hSucc :
      ∀ t : ℕ,
        xHat (t + 1) =
          iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t))
    (hAcceptedStageRelativeGap :
      ∀ t : ℕ,
        iterativeSmoothingStoppingCriterion a xHat t →
          F (iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t)) - fStar ≤
            (δ / (1 + δ)) *
              F (iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t))) :
    F x̂T - fStar ≤ (δ / (1 + δ)) * F x̂T := by
  -- The first accepted stage satisfies the canonical stopping predicate by construction.
  have hsStop : iterativeSmoothingStoppingCriterion a xHat s := by
    simpa [s, iterativeSmoothingStoppingCriterion] using
      iterativeSmoothingStoppingIndex_spec hTerminate
  -- Specialize the stagewise relative-gap estimate at the first accepted stage.
  have hsGap :
      F (iterativeSmoothingStep S a d G δ γ (xHat s) (hParameterPos s)) - fStar ≤
        (δ / (1 + δ)) *
          F (iterativeSmoothingStep S a d G δ γ (xHat s) (hParameterPos s)) :=
    hAcceptedStageRelativeGap s hsStop
  -- Route correction: rewrite the accepted-stage output `xHat (s + 1)` as the canonical output
  -- point `x̂T` before applying the stagewise estimate.
  have hStep_eq_output :
      iterativeSmoothingStep S a d G δ γ (xHat s) (hParameterPos s) = x̂T := by
    calc
      iterativeSmoothingStep S a d G δ γ (xHat s) (hParameterPos s) = xHat (s + 1) := by
        symm
        exact hSucc s
      _ = x̂T := by
        simp [iterativeSmoothingOutputPoint_eq, iterativeSmoothingStoppingTime, s, T]
  -- Normalize the stagewise estimate to the public output-point formulation.
  simpa [hStep_eq_output] using hsGap

/-- Theorem 7.11 (2): if `δ > 0` and the terminal relative-gap estimate from the stopping-rule
analysis holds at `\hat x_T`, then the accepted output point satisfies
`f(\hat x_T) ≤ (1 + δ) f*`. -/
theorem iterativeSmoothing_outputPoint_value_le
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      F x̂T - fStar ≤ (δ / (1 + δ)) * F x̂T) :
    F x̂T ≤ (1 + δ) * fStar := by
  -- Reuse the dedicated algebraic bridge from the relative-gap estimate to the value bound.
  exact iterativeSmoothing_outputPoint_value_le_of_relative_gap hδ hTerminal_relative_gap

-- Proof sketch: combine the stopping-time bound from Theorem 7.11 (1) with the definition of
-- `iterativeSmoothingTotalLowerLevelSteps` as the product of the canonical stopping time and the
-- canonical block length, then expand the block-length expression.
/-- Helper for Theorem 7.11: with explicit stagewise parameter positivity, the total lower-level
work is bounded by the textbook expression. -/
lemma iterativeSmoothing_totalLowerLevelSteps_le_of_parameter_pos
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (hδ : 0 < δ)
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hPreterminal_feasible : x̂ s ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ x : E, x ∈ feasibleSet → fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate : ℝ) ≤
      2 * γ * Real.exp 1 * (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) := by
  have htime :
      (T : ℝ) ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) :=
    iterativeSmoothing_stoppingTime_le_of_parameter_pos
      hParameterPos hScale_pos hPreterminal_feasible hOptimal_value_le_of_feasible
      hInitial_value_le
  have hblock :
      (iterativeSmoothingBlockLength (m : ℕ) n δ γ : ℝ) ≤
        2 * Real.exp 1 * γ *
          Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) :=
    iterativeSmoothingBlockLength_le_unfloored hδ hScale_pos
  have hone_log_nonneg : 0 ≤ 1 + Real.log (γ * Real.sqrt (n : ℝ)) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    linarith [htime, hT_nonneg]
  -- Bound the two factors separately and combine them through the product definition.
  rw [iterativeSmoothingTotalLowerLevelSteps_def, Nat.cast_mul]
  have htime_mul :
      (T : ℝ) * (iterativeSmoothingBlockLength (m : ℕ) n δ γ : ℝ) ≤
        (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
          (iterativeSmoothingBlockLength (m : ℕ) n δ γ : ℝ) := by
    exact mul_le_mul_of_nonneg_right htime (by positivity)
  have hblock_mul :
      (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
          (iterativeSmoothingBlockLength (m : ℕ) n δ γ : ℝ) ≤
        (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
          (2 * Real.exp 1 * γ *
            Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ)) := by
    exact mul_le_mul_of_nonneg_left hblock hone_log_nonneg
  simpa [mul_assoc, mul_left_comm, mul_comm] using htime_mul.trans hblock_mul

/-- Theorem 7.11 (3): if the generated points are feasible, feasible points have value at least
`f*`, the initial value satisfies `f(\hat x_0) ≤ γ √n f*`, and the stagewise smoothing
parameters are positive, then the total number of lower-level steps is bounded by the stated
explicit complexity expression once the scale and relative-accuracy parameters are in their
textbook range. -/
theorem iterativeSmoothing_totalLowerLevelSteps_le
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (hδ : 0 < δ)
    (hScale_pos : 0 < γ * Real.sqrt (n : ℝ))
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ x : E, x ∈ feasibleSet → fStar ≤ F x)
    (hInitial_value_le :
      F (x̂ 0) ≤ γ * Real.sqrt (n : ℝ) * fStar) :
    (iterativeSmoothingTotalLowerLevelSteps δ γ hTerminate : ℝ) ≤
      2 * γ * Real.exp 1 * (1 + Real.log (γ * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (2 * (m : ℝ))) * (1 + 1 / δ) := by
  -- The public theorem again reduces to the preterminal feasibility input expected by the helper.
  have hPreterminal_feasible : x̂ s ∈ feasibleSet :=
    hGenerated_feasible s
  -- Reuse the already-proved total-work estimate with explicit parameter positivity.
  exact
    iterativeSmoothing_totalLowerLevelSteps_le_of_parameter_pos
      hParameterPos hδ hScale_pos hPreterminal_feasible hOptimal_value_le_of_feasible
      hInitial_value_le

/-- If the optimal value `f*` is positive, then the accepted output point in Theorem 7.11 has
relative accuracy `δ` with respect to `f*` in the sense of Definition 7.1. -/
theorem iterativeSmoothing_outputPoint_isRelativeAccuracy
    (hfStar_pos : 0 < fStar)
    (hδ : 0 < δ)
    (hOutput_value_ge : fStar ≤ F (iterativeSmoothingOutputPoint hTerminate))
    (hTerminal_relative_gap :
      F (iterativeSmoothingOutputPoint hTerminate) - fStar ≤
        (δ / (1 + δ)) * F (iterativeSmoothingOutputPoint hTerminate)) :
    IsRelativeAccuracy fStar δ (F (iterativeSmoothingOutputPoint hTerminate)) := by
  have hOne_add_δ : 0 < 1 + δ := by
    linarith
  have hMul :
      (F (iterativeSmoothingOutputPoint hTerminate) - fStar) * (1 + δ) ≤
        δ * F (iterativeSmoothingOutputPoint hTerminate) := by
    have hScaled :=
      mul_le_mul_of_nonneg_right hTerminal_relative_gap hOne_add_δ.le
    have hOne_add_δ_ne : (1 + δ) ≠ 0 := ne_of_gt hOne_add_δ
    simpa [div_eq_mul_inv, hOne_add_δ_ne, mul_assoc, mul_left_comm, mul_comm] using hScaled
  have hUpper : F (iterativeSmoothingOutputPoint hTerminate) ≤ (1 + δ) * fStar := by
    nlinarith [hMul]
  exact ⟨hfStar_pos, hOutput_value_ge, hUpper⟩

end Complexity
