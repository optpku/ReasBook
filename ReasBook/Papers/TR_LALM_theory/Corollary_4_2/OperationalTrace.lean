/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.Asymptotics.Defs
public import TR_LALM_theory.Corollary_4_2.Restart
public import TR_LALM_theory.Lemma_2_11.Residual
import TR_LALM_theory.Corollary_3_8
import TR_LALM_theory.Corollary_3_8.OperationalTrace

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The corrected deterministic residual-complexity constant. -/
noncomputable def deterministicComplexityConstant
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) : ℝ :=
  Residual.comparisonConstant
      (primalComparisonConstant h params.delta params.beta params.rho params.multiplierBound)
      (multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound) params.rho *
    (params.delta ^ 2 +
      8 * (run.lyapunov h params 1 - lyapunovLowerBound h params) / params.beta)

/-- The corrected deterministic complexity constant has its explicit formula. -/
theorem deterministicComplexityConstant_def
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    deterministicComplexityConstant h params run =
      Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
        (params.delta ^ 2 +
          8 * (run.lyapunov h params 1 - lyapunovLowerBound h params) /
            params.beta) := by
  -- Expose the residual comparison and Lyapunov-gap factors.
  rfl

/-- The corrected deterministic iteration budget at tolerance `ε`. -/
noncomputable def deterministicIterationBudget
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (ε : ℝ≥0) : ℕ :=
  Nat.ceil (deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2) + 2

/-- The corrected deterministic budget is the ceiling of the residual threshold
plus two initial iterations. -/
theorem deterministicIterationBudget_def
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (ε : ℝ≥0) :
    deterministicIterationBudget h params run ε =
      Nat.ceil (deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2) + 2 := by
  -- Expose the ceiling budget and its two-index overhead.
  rfl

/-- The corrected direct stochastic iteration budget at tolerance `ε`. -/
noncomputable def stochasticIterationBudget
    {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (ε : ℝ≥0) : ℕ :=
  Nat.ceil (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) + 2

/-- The corrected stochastic budget is the ceiling of its residual threshold
plus two initial iterations. -/
theorem stochasticIterationBudget_def
    {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (ε : ℝ≥0) :
    stochasticIterationBudget h oracle params ε =
      Nat.ceil (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) + 2 := by
  -- Expose the direct stochastic ceiling budget.
  rfl

/-- The corrected safeguarded iteration budget adjusts the stochastic threshold
by the restart success probability `1 - confidence`. -/
noncomputable def safeguardedIterationBudget
    {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ) (ε : ℝ≥0) : ℕ :=
  Nat.ceil (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2 /
    (1 - confidence)) + 2

/-- The corrected safeguarded budget is the ceiling of the
confidence-adjusted residual threshold plus two initial iterations. -/
theorem safeguardedIterationBudget_def
    {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ) (ε : ℝ≥0) :
    safeguardedIterationBudget h oracle params confidence ε =
      Nat.ceil (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2 /
        (1 - confidence)) + 2 := by
  -- Expose the confidence-adjusted ceiling budget.
  rfl

/-- The corrected safeguarded budget always contains at least two iterations. -/
theorem safeguardedIterationBudget_ge_two
    {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ) (ε : ℝ≥0) :
    2 ≤ safeguardedIterationBudget h oracle params confidence ε := by
  -- The explicit two-iteration overhead gives the lower bound.
  rw [safeguardedIterationBudget_def]
  omega

/-- The corrected safeguarded budget satisfies the confidence-adjusted
iteration threshold used by the restart guarantee. -/
theorem safeguardedIterationBudget_threshold
    {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀)
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) (ε : ℝ≥0) (ε_pos : 0 < ε) :
    stochasticComplexityConstant h oracle params * ε⁻¹ ^ 2 ≤
      (1 - confidence) *
        ((safeguardedIterationBudget h oracle params confidence ε : ℝ) - 1) := by
  -- The positive success probability transports the ceiling bound through division.
  have hsuccess : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hceiling := Nat.le_ceil
    (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2 /
      (1 - confidence))
  rw [safeguardedIterationBudget_def]
  norm_num at hceiling ⊢
  have hrecover :
      stochasticComplexityConstant h oracle params * ((ε : ℝ) ^ 2)⁻¹ =
        (1 - confidence) *
          (stochasticComplexityConstant h oracle params * ((ε : ℝ) ^ 2)⁻¹ /
            (1 - confidence)) := by
    field_simp
  calc
    stochasticComplexityConstant h oracle params * ((ε : ℝ) ^ 2)⁻¹ =
        (1 - confidence) *
          (stochasticComplexityConstant h oracle params * ((ε : ℝ) ^ 2)⁻¹ /
            (1 - confidence)) := hrecover
    _ ≤ (1 - confidence) *
        ↑⌈stochasticComplexityConstant h oracle params * ((ε : ℝ) ^ 2)⁻¹ /
          (1 - confidence)⌉₊ :=
      mul_le_mul_of_nonneg_left hceiling hsuccess.le
    _ ≤ (1 - confidence) *
        (↑⌈stochasticComplexityConstant h oracle params * ((ε : ℝ) ^ 2)⁻¹ /
          (1 - confidence)⌉₊ + 2 - 1) := by
      apply mul_le_mul_of_nonneg_left _ hsuccess.le
      linarith

namespace Run

variable {h : EqualityConstrained.Regularity f c}
variable {params : Parameters h x₀ multiplier₀}

/-- The deterministic corrected operational trace records the exact gradient,
base-model solve, and correction solve at each transition. -/
noncomputable def exactGradientSolveTrace
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) :
    List (EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
  (List.range K).map (fun k ↦
    (gradient f (run.point k), run.baseStep k, run.correction k))

/-- The corrected deterministic trace has one explicit triple per transition. -/
theorem exactGradientSolveTrace_def
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) :
    run.exactGradientSolveTrace K = (List.range K).map (fun k ↦
      (gradient f (run.point k), run.baseStep k, run.correction k)) := by
  -- Expose the one-entry-per-transition trace.
  rfl

/-- The number of transitions in a corrected deterministic prefix. -/
noncomputable def iterationCount
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientSolveTrace K).length

/-- The number of exact first-order evaluations in a corrected deterministic prefix. -/
noncomputable def firstOrderEvaluationCount
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientSolveTrace K).length

/-- The number of primal model linear-system solves in a corrected deterministic prefix. -/
noncomputable def primalSolveCount
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientSolveTrace K).length

/-- The number of correction linear-system solves in a corrected deterministic prefix. -/
noncomputable def correctionSolveCount
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) : ℕ :=
  (run.exactGradientSolveTrace K).length

/-- Every corrected deterministic transition contributes one iteration count. -/
theorem iterationCount_spec
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) :
    run.iterationCount K = K := by
  -- Mapping the range preserves its length.
  simp [iterationCount, exactGradientSolveTrace]

/-- Every corrected deterministic transition contributes one first-order evaluation. -/
theorem firstOrderEvaluationCount_spec
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) :
    run.firstOrderEvaluationCount K = K := by
  -- Every trace entry contains exactly one exact gradient evaluation.
  simp [firstOrderEvaluationCount, exactGradientSolveTrace]

/-- Every corrected deterministic transition contributes one primal solve. -/
theorem primalSolveCount_spec
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) :
    run.primalSolveCount K = K := by
  -- Every trace entry contains exactly one base-model solve.
  simp [primalSolveCount, exactGradientSolveTrace]

/-- Every corrected deterministic transition contributes one correction solve. -/
theorem correctionSolveCount_spec
    (run : Run f c params.rho params.beta x₀ multiplier₀) (K : ℕ) :
    run.correctionSolveCount K = K := by
  -- Every trace entry contains exactly one correction solve.
  simp [correctionSolveCount, exactGradientSolveTrace]

end Run

namespace StochasticRun

variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀} {Q B b : ℕ+}

/-- The concrete SPIDER gradient-evaluation count for a corrected stochastic prefix. -/
noncomputable def gradientEvaluationCount
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : ℕ :=
  ((List.range K).flatMap (fun k ↦
    if k % (Q : ℕ) = 0 then
      (List.range B).map (fun i ↦ run.sample k i)
    else
      (List.range b).map (fun i ↦ run.sample k i) ++
        (List.range b).map (fun i ↦ run.sample k i))).length

/-- The deterministic constraint-evaluation count of a corrected stochastic prefix,
including the base and SOC evaluations in every transition. -/
noncomputable def constraintEvaluationCount
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : ℕ :=
  2 * ((List.range K).map (fun k ↦ fun ω ↦ c (run.point (k + 1) ω))).length

/-- The deterministic Jacobian-evaluation count of a corrected stochastic prefix,
including the base and SOC evaluations in every transition. -/
noncomputable def jacobianEvaluationCount
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : ℕ :=
  2 * ((List.range K).map (fun k ↦ fun ω ↦ fderiv ℝ c (run.point k ω))).length

/-- The primal model solve count of a corrected stochastic prefix. -/
noncomputable def primalSolveCount
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : ℕ :=
  ((List.range K).map (fun k ↦ run.baseStep k)).length

/-- The correction solve count of a corrected stochastic prefix. -/
noncomputable def correctionSolveCount
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : ℕ :=
  ((List.range K).map (fun k ↦ run.correction k)).length

/-- The corrected SPIDER gradient counter has its refresh/update sum formula. -/
theorem gradientEvaluationCount_spec
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.gradientEvaluationCount K = ∑ k ∈ Finset.range K,
      if k % (Q : ℕ) = 0 then (B : ℕ) else 2 * (b : ℕ) := by
  -- Convert the flattened batch lists into their finite sum of lengths.
  unfold gradientEvaluationCount
  rw [List.length_flatMap]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  apply Finset.sum_congr rfl
  intro k hk
  split
  · simp
  · simp [two_mul]

/-- The corrected stochastic constraint counter is two per transition. -/
theorem constraintEvaluationCount_spec
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.constraintEvaluationCount K = 2 * K := by
  -- Mapping the transition range preserves its length before the SOC factor.
  simp [constraintEvaluationCount]

/-- The corrected stochastic Jacobian counter is two per transition. -/
theorem jacobianEvaluationCount_spec
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.jacobianEvaluationCount K = 2 * K := by
  -- Mapping the transition range preserves its length before the SOC factor.
  simp [jacobianEvaluationCount]

/-- The corrected stochastic primal-solve counter is one per transition. -/
theorem primalSolveCount_spec
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.primalSolveCount K = K := by
  -- Mapping the transition range preserves its length.
  simp [primalSolveCount]

/-- The corrected stochastic correction-solve counter is one per transition. -/
theorem correctionSolveCount_spec
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.correctionSolveCount K = K := by
  -- Mapping the transition range preserves its length.
  simp [correctionSolveCount]

end StochasticRun

namespace SafeguardedRestart

variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- The iterations executed by corrected attempt `i`, truncated at its first
localization exit. -/
noncomputable def attemptIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℕ :=
  RestartAccounting.truncatedIterations K
    (StochasticRun.Localization.exitTime (restart.attempt i) X ω)

/-- No corrected restart attempt executes more than `K` iterations. -/
theorem attemptIterations_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.attemptIterations i ω ≤ K := by
  -- Apply the canonical truncation bound at this attempt's exit time.
  exact RestartAccounting.truncatedIterations_le K _

/-- The accumulated corrected-attempt cost, using the canonical extended
restart accounting and hence equal to `⊤` on nontermination. -/
-- Route correction: expose the canonical branches locally because the imported
-- Corollary 3.8 accounting definition is opaque outside its owner module.
noncomputable def accumulatedCost
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : ℕ → Ω → ℕ) (ω : Ω) : ℕ∞ :=
  if h_count : restart.attemptCount ω = ⊤ then ⊤
  else (∑ i ∈ Finset.range ((restart.attemptCount ω).untop h_count), cost i ω : ℕ)

/-- At a finite corrected attempt count, accumulated cost is the finite sum of
the per-attempt costs. -/
theorem accumulatedCost_eq_sum
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : ℕ → Ω → ℕ) (ω : Ω) (h_count : restart.attemptCount ω ≠ ⊤) :
    restart.accumulatedCost cost ω =
      ∑ i ∈ Finset.range ((restart.attemptCount ω).untop h_count), cost i ω := by
  -- Select the locally exposed finite branch of canonical restart accounting.
  simp only [accumulatedCost, h_count, ↓reduceDIte]

/-- A nonterminating corrected restart has infinite accumulated cost. -/
theorem accumulatedCost_eq_top
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : ℕ → Ω → ℕ) (ω : Ω) (h_count : restart.attemptCount ω = ⊤) :
    restart.accumulatedCost cost ω = ⊤ := by
  -- Select the locally exposed infinite branch of canonical restart accounting.
  simp only [accumulatedCost, h_count, ↓reduceDIte]

/-- Helper for Corollary 4.2: a positive uniform per-attempt budget bounds
the corrected accumulated cost by attempt count times that budget. -/
theorem accumulatedCost_le_attemptCount_mul
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : ℕ → Ω → ℕ) (ω : Ω) (budget : ℕ)
    (hbudget : 0 < budget) (hcost : ∀ i, cost i ω ≤ budget) :
    restart.accumulatedCost cost ω ≤ restart.attemptCount ω * budget := by
  -- Split once on the extended attempt count and bound the finite sum termwise.
  cases h_count : restart.attemptCount ω using ENat.recTopCoe with
  | top =>
      have hbudgetNe : (budget : ℕ∞) ≠ 0 := by
        exact_mod_cast hbudget.ne'
      simp only [accumulatedCost, h_count, ↓reduceDIte, ENat.top_mul',
        hbudgetNe, if_false, le_rfl]
  | coe count =>
      have hsum :
          ∑ i ∈ Finset.range count, cost i ω ≤ count * budget := by
        calc
          ∑ i ∈ Finset.range count, cost i ω ≤
              ∑ _i ∈ Finset.range count, budget :=
            Finset.sum_le_sum fun i _hi ↦ hcost i
          _ = count * budget := by
            simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      simp only [accumulatedCost, h_count, ENat.coe_ne_top, ↓reduceDIte]
      exact_mod_cast hsum

/-- The total number of corrected stochastic transitions actually executed
through the first accepted attempt. -/
noncomputable def totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.accumulatedCost restart.attemptIterations ω

/-- Corrected total work is at most `K` times the number of attempted runs. -/
theorem totalIterations_le_attemptCount_mul
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.totalIterations ω ≤ restart.attemptCount ω * K := by
  -- Transfer the per-attempt horizon bound through accumulated cost.
  have hKPos : 0 < K := by
    omega
  exact restart.accumulatedCost_le_attemptCount_mul restart.attemptIterations ω K
    hKPos
    (fun i ↦ restart.attemptIterations_le i ω)

/-- A nonterminating corrected restart has infinite total iteration count. -/
theorem totalIterations_eq_top
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (h_count : restart.attemptCount ω = ⊤) :
    restart.totalIterations ω = ⊤ := by
  -- Total iterations are the accumulated truncated-attempt costs.
  exact restart.accumulatedCost_eq_top restart.attemptIterations ω h_count

/-- The stochastic-gradient evaluations made by one truncated corrected attempt. -/
noncomputable def attemptGradientEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) : ℕ :=
  (restart.attempt i).gradientEvaluationCount (restart.attemptIterations i ω)

/-- The corrected per-attempt gradient counter is evaluated at the number of
iterations actually executed. -/
theorem attemptGradientEvaluationCount_def
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.attemptGradientEvaluationCount i ω =
      (restart.attempt i).gradientEvaluationCount
        (restart.attemptIterations i ω) := by
  rfl

/-- One corrected attempt uses at most its prescribed full-run gradient budget. -/
theorem attemptGradientEvaluationCount_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (ω : Ω) :
    restart.attemptGradientEvaluationCount i ω ≤
      (restart.attempt i).gradientEvaluationCount K := by
  -- Enlarge the nonnegative batch-cost sum from the executed prefix to the horizon.
  rw [attemptGradientEvaluationCount_def,
    (restart.attempt i).gradientEvaluationCount_spec,
    (restart.attempt i).gradientEvaluationCount_spec]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (restart.attemptIterations_le i ω))
    (fun _ _ _ ↦ Nat.zero_le _)

/-- The total corrected SPIDER gradient-evaluation count across all attempts. -/
noncomputable def gradientEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.accumulatedCost restart.attemptGradientEvaluationCount ω

/-- The total deterministic constraint-evaluation count across corrected attempts,
with one base and one SOC evaluation per executed transition. -/
noncomputable def constraintEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  2 * restart.totalIterations ω

/-- The total deterministic Jacobian-evaluation count across corrected attempts,
with one base and one SOC evaluation per executed transition. -/
noncomputable def jacobianEvaluationCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  2 * restart.totalIterations ω

/-- The total primal model solve count across corrected attempts. -/
noncomputable def primalSolveCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- The total correction solve count across corrected attempts. -/
noncomputable def correctionSolveCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- Corollary 4.2: the prescribed abstract localization-membership cost assigns
one membership test to each corrected transition; it is a cost model, not an
instrumented execution trace. -/
noncomputable def membershipTestCount
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) : ℕ∞ :=
  restart.totalIterations ω

/-- The corrected total gradient count is bounded by the full-attempt budget
times the number of attempted runs. -/
theorem gradientEvaluationCount_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.gradientEvaluationCount ω ≤
      restart.attemptCount ω * (restart.attempt 0).gradientEvaluationCount K := by
  -- The full-attempt gradient budget is positive because the horizon is nonempty.
  have hbudget : 0 < (restart.attempt 0).gradientEvaluationCount K := by
    rw [(restart.attempt 0).gradientEvaluationCount_spec]
    refine Finset.sum_pos ?_ ?_
    · intro k hk
      split
      · exact (SPIDER.refreshBatchSize K).pos
      · positivity
    · have hKPos : 0 < K := by
        omega
      exact ⟨0, Finset.mem_range.mpr hKPos⟩
  -- All attempts have the same schedule, so their full-prefix counts agree.
  have hfull (i : ℕ) :
      (restart.attempt i).gradientEvaluationCount K =
        (restart.attempt 0).gradientEvaluationCount K := by
    rw [(restart.attempt i).gradientEvaluationCount_spec,
      (restart.attempt 0).gradientEvaluationCount_spec]
  exact restart.accumulatedCost_le_attemptCount_mul
    restart.attemptGradientEvaluationCount ω _ hbudget
    (fun i ↦ (restart.attemptGradientEvaluationCount_le i ω).trans_eq (hfull i))

/-- A nonterminating corrected restart has infinite gradient-evaluation count. -/
theorem gradientEvaluationCount_eq_top
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (h_count : restart.attemptCount ω = ⊤) :
    restart.gradientEvaluationCount ω = ⊤ := by
  -- The gradient counter uses the same infinite accumulated-cost branch.
  exact restart.accumulatedCost_eq_top restart.attemptGradientEvaluationCount ω h_count

/-- The corrected restart constraint counter is twice the total transition count. -/
theorem constraintEvaluationCount_eq_two_mul_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.constraintEvaluationCount ω = 2 * restart.totalIterations ω := by
  -- This counter charges the base and SOC constraint evaluations.
  rfl

/-- The corrected restart Jacobian counter is twice the total transition count. -/
theorem jacobianEvaluationCount_eq_two_mul_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.jacobianEvaluationCount ω = 2 * restart.totalIterations ω := by
  -- This counter charges the base and SOC Jacobian evaluations.
  rfl

/-- Compatibility name for Corollary 4.2: the corrected constraint counter is
twice the total transition count. -/
theorem constraintEvaluationCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.constraintEvaluationCount ω = 2 * restart.totalIterations ω := by
  exact constraintEvaluationCount_eq_two_mul_totalIterations restart ω

/-- Compatibility name for Corollary 4.2: the corrected Jacobian counter is
twice the total transition count. -/
theorem jacobianEvaluationCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.jacobianEvaluationCount ω = 2 * restart.totalIterations ω := by
  exact jacobianEvaluationCount_eq_two_mul_totalIterations restart ω

/-- The corrected restart primal-solve counter equals the total transition count. -/
theorem primalSolveCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.primalSolveCount ω = restart.totalIterations ω := by
  -- This counter is an alias for the executed-transition count.
  rfl

/-- The corrected restart correction-solve counter equals the total transition count. -/
theorem correctionSolveCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.correctionSolveCount ω = restart.totalIterations ω := by
  -- This counter is an alias for the executed-transition count.
  rfl

/-- The prescribed membership-test cost model for Corollary 4.2 equals the
corrected transition count. -/
theorem membershipTestCount_eq_totalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.membershipTestCount ω = restart.totalIterations ω := by
  rfl

/-- The prescribed membership-test cost for Corollary 4.2 is bounded by the
horizon times the number of attempted corrected runs. -/
theorem membershipTestCount_le_attemptCount_mul
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) :
    restart.membershipTestCount ω ≤ restart.attemptCount ω * K := by
  rw [membershipTestCount_eq_totalIterations]
  exact restart.totalIterations_le_attemptCount_mul ω

/-- A nonterminating corrected restart has infinite prescribed membership-test
cost in the abstract model for Corollary 4.2. -/
theorem membershipTestCount_eq_top
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (ω : Ω) (h_count : restart.attemptCount ω = ⊤) :
    restart.membershipTestCount ω = ⊤ := by
  rw [membershipTestCount_eq_totalIterations]
  exact restart.totalIterations_eq_top ω h_count

/-- The fixed-horizon expected prescribed membership-test cost for Corollary 4.2
equals the expected corrected transition count. -/
theorem expectedMembershipTestCount_eq_expectedTotalIterations
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    (∫⁻ ω, (restart.membershipTestCount ω : ℝ≥0∞) ∂ℙ) =
      ∫⁻ ω, (restart.totalIterations ω : ℝ≥0∞) ∂ℙ := by
  simp only [membershipTestCount_eq_totalIterations]

/-- Any fixed-horizon expected transition-count bound for Corollary 4.2 transfers
to the prescribed membership-test cost. -/
theorem expectedMembershipTestCount_le_of_expectedTotalIterations_le
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (bound : ℝ≥0∞)
    (hbound : (∫⁻ ω, (restart.totalIterations ω : ℝ≥0∞) ∂ℙ) ≤ bound) :
    (∫⁻ ω, (restart.membershipTestCount ω : ℝ≥0∞) ∂ℙ) ≤ bound := by
  rw [expectedMembershipTestCount_eq_expectedTotalIterations]
  exact hbound

/-- The expected prescribed membership-test cost for Corollary 4.2 is bounded by
the horizon times the expected number of corrected attempts. -/
theorem expectedMembershipTestCount_le_attemptCount_mul
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    (∫⁻ ω, (restart.membershipTestCount ω : ℝ≥0∞) ∂ℙ) ≤
      (∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ) * K := by
  have hpointwise (ω : Ω) :
      (restart.membershipTestCount ω : ℝ≥0∞) ≤
        (restart.attemptCount ω : ℝ≥0∞) * K := by
    simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
      ENat.toENNReal_mono (restart.membershipTestCount_le_attemptCount_mul ω)
  calc
    (∫⁻ ω, (restart.membershipTestCount ω : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) * K ∂ℙ :=
      lintegral_mono hpointwise
    _ = (∫⁻ ω, (restart.attemptCount ω : ℝ≥0∞) ∂ℙ) * K := by
      rw [lintegral_mul_const']
      exact ENNReal.natCast_ne_top K

/-- The safeguarded `ε`-schedule expected membership-test cost for Corollary 4.2
is pointwise identical to its expected corrected transition count. -/
theorem expectedMembershipTestCount_schedule_eq_expectedTotalIterations
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).membershipTestCount ω : ℝ≥0∞) ∂ℙ)) =
      fun ε : ℝ≥0 ↦ ENNReal.toReal
        (∫⁻ ω, ((restart ε).totalIterations ω : ℝ≥0∞) ∂ℙ) := by
  funext ε
  rw [expectedMembershipTestCount_eq_expectedTotalIterations]

/-- An expected corrected-transition Big-O estimate along the safeguarded
`ε`-schedule transfers to the prescribed membership-test cost for Corollary 4.2. -/
theorem expectedMembershipTestCount_isBigO_of_totalIterations
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (rate : ℝ≥0 → ℝ)
    (h_total : (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).totalIterations ω : ℝ≥0∞) ∂ℙ))
        =O[nhdsWithin 0 (Set.Ioi 0)] rate) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).membershipTestCount ω : ℝ≥0∞) ∂ℙ))
        =O[nhdsWithin 0 (Set.Ioi 0)] rate := by
  rw [expectedMembershipTestCount_schedule_eq_expectedTotalIterations confidence X restart]
  exact h_total

end SafeguardedRestart

end LALM.Correction

end
