/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.Order.Floor.Div
public import TR_LALM_theory.Corollary_4_2.StoppedRestartProbability

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

namespace StoppedSafeguardedRestart

/-- Corollary 4.2: the accumulated finite stopped-attempt cost is the finite
sum of attempted costs, and is `⊤` precisely on nontermination. -/
noncomputable def accumulatedCost
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (cost : ℕ → Ω → ℕ) (ω : Ω) : ℕ∞ :=
  if hcount : attemptCount restart ω = ⊤ then ⊤
  else (∑ i ∈ Finset.range ((attemptCount restart ω).untop hcount), cost i ω : ℕ)

/-- Helper for Corollary 4.2: at finite acceptance, accumulated work is the
corresponding finite sum of per-attempt costs. -/
theorem accumulatedCost_eq_sum
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (cost : ℕ → Ω → ℕ) (ω : Ω)
    (hcount : attemptCount restart ω ≠ ⊤) :
    accumulatedCost restart cost ω =
      ∑ i ∈ Finset.range ((attemptCount restart ω).untop hcount), cost i ω := by
  simp only [accumulatedCost, hcount, ↓reduceDIte]

/-- Helper for Corollary 4.2: a nonterminating stopped restart has infinite
accumulated cost. -/
theorem accumulatedCost_eq_top
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (cost : ℕ → Ω → ℕ) (ω : Ω)
    (hcount : attemptCount restart ω = ⊤) :
    accumulatedCost restart cost ω = ⊤ := by
  simp only [accumulatedCost, hcount, ↓reduceDIte]

/-- Helper for Corollary 4.2: a uniform finite per-attempt budget bounds the
accumulated stopped cost by the attempt count times that budget. -/
theorem accumulatedCost_le_attemptCount_mul
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (cost : ℕ → Ω → ℕ) (ω : Ω) (budget : ℕ)
    (hbudget : 0 < budget) (hcost : ∀ i, cost i ω ≤ budget) :
    accumulatedCost restart cost ω ≤ attemptCount restart ω * budget := by
  cases hcount : attemptCount restart ω using ENat.recTopCoe with
  | top =>
      have hbudgetNe : (budget : ℕ∞) ≠ 0 := by
        exact_mod_cast hbudget.ne'
      simp only [accumulatedCost, hcount, ↓reduceDIte, ENat.top_mul',
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
      simp only [accumulatedCost, hcount, ENat.coe_ne_top, ↓reduceDIte]
      exact_mod_cast hsum

/-- Corollary 4.2: the total number of active transitions executed across the
accepted stopped attempts. -/
noncomputable def totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  accumulatedCost restart restart.attemptIterations ω

/-- Corollary 4.2: stopped total work is bounded by the horizon times the
number of attempted runs. -/
theorem totalIterations_le_attemptCount_mul
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) :
    totalIterations restart ω ≤ attemptCount restart ω * K := by
  have hKPos : 0 < K := by omega
  exact accumulatedCost_le_attemptCount_mul restart restart.attemptIterations ω K
    hKPos (fun i ↦ attemptIterations_le restart i ω)

/-- Helper for Corollary 4.2: a nonterminating stopped restart has infinite
transition count. -/
theorem totalIterations_eq_top
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) (hcount : attemptCount restart ω = ⊤) :
    totalIterations restart ω = ⊤ := by
  exact accumulatedCost_eq_top restart restart.attemptIterations ω hcount

/-- Helper for Corollary 4.2: at most `K ⌈/⌉ q` indices below a stopped prefix
of length at most `K` are refresh indices. -/
private lemma refreshIndexCard_le_ceilDiv
    (L K q : ℕ) (hq : 0 < q) (hLK : L ≤ K) :
    ((Finset.range L).filter (fun k ↦ k % q = 0)).card ≤ K ⌈/⌉ q := by
  have hKq : K ≤ (K ⌈/⌉ q) * q := by
    simpa only [mul_comm] using
      (ceilDiv_le_iff_le_mul hq).mp (le_refl (K ⌈/⌉ q))
  have hcard : ((Finset.range L).filter (fun k ↦ k % q = 0)).card ≤
      (Finset.range (K ⌈/⌉ q)).card := by
    apply Finset.card_le_card_of_injOn (fun k ↦ k / q)
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul hq]
      exact lt_of_lt_of_le (lt_of_lt_of_le (Finset.mem_range.mp hk'.1) hLK) hKq
    · intro a ha b hb hab
      change a / q = b / q at hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have harepr := Nat.div_add_mod a q
      have hbrepr := Nat.div_add_mod b q
      calc
        a = q * (a / q) + a % q := harepr.symm
        _ = q * (a / q) := by rw [ha'.2, Nat.add_zero]
        _ = q * (b / q) := by rw [hab]
        _ = q * (b / q) + b % q := by rw [hb'.2, Nat.add_zero]
        _ = b := hbrepr
  simpa only [Finset.card_range] using hcard

/-- Corollary 4.2: the stochastic-gradient count charged to one stopped
attempt, including exactly the refresh and two inner batches of SPIDER. -/
noncomputable def attemptGradientEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) : ℕ :=
  ∑ k ∈ StoppedAttempt.executedIndexSet (restart.attempt i) ω,
    if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
      (SPIDER.refreshBatchSize K : ℕ)
    else 2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)

/-- Helper for Corollary 4.2: one stopped attempt uses no more than the exact
finite-horizon SPIDER budget `⌈K/Q⌉ B + 2 K b`. -/
theorem attemptGradientEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (ω : Ω) :
    attemptGradientEvaluationCount restart i ω ≤
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
  have hq : 0 < (SPIDER.refreshPeriod K : ℕ) :=
    (SPIDER.refreshPeriod K).pos
  let S := StoppedAttempt.executedIndexSet (restart.attempt i) ω
  have hS : S ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr ((StoppedAttempt.mem_executedIndexSet_iff
      (restart.attempt i) ω k).mp hk).1
  have hrefreshS : (S.filter
      (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card ≤
      K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ) := by
    have hfilter : S.filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0) ⊆
        (Finset.range K).filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0) := by
      intro k hk
      have hkS := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hS hkS.1, hkS.2⟩
    exact (Finset.card_le_card hfilter).trans
      (refreshIndexCard_le_ceilDiv K K (SPIDER.refreshPeriod K : ℕ) hq le_rfl)
  have hScard : S.card ≤ K :=
    (Finset.card_le_card hS).trans_eq (Finset.card_range K)
  unfold attemptGradientEvaluationCount
  calc
    (∑ k ∈ S,
        if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
          (SPIDER.refreshBatchSize K : ℕ)
        else 2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) ≤
        ∑ k ∈ S,
          ((if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
              (SPIDER.refreshBatchSize K : ℕ) else 0) +
            2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) := by
      apply Finset.sum_le_sum
      intro k hk
      split <;> omega
    _ = (S.filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card *
          (SPIDER.refreshBatchSize K : ℕ) +
        S.card * (2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        K * (2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) :=
      add_le_add (Nat.mul_le_mul_right _ hrefreshS) (Nat.mul_le_mul_right _ hScard)
    _ = (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by ring

/-- Corollary 4.2: total stochastic-gradient work across stopped attempts. -/
noncomputable def gradientEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  accumulatedCost restart restart.attemptGradientEvaluationCount ω

/-- Corollary 4.2: total stochastic-gradient work is bounded by the exact
per-attempt SPIDER budget times the number of attempts. -/
theorem gradientEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) :
    gradientEvaluationCount restart ω ≤ attemptCount restart ω *
      ((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) := by
  have hbudget : 0 <
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
    have hsecond : 0 <
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
      positivity
    exact lt_of_lt_of_le hsecond (Nat.le_add_left _ _)
  exact accumulatedCost_le_attemptCount_mul restart
    restart.attemptGradientEvaluationCount ω _ hbudget
    (fun j ↦ attemptGradientEvaluationCount_le restart j ω)

/-- Corollary 4.2: a corrected SOC transition charges two constraint
evaluations, one for the trial residual and one for the corrected endpoint.
The one-time initialization evaluation of `c x₀` is outside this transition
counter. -/
noncomputable def constraintEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ := 2 * totalIterations restart ω

/-- Corollary 4.2: a corrected SOC transition charges two Jacobian
evaluations, at the base point and at the trial point. -/
noncomputable def jacobianEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ := 2 * totalIterations restart ω

/-- Corollary 4.2: a corrected SOC transition charges one base-model linear
solve. -/
noncomputable def primalSolveCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ := totalIterations restart ω

/-- Corollary 4.2: a corrected SOC transition charges one correction linear
solve. -/
noncomputable def correctionSolveCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ := totalIterations restart ω

/-- Corollary 4.2: localization membership uses the abstract one-test-per-
transition cost model. -/
noncomputable def membershipTestCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ := totalIterations restart ω

/-- Corollary 4.2: the aggregate corrected SOC charge combines two constraint
evaluations, two Jacobian evaluations, two linear solves, and one localization
test per active transition. -/
noncomputable def socOperationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  constraintEvaluationCount restart ω + jacobianEvaluationCount restart ω +
    primalSolveCount restart ω + correctionSolveCount restart ω +
      membershipTestCount restart ω

/-- Helper for Corollary 4.2: the corrected constraint counter is twice the
executed-transition count. -/
theorem constraintEvaluationCount_eq_two_mul_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    constraintEvaluationCount restart ω = 2 * totalIterations restart ω := by
  simp only [constraintEvaluationCount]

/-- Helper for Corollary 4.2: the corrected Jacobian counter is twice the
executed-transition count. -/
theorem jacobianEvaluationCount_eq_two_mul_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    jacobianEvaluationCount restart ω = 2 * totalIterations restart ω := by
  simp only [jacobianEvaluationCount]

/-- Helper for Corollary 4.2: the primal-solve counter equals executed
transitions. -/
theorem primalSolveCount_eq_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    primalSolveCount restart ω = totalIterations restart ω := by
  simp only [primalSolveCount]

/-- Helper for Corollary 4.2: the correction-solve counter equals executed
transitions. -/
theorem correctionSolveCount_eq_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    correctionSolveCount restart ω = totalIterations restart ω := by
  simp only [correctionSolveCount]

/-- Helper for Corollary 4.2: the abstract membership-test counter equals
executed transitions. -/
theorem membershipTestCount_eq_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    membershipTestCount restart ω = totalIterations restart ω := by
  simp only [membershipTestCount]

/-- Helper for Corollary 4.2: the aggregate corrected SOC charge is seven
times the executed-transition count. -/
theorem socOperationCount_eq_seven_mul_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    socOperationCount restart ω = 7 * totalIterations restart ω := by
  simp only [socOperationCount, constraintEvaluationCount,
    jacobianEvaluationCount, primalSolveCount, correctionSolveCount,
    membershipTestCount]
  ring

/-- Helper for Corollary 4.2: pointwise accumulated work transfers to an
expected ENNReal work bound. -/
theorem expectedAccumulatedCost_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i))
    (cost : ℕ → Ω → ℕ) (budget : ℕ) (hbudget : 0 < budget)
    (hcost : ∀ i ω, cost i ω ≤ budget) :
    ∫⁻ ω, (accumulatedCost restart cost ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
  have hpointwise (ω : Ω) :
      accumulatedCost restart cost ω ≤ attemptCount restart ω * budget := by
    apply accumulatedCost_le_attemptCount_mul restart cost ω budget
    · exact hbudget
    · intro i
      exact hcost i ω
  have hcoerced (ω : Ω) :
      (accumulatedCost restart cost ω : ℝ≥0∞) ≤
        (attemptCount restart ω : ℝ≥0∞) * budget := by
    simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
      ENat.toENNReal_mono (hpointwise ω)
  calc
    (∫⁻ ω, (accumulatedCost restart cost ω : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ ω, (attemptCount restart ω : ℝ≥0∞) * budget ∂ℙ :=
      lintegral_mono hcoerced
    _ = (∫⁻ ω, (attemptCount restart ω : ℝ≥0∞) ∂ℙ) * budget := by
      rw [lintegral_mul_const']
      exact ENNReal.natCast_ne_top budget
    _ ≤ ENNReal.ofReal (1 / (1 - confidence)) * budget := by
      exact mul_le_mul_left (
        expectedAttemptCount_le restart confidence_pos confidence_lt_one hX
          successProbability_lower) budget
    _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
      have hden : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
      calc
        ENNReal.ofReal (1 / (1 - confidence)) * budget =
            ENNReal.ofReal (1 / (1 - confidence)) *
              ENNReal.ofReal (budget : ℝ) := by rw [ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal ((1 / (1 - confidence)) * (budget : ℝ)) :=
          (ENNReal.ofReal_mul (one_div_nonneg.mpr hden.le)).symm
        _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
          rw [one_div, div_eq_mul_inv, mul_comm]

/-- Corollary 4.2: expected stopped transitions are bounded by the horizon
times the geometric restart factor. -/
theorem expectedTotalIterations_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (totalIterations restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  exact expectedAccumulatedCost_le restart confidence_pos confidence_lt_one hX
    successProbability_lower restart.attemptIterations K (by omega)
    (fun i ω ↦ attemptIterations_le restart i ω)

/-- Helper for Corollary 4.2: a fixed positive integer charge per corrected
transition inherits the geometric expected-work factor. -/
theorem expectedChargedTotalIterations_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i))
    (charge : ℕ) :
    ∫⁻ ω, ((charge : ℕ∞) * totalIterations restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((charge * K : ℕ) : ℝ) / (1 - confidence)) := by
  have hpointNat (ω : Ω) :
      (charge : ℕ∞) * totalIterations restart ω ≤
        attemptCount restart ω * (charge * K) := by
    calc
      (charge : ℕ∞) * totalIterations restart ω ≤
          (charge : ℕ∞) * (attemptCount restart ω * K) := by
        gcongr
        exact totalIterations_le_attemptCount_mul restart ω
      _ = attemptCount restart ω * (charge * K) := by
        ac_rfl
  have hcoerced (ω : Ω) :
      ((charge : ℕ∞) * totalIterations restart ω : ℝ≥0∞) ≤
        (attemptCount restart ω : ℝ≥0∞) * ((charge * K : ℕ) : ℝ≥0∞) := by
    simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe, Nat.cast_mul] using
      ENat.toENNReal_mono (hpointNat ω)
  calc
    (∫⁻ ω, ((charge : ℕ∞) * totalIterations restart ω : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ ω, (attemptCount restart ω : ℝ≥0∞) *
          ((charge * K : ℕ) : ℝ≥0∞) ∂ℙ :=
      lintegral_mono hcoerced
    _ = (∫⁻ ω, (attemptCount restart ω : ℝ≥0∞) ∂ℙ) *
        ((charge * K : ℕ) : ℝ≥0∞) := by
      rw [lintegral_mul_const']
      exact ENNReal.natCast_ne_top (charge * K)
    _ ≤ ENNReal.ofReal (1 / (1 - confidence)) *
        ((charge * K : ℕ) : ℝ≥0∞) := by
      exact mul_le_mul_left (
        expectedAttemptCount_le restart confidence_pos confidence_lt_one hX
          successProbability_lower) _
    _ = ENNReal.ofReal (((charge * K : ℕ) : ℝ) / (1 - confidence)) := by
      have hden : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
      calc
        ENNReal.ofReal (1 / (1 - confidence)) *
            ((charge * K : ℕ) : ℝ≥0∞) =
            ENNReal.ofReal (1 / (1 - confidence)) *
              ENNReal.ofReal ((charge * K : ℕ) : ℝ) := by
          rw [ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal ((1 / (1 - confidence)) *
              ((charge * K : ℕ) : ℝ)) :=
          (ENNReal.ofReal_mul (one_div_nonneg.mpr hden.le)).symm
        _ = ENNReal.ofReal (((charge * K : ℕ) : ℝ) / (1 - confidence)) := by
          rw [one_div, div_eq_mul_inv, mul_comm]

/-- Corollary 4.2: expected constraint evaluations obey the same stopped
transition bound. -/
theorem expectedConstraintEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (constraintEvaluationCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((2 * K : ℕ) : ℝ) / (1 - confidence)) := by
  convert expectedChargedTotalIterations_le restart confidence_pos
      confidence_lt_one hX successProbability_lower 2 using 1
  · simp only [constraintEvaluationCount, ENat.toENNReal_mul,
      ENat.toENNReal_coe]
    rfl

/-- Corollary 4.2: expected Jacobian evaluations obey the same stopped
transition bound. -/
theorem expectedJacobianEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (jacobianEvaluationCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((2 * K : ℕ) : ℝ) / (1 - confidence)) := by
  convert expectedChargedTotalIterations_le restart confidence_pos
      confidence_lt_one hX successProbability_lower 2 using 1
  · simp only [jacobianEvaluationCount, ENat.toENNReal_mul,
      ENat.toENNReal_coe]
    rfl

/-- Corollary 4.2: expected primal solves obey the same stopped transition
bound. -/
theorem expectedPrimalSolveCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (primalSolveCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  simpa only [primalSolveCount_eq_totalIterations] using
    expectedTotalIterations_le restart confidence_pos confidence_lt_one hX
      successProbability_lower

/-- Corollary 4.2: expected correction solves obey the same stopped transition
bound. -/
theorem expectedCorrectionSolveCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (correctionSolveCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  simpa only [correctionSolveCount_eq_totalIterations] using
    expectedTotalIterations_le restart confidence_pos confidence_lt_one hX
      successProbability_lower

/-- Corollary 4.2: expected abstract membership tests obey the same stopped
transition bound. -/
theorem expectedMembershipTestCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (membershipTestCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  simpa only [membershipTestCount_eq_totalIterations] using
    expectedTotalIterations_le restart confidence_pos confidence_lt_one hX
      successProbability_lower

/-- Corollary 4.2: the aggregate corrected SOC charge has expected value at
most `7 * K / (1 - confidence)` in the exact-real transition model. -/
theorem expectedSocOperationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (socOperationCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((7 * K : ℕ) : ℝ) / (1 - confidence)) := by
  calc
    (∫⁻ ω, (socOperationCount restart ω : ℝ≥0∞) ∂ℙ) =
        ∫⁻ ω, ((7 : ℕ∞) * totalIterations restart ω : ℝ≥0∞) ∂ℙ := by
      apply lintegral_congr
      intro ω
      rw [socOperationCount_eq_seven_mul_totalIterations,
        ENat.toENNReal_mul]
    _ ≤ ENNReal.ofReal (((7 * K : ℕ) : ℝ) / (1 - confidence)) :=
      expectedChargedTotalIterations_le restart confidence_pos
        confidence_lt_one hX successProbability_lower 7

/-- Corollary 4.2: expected stochastic-gradient work is bounded by the exact
SPIDER budget divided by the success probability. -/
theorem expectedGradientEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ ℙ (successEvent restart i)) :
    ∫⁻ ω, (gradientEvaluationCount restart ω : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ) /
        (1 - confidence)) := by
  exact expectedAccumulatedCost_le restart confidence_pos confidence_lt_one hX
    successProbability_lower restart.attemptGradientEvaluationCount
    ((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
      (SPIDER.refreshBatchSize K : ℕ) +
      2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) (by
        have hsecond : 0 <
            2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
          positivity
        exact lt_of_lt_of_le hsecond (Nat.le_add_left _ _))
    (fun i ω ↦ attemptGradientEvaluationCount_le restart i ω)

/-- Helper for Corollary 4.2: the explicitly named SOC constraint counter
is the corrected transition counter exposed above.  The shorter historical
name `constraintEvaluationCount` is retained for compatibility. -/
noncomputable abbrev correctedConstraintEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  constraintEvaluationCount restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC Jacobian counter
is the corrected transition counter exposed above. -/
noncomputable abbrev correctedJacobianEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  jacobianEvaluationCount restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC primal-solve counter
is the base-model solve count of a corrected transition. -/
noncomputable abbrev correctedPrimalSolveCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  primalSolveCount restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC correction-solve
counter records the additional linear solve in the optional correction. -/
noncomputable abbrev correctedCorrectionSolveCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  correctionSolveCount restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC aggregate counter
combines the two evaluations, two solves, and one membership test charged by
the optional second-order correction. -/
noncomputable abbrev correctedSocOperationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (ω : Ω) : ℕ∞ :=
  socOperationCount restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC constraint counter is
twice the number of active corrected transitions. -/
theorem correctedConstraintEvaluationCount_eq_two_mul_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    correctedConstraintEvaluationCount restart ω = 2 * totalIterations restart ω := by
  exact constraintEvaluationCount_eq_two_mul_totalIterations restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC Jacobian counter is
twice the number of active corrected transitions. -/
theorem correctedJacobianEvaluationCount_eq_two_mul_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    correctedJacobianEvaluationCount restart ω = 2 * totalIterations restart ω := by
  exact jacobianEvaluationCount_eq_two_mul_totalIterations restart ω

/-- Helper for Corollary 4.2: the explicitly named SOC aggregate counter is
seven times the number of active corrected transitions. -/
theorem correctedSocOperationCount_eq_seven_mul_totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (ω : Ω) :
    correctedSocOperationCount restart ω = 7 * totalIterations restart ω := by
  exact socOperationCount_eq_seven_mul_totalIterations restart ω

end StoppedSafeguardedRestart

end LALM.Correction

end
