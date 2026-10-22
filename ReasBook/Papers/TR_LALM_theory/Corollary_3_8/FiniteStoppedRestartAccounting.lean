/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.Order.Floor.Div
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartProbability
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartProbability

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.FiniteStopped.StoppedSafeguardedRestart

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

/-- Corollary 3.8: accumulate the finite costs of all attempted runs, with
infinite cost on the nontermination branch. -/
noncomputable def accumulatedCost
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (cost : ℕ → Ω → ℕ) (omega : Ω) : ℕ∞ :=
  if hcount : attemptCount restart omega = ⊤ then ⊤
  else
    (∑ i ∈ Finset.range ((attemptCount restart omega).untop hcount),
      cost i omega : ℕ)

/-- Helper for Corollary 3.8: a positive uniform per-attempt budget controls
the accumulated extended-natural cost. -/
theorem accumulatedCost_le_attemptCount_mul
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (cost : ℕ → Ω → ℕ) (omega : Ω) (budget : ℕ)
    (hbudget : 0 < budget) (hcost : ∀ i, cost i omega ≤ budget) :
    accumulatedCost restart cost omega ≤ attemptCount restart omega * budget := by
  cases hcount : attemptCount restart omega using ENat.recTopCoe with
  | top =>
      have hbudgetNe : (budget : ℕ∞) ≠ 0 := by
        exact_mod_cast hbudget.ne'
      simp only [accumulatedCost, hcount, ↓reduceDIte, ENat.top_mul',
        hbudgetNe, if_false, le_rfl]
  | coe count =>
      have hsum :
          ∑ i ∈ Finset.range count, cost i omega ≤ count * budget := by
        calc
          ∑ i ∈ Finset.range count, cost i omega ≤
              ∑ _i ∈ Finset.range count, budget :=
            Finset.sum_le_sum fun i _hi ↦ hcost i
          _ = count * budget := by
            simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      simp only [accumulatedCost, hcount, ENat.coe_ne_top, ↓reduceDIte]
      exact_mod_cast hsum

/-- Corollary 3.8: total active transitions across all finite attempts. -/
noncomputable def totalIterations
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ :=
  accumulatedCost restart restart.attemptIterations omega

/-- Corollary 3.8: total active transitions are bounded by the horizon times
the number of attempted runs. -/
theorem totalIterations_le_attemptCount_mul
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    totalIterations restart omega ≤ attemptCount restart omega * K := by
  exact accumulatedCost_le_attemptCount_mul restart restart.attemptIterations
    omega K (by omega) (fun i ↦ attemptIterations_le restart i omega)

/-- Helper for Corollary 3.8: at most `K ⌈/⌉ q` indices in a prefix of length
at most `K` are refresh indices. -/
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
      exact lt_of_lt_of_le
        (lt_of_lt_of_le (Finset.mem_range.mp hk'.1) hLK) hKq
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

/-- Corollary 3.8: the stochastic-gradient count of one finite stopped
attempt, with one refresh batch or two recursive batches per active index. -/
noncomputable def attemptGradientEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : ℕ :=
  ∑ k ∈ StoppedAttempt.executedIndexSet (restart.attempt i) omega,
    if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
      (SPIDER.refreshBatchSize K : ℕ)
    else 2 * (SPIDER.innerBatchSize h oracle params K : ℕ)

/-- Corollary 3.8: one finite attempt is bounded by the exact TeX SPIDER
budget `⌈K/Q⌉ B + 2 K b`. -/
theorem attemptGradientEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) :
    attemptGradientEvaluationCount restart i omega ≤
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
  have hq : 0 < (SPIDER.refreshPeriod K : ℕ) :=
    (SPIDER.refreshPeriod K).pos
  let S := StoppedAttempt.executedIndexSet (restart.attempt i) omega
  have hS : S ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr ((StoppedAttempt.mem_executedIndexSet_iff
      (restart.attempt i) omega k).mp hk).1
  have hrefreshS :
      (S.filter (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card ≤
        K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ) := by
    have hfilter :
        S.filter (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0) ⊆
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
        else 2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) ≤
        ∑ k ∈ S,
          ((if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
              (SPIDER.refreshBatchSize K : ℕ) else 0) +
            2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      apply Finset.sum_le_sum
      intro k hk
      split <;> omega
    _ = (S.filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card *
          (SPIDER.refreshBatchSize K : ℕ) +
        S.card * (2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        K * (2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) :=
      add_le_add (Nat.mul_le_mul_right _ hrefreshS)
        (Nat.mul_le_mul_right _ hScard)
    _ = (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by ring

/-- Corollary 3.8: total stochastic-gradient evaluations over all finite
attempts. -/
noncomputable def gradientEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ :=
  accumulatedCost restart restart.attemptGradientEvaluationCount omega

/-- Corollary 3.8: total stochastic-gradient work is at most the one-attempt
SPIDER budget times the attempt count. -/
theorem gradientEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    gradientEvaluationCount restart omega ≤ attemptCount restart omega *
      ((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
  have hbudget : 0 <
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
    have hsecond : 0 <
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
      positivity
    exact lt_of_lt_of_le hsecond (Nat.le_add_left _ _)
  exact accumulatedCost_le_attemptCount_mul restart
    restart.attemptGradientEvaluationCount omega _ hbudget
    (fun i ↦ attemptGradientEvaluationCount_le restart i omega)

/-- Corollary 3.8: one logical constraint evaluation is charged per active
base transition. -/
noncomputable def constraintEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ := totalIterations restart omega

/-- Corollary 3.8: one logical Jacobian evaluation is charged per active base
transition. -/
noncomputable def jacobianEvaluationCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ := totalIterations restart omega

/-- Corollary 3.8: one exact base linear-system solve is charged per active
transition. -/
noncomputable def linearSystemSolveCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ := totalIterations restart omega

/-- Corollary 3.8: the exact-real model charges one localization membership
test per active transition. -/
noncomputable def membershipTestCount
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) : ℕ∞ := totalIterations restart omega

/-- Helper for Corollary 3.8: a pointwise finite cost bound transfers to an
expected `ENNReal` work bound. -/
theorem expectedAccumulatedCost_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i))
    (cost : ℕ → Ω → ℕ) (budget : ℕ) (hbudget : 0 < budget)
    (hcost : ∀ i omega, cost i omega ≤ budget) :
    ∫⁻ omega, (accumulatedCost restart cost omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
  have hpointwise (omega : Ω) :
      accumulatedCost restart cost omega ≤ attemptCount restart omega * budget :=
    accumulatedCost_le_attemptCount_mul restart cost omega budget hbudget
      (fun i ↦ hcost i omega)
  have hcoerced (omega : Ω) :
      (accumulatedCost restart cost omega : ℝ≥0∞) ≤
        (attemptCount restart omega : ℝ≥0∞) * budget := by
    simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
      ENat.toENNReal_mono (hpointwise omega)
  calc
    (∫⁻ omega, (accumulatedCost restart cost omega : ℝ≥0∞) ∂P) ≤
        ∫⁻ omega, (attemptCount restart omega : ℝ≥0∞) * budget ∂P :=
      lintegral_mono hcoerced
    _ = (∫⁻ omega, (attemptCount restart omega : ℝ≥0∞) ∂P) * budget := by
      rw [lintegral_mul_const']
      exact ENNReal.natCast_ne_top budget
    _ ≤ ENNReal.ofReal (1 / (1 - confidence)) * budget := by
      exact mul_le_mul_left
        (expectedAttemptCount_le restart confidence_pos confidence_lt_one
          successProbability_lower) budget
    _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
      have hden : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
      calc
        ENNReal.ofReal (1 / (1 - confidence)) * budget =
            ENNReal.ofReal (1 / (1 - confidence)) *
              ENNReal.ofReal (budget : ℝ) := by rw [ENNReal.ofReal_natCast]
        _ = ENNReal.ofReal
            ((1 / (1 - confidence)) * (budget : ℝ)) :=
          (ENNReal.ofReal_mul (one_div_nonneg.mpr hden.le)).symm
        _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
          rw [one_div, div_eq_mul_inv, mul_comm]

/-- Corollary 3.8: expected active transitions are bounded by
`K / (1 - confidence)`. -/
theorem expectedTotalIterations_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (totalIterations restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  exact expectedAccumulatedCost_le restart confidence_pos confidence_lt_one
    successProbability_lower restart.attemptIterations K (by omega)
    (fun i omega ↦ attemptIterations_le restart i omega)

/-- Corollary 3.8: expected stochastic-gradient work satisfies the exact
restart bound from the article. -/
theorem expectedGradientEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (gradientEvaluationCount restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ) /
        (1 - confidence)) := by
  exact expectedAccumulatedCost_le restart confidence_pos confidence_lt_one
    successProbability_lower restart.attemptGradientEvaluationCount
    ((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
      (SPIDER.refreshBatchSize K : ℕ) +
      2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ)) (by
        have hsecond : 0 <
            2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
          positivity
        exact lt_of_lt_of_le hsecond (Nat.le_add_left _ _))
    (fun i omega ↦ attemptGradientEvaluationCount_le restart i omega)

/-- Corollary 3.8: expected deterministic constraint evaluations are
`O(K / (1 - confidence))` in the one-per-transition charge model. -/
theorem expectedConstraintEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (constraintEvaluationCount restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  exact expectedTotalIterations_le restart confidence_pos confidence_lt_one
    successProbability_lower

/-- Corollary 3.8: expected deterministic Jacobian evaluations are bounded by
the same base transition count. -/
theorem expectedJacobianEvaluationCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (jacobianEvaluationCount restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  exact expectedTotalIterations_le restart confidence_pos confidence_lt_one
    successProbability_lower

/-- Corollary 3.8: expected exact base linear-system solves are bounded by the
same base transition count. -/
theorem expectedLinearSystemSolveCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (linearSystemSolveCount restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  exact expectedTotalIterations_le restart confidence_pos confidence_lt_one
    successProbability_lower

/-- Corollary 3.8: expected exact localization membership tests are bounded
by the same base transition count. -/
theorem expectedMembershipTestCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (membershipTestCount restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  exact expectedTotalIterations_le restart confidence_pos confidence_lt_one
    successProbability_lower

end LALM.FiniteStopped.StoppedSafeguardedRestart

end
