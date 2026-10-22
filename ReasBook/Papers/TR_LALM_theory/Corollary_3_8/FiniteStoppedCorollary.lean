/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalRestart
public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidual
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalRestart
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidual

public section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace LALM.FiniteStopped.CanonicalFiniteStoppedCorollary

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}

/-- Corollary 3.8: the confidence-adjusted horizon obtained by rounding the
article threshold upward. -/
@[expose] noncomputable def iterationBudget
    (confidence : ℝ) (ε : ℝ≥0) : ℕ :=
  Nat.ceil
      (LALM.StochasticRun.complexityConstant h oracle params *
        (ε : ℝ)⁻¹ ^ 2 / (1 - confidence)) +
    2

/-- Helper for Corollary 3.8: the confidence-adjusted horizon is at least two. -/
theorem iterationBudget_ge_two (confidence : ℝ) (ε : ℝ≥0) :
    2 ≤ iterationBudget (h := h) (oracle := oracle) (params := params)
      confidence ε := by
  unfold iterationBudget
  omega

/-- Corollary 3.8: the rounded confidence-adjusted horizon satisfies the exact
residual threshold required for a stochastic `ε`-KKT pair. -/
theorem iterationBudget_spec
    (confidence : ℝ) (confidence_lt_one : confidence < 1) (ε : ℝ≥0) :
    LALM.StochasticRun.complexityConstant h oracle params *
        (ε : ℝ)⁻¹ ^ 2 ≤
      (1 - confidence) *
        ((iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε : ℝ) - 1) := by
  let argument :=
    LALM.StochasticRun.complexityConstant h oracle params *
      (ε : ℝ)⁻¹ ^ 2 / (1 - confidence)
  have hdenominator : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hceil : argument ≤ (Nat.ceil argument : ℝ) := Nat.le_ceil argument
  have hscaled :
      LALM.StochasticRun.complexityConstant h oracle params *
          (ε : ℝ)⁻¹ ^ 2 ≤
        (1 - confidence) * (Nat.ceil argument : ℝ) := by
    have hscaled' := (div_le_iff₀ hdenominator).mp
      (show LALM.StochasticRun.complexityConstant h oracle params *
          (ε : ℝ)⁻¹ ^ 2 / (1 - confidence) ≤
        (Nat.ceil argument : ℝ) by
        simpa only [argument] using hceil)
    simpa only [mul_comm] using hscaled'
  have hceilBudget : (Nat.ceil argument : ℝ) ≤
      (iterationBudget (h := h) (oracle := oracle) (params := params)
        confidence ε : ℝ) - 1 := by
    rw [iterationBudget]
    push_cast
    linarith
  exact hscaled.trans
    (mul_le_mul_of_nonneg_left hceilBudget hdenominator.le)

/-- Corollary 3.8: the explicit independent finite stopped restart used by
the theorem. -/
noncomputable def restart
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  canonicalFiniteStoppedSafeguardedRestart confidence K hK X hX
    initial_mem h_region

/-- Corollary 3.8: attach the canonical finite analytic certificate to every
coordinate of the explicit restart. -/
noncomputable def certifiedRestart
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  CertifiedStoppedSafeguardedRestart.canonical
    (restart confidence K hK X hX initial_mem h_region)
    confidence_pos confidence_lt_one

/-- Corollary 3.8: the explicit independent restart at the rounded
confidence-adjusted horizon. -/
noncomputable def epsilonRestart
    (confidence : ℝ) (ε : ℝ≥0)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    StoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := canonicalStoppedRestartMeasure ν
        (iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε)
        (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
          confidence ε))
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence)
      (K := iterationBudget (h := h) (oracle := oracle) (params := params)
        confidence ε)
      (hK := iterationBudget_ge_two (h := h) (oracle := oracle)
        (params := params) confidence ε)
      (X := X) :=
  restart confidence
    (iterationBudget (h := h) (oracle := oracle) (params := params)
      confidence ε)
    (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
      confidence ε)
    X hX initial_mem h_region

/-- Corollary 3.8: the explicit independent finite stopped restart terminates
almost surely. -/
theorem terminatesAE
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∀ᵐ omega ∂canonicalStoppedRestartMeasure ν K hK,
      StoppedSafeguardedRestart.firstAccepted
        (restart confidence K hK X hX initial_mem h_region) omega ≠ ⊤ := by
  exact (certifiedRestart confidence K hK X hX initial_mem h_region
    confidence_pos confidence_lt_one).terminatesAE
      confidence_pos confidence_lt_one

/-- Corollary 3.8: the explicit restart has expected attempt count at most
`1 / (1 - confidence)`. -/
theorem expectedAttemptCount_le
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    (∫⁻ omega,
      (StoppedSafeguardedRestart.attemptCount
        (restart confidence K hK X hX initial_mem h_region) omega : ℝ≥0∞)
      ∂canonicalStoppedRestartMeasure ν K hK) ≤
      ENNReal.ofReal (1 / (1 - confidence)) := by
  exact (certifiedRestart confidence K hK X hX initial_mem h_region
    confidence_pos confidence_lt_one).expectedAttemptCount_le
      confidence_pos confidence_lt_one

/-- Corollary 3.8: the returned pair of the explicit restart satisfies the
article's mean-square residual bound. -/
theorem residualMeanSquare_le
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    finiteStoppedResidualMeanSquare
        (restart confidence K hK X hX initial_mem h_region) ≤
      ENNReal.ofReal
        (LALM.StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
  exact CertifiedStoppedSafeguardedRestart.finiteStoppedResidualMeanSquare_le_tex
    (restart confidence K hK X hX initial_mem h_region)
    confidence_pos confidence_lt_one

/-- Corollary 3.8: the explicit restart satisfies the exact expected SPIDER
gradient-work bound. -/
theorem expectedGradientEvaluationCount_le
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    (∫⁻ omega,
      (StoppedSafeguardedRestart.gradientEvaluationCount
        (restart confidence K hK X hX initial_mem h_region) omega : ℝ≥0∞)
      ∂canonicalStoppedRestartMeasure ν K hK) ≤
      ENNReal.ofReal ((
        (((K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ)) /
        (1 - confidence)) := by
  exact (certifiedRestart confidence K hK X hX initial_mem h_region
    confidence_pos confidence_lt_one).expectedGradientEvaluationCount_le
      confidence_pos confidence_lt_one

/-- Corollary 3.8: each deterministic transition counter of the explicit
restart has expected value at most `K / (1 - confidence)`. -/
theorem expectedDeterministicCounts_le
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    (∫⁻ omega,
      (StoppedSafeguardedRestart.constraintEvaluationCount
        (restart confidence K hK X hX initial_mem h_region) omega : ℝ≥0∞)
      ∂canonicalStoppedRestartMeasure ν K hK) ≤
        ENNReal.ofReal ((K : ℝ) / (1 - confidence)) ∧
    (∫⁻ omega,
      (StoppedSafeguardedRestart.jacobianEvaluationCount
        (restart confidence K hK X hX initial_mem h_region) omega : ℝ≥0∞)
      ∂canonicalStoppedRestartMeasure ν K hK) ≤
        ENNReal.ofReal ((K : ℝ) / (1 - confidence)) ∧
    (∫⁻ omega,
      (StoppedSafeguardedRestart.linearSystemSolveCount
        (restart confidence K hK X hX initial_mem h_region) omega : ℝ≥0∞)
      ∂canonicalStoppedRestartMeasure ν K hK) ≤
        ENNReal.ofReal ((K : ℝ) / (1 - confidence)) ∧
    (∫⁻ omega,
      (StoppedSafeguardedRestart.membershipTestCount
        (restart confidence K hK X hX initial_mem h_region) omega : ℝ≥0∞)
      ∂canonicalStoppedRestartMeasure ν K hK) ≤
        ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  let certified := certifiedRestart confidence K hK X hX initial_mem h_region
    confidence_pos confidence_lt_one
  exact ⟨certified.expectedConstraintEvaluationCount_le
      confidence_pos confidence_lt_one,
    certified.expectedJacobianEvaluationCount_le
      confidence_pos confidence_lt_one,
    certified.expectedLinearSystemSolveCount_le
      confidence_pos confidence_lt_one,
    certified.expectedMembershipTestCount_le
      confidence_pos confidence_lt_one⟩

/-- Corollary 3.8: at the article iteration threshold, the output of the
explicit independent finite stopped restart is stochastic `ε`-KKT. -/
theorem isApproximatePair_of_iterationBound
    (confidence : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      LALM.StochasticRun.complexityConstant h oracle params *
          (ε : ℝ)⁻¹ ^ 2 ≤
        (1 - confidence) * ((K : ℝ) - 1)) :
    KKT.Stochastic.IsApproximatePair
      (canonicalStoppedRestartMeasure ν K hK) f c ε
      (StoppedSafeguardedRestart.returnedPoint
        (restart confidence K hK X hX initial_mem h_region))
      (StoppedSafeguardedRestart.returnedMultiplier
        (restart confidence K hK X hX initial_mem h_region)) := by
  exact CertifiedStoppedSafeguardedRestart.isApproximatePair_of_iterationBound
    (restart confidence K hK X hX initial_mem h_region)
    confidence_pos confidence_lt_one ε ε_pos h_iterations

/-- Corollary 3.8: the rounded confidence-adjusted horizon automatically
produces a stochastic `ε`-KKT pair. -/
theorem epsilonRestart_isApproximatePair
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (ε : ℝ≥0) (ε_pos : 0 < ε) :
    KKT.Stochastic.IsApproximatePair
      (canonicalStoppedRestartMeasure ν
        (iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε)
        (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
          confidence ε)) f c ε
      (StoppedSafeguardedRestart.returnedPoint
        (epsilonRestart confidence ε X hX initial_mem h_region))
      (StoppedSafeguardedRestart.returnedMultiplier
        (epsilonRestart confidence ε X hX initial_mem h_region)) := by
  simpa only [epsilonRestart] using
    isApproximatePair_of_iterationBound confidence
      (iterationBudget (h := h) (oracle := oracle) (params := params)
        confidence ε)
      (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
        confidence ε)
      X hX initial_mem h_region confidence_pos confidence_lt_one ε ε_pos
      (iterationBudget_spec (h := h) (oracle := oracle) (params := params)
        confidence confidence_lt_one ε)

/-- Helper for Corollary 3.8: a natural ceiling of a fixed multiple of
`ε⁻²`, with fixed additive overhead, is `O(ε⁻²)` as `ε → 0⁺`. -/
private lemma natCeilQuadraticBudget_isBigO (C : ℝ) :
    (fun ε : ℝ≥0 ↦ ((Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) + 2 : ℕ) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  refine Asymptotics.IsBigO.of_bound (|C| + 3) ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hinverse : 1 ≤ (ε : ℝ)⁻¹ := (one_le_inv₀ hεreal).2 hεrealOne
  have hinverseSq : 1 ≤ (ε : ℝ)⁻¹ ^ 2 := by nlinarith
  have hinverseSqNonneg : 0 ≤ (ε : ℝ)⁻¹ ^ 2 := sq_nonneg _
  by_cases hC : 0 ≤ C
  · have hargument : 0 ≤ C * (ε : ℝ)⁻¹ ^ 2 :=
      mul_nonneg hC hinverseSqNonneg
    have hceiling := Nat.ceil_lt_add_one hargument
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_add,
      Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg,
      abs_of_nonneg hC]
    have hcoefficient : 0 ≤ C + 3 := by positivity
    nlinarith [mul_nonneg hcoefficient (sub_nonneg.mpr hinverseSq)]
  · have hargument : C * (ε : ℝ)⁻¹ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hinverseSqNonneg
    have hceiling : Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) = 0 :=
      Nat.ceil_eq_zero.mpr hargument
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    rw [hceiling, Nat.zero_add, Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg htwo, Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg]
    have hcoefficient : 0 ≤ |C| + 3 := by positivity
    calc
      (2 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      _ = (|C| + 3) * 1 := (mul_one _).symm
      _ ≤ (|C| + 3) * (ε : ℝ)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hinverseSq hcoefficient

omit [IsProbabilityMeasure ν] in
/-- Helper for Corollary 3.8: an ENNReal expected-cost bound transfers a real
Big-O estimate from its nonnegative deterministic majorant. -/
private lemma expectedCost_isBigO_of_bound
    (cost : ℝ≥0 → CanonicalStoppedRestartSampleSpace Ξ → ℕ∞)
    (mu : ℝ≥0 → Measure (CanonicalStoppedRestartSampleSpace Ξ))
    (bound rate : ℝ≥0 → ℝ) (hboundNonneg : ∀ ε, 0 ≤ bound ε)
    (hcost : ∀ ε, ∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂mu ε ≤
      ENNReal.ofReal (bound ε))
    (hboundBigO : bound =O[nhdsWithin 0 (Set.Ioi 0)] rate) :
    (fun ε ↦ ENNReal.toReal
      (∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂mu ε))
      =O[nhdsWithin 0 (Set.Ioi 0)] rate := by
  have hdomination :
      (fun ε ↦ ENNReal.toReal
        (∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂mu ε))
        =O[nhdsWithin 0 (Set.Ioi 0)] bound :=
    Asymptotics.isBigO_of_le _ fun ε ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        Real.norm_eq_abs, abs_of_nonneg (hboundNonneg ε)]
      exact ENNReal.toReal_le_of_le_ofReal (hboundNonneg ε) (hcost ε)
  exact hdomination.trans hboundBigO

/-- Corollary 3.8: the confidence-adjusted finite horizon is `O(ε⁻²)`. -/
theorem iterationBudget_isBigO
    (confidence : ℝ) :
    (fun ε : ℝ≥0 ↦
      (iterationBudget (h := h) (oracle := oracle) (params := params)
        confidence ε : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  simpa only [iterationBudget, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    natCeilQuadraticBudget_isBigO
      (LALM.StochasticRun.complexityConstant h oracle params /
        (1 - confidence))

/- The following small schedule lemmas provide the interface needed to lift the
   exact one-attempt SPIDER count to its asymptotic form. -/

/-- Helper for Corollary 3.8: the finite refresh period squares cover its
iteration horizon. -/
private lemma finiteIteration_le_refreshPeriod_sq (K : ℕ) (hK : 2 ≤ K) :
    K ≤ (SPIDER.refreshPeriod K : ℕ) * (SPIDER.refreshPeriod K : ℕ) := by
  have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
  have hsqrtSquare := Real.sq_sqrt (Nat.cast_nonneg K)
  have hsqrtCeil := Nat.le_ceil (Real.sqrt K)
  have hceilNonneg :
      (0 : ℝ) ≤ (Nat.ceil (Real.sqrt K) : ℝ) := Nat.cast_nonneg _
  have hreal :
      (K : ℝ) ≤ (Nat.ceil (Real.sqrt K) : ℝ) * Nat.ceil (Real.sqrt K) := by
    nlinarith
  rw [SPIDER.refreshPeriod_coe K hK]
  exact_mod_cast hreal

/-- Helper for Corollary 3.8: the finite refresh period is bounded by one plus
the square root of the horizon. -/
private lemma finiteRefreshPeriod_le_sqrt_add_one (K : ℕ) (hK : 2 ≤ K) :
    ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := by
  rw [SPIDER.refreshPeriod_coe K hK]
  exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg (K : ℝ))).le

/-- Helper for Corollary 3.8: the finite SPIDER inner batch is bounded by a
linear function of the refresh period. -/
private lemma finiteInnerBatchSize_le_linear
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) :
    ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
      2 * LALM.StochasticRun.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 * (SPIDER.refreshPeriod K : ℕ) + 1 := by
  let A : ℝ :=
    2 * LALM.StochasticRun.errorStepConstant h params *
      oracle.meanSquareLipschitz ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [LALM.FiniteStopped.StoppedAttemptAnalysis.errorStepConstant_pos
      h params]
  have hargument :
      0 ≤ A * (SPIDER.refreshPeriod K : ℕ) :=
    mul_nonneg hA (Nat.cast_nonneg _)
  have hceiling := Nat.ceil_lt_add_one hargument
  have honeLe :
      (1 : ℝ) ≤ A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
    linarith
  rw [SPIDER.innerBatchSize_coe, Nat.cast_max]
  apply max_le
  · simpa only [A, Nat.cast_one] using honeLe
  · dsimp only [A] at hceiling ⊢
    exact hceiling.le

/-- Helper for Corollary 3.8: when `K ≥ 2`, the ceiling-divided refresh count
is no larger than the refresh period itself. -/
private lemma finiteCeilDiv_le_refreshPeriod (K : ℕ) (hK : 2 ≤ K) :
    K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ) ≤
      (SPIDER.refreshPeriod K : ℕ) := by
  have hq : 0 < (SPIDER.refreshPeriod K : ℕ) :=
    (SPIDER.refreshPeriod K).pos
  exact (ceilDiv_le_iff_le_mul hq).2
    (finiteIteration_le_refreshPeriod_sq K hK)

/-- Helper for Corollary 3.8: the exact finite stopped SPIDER one-attempt
budget is `O(ε⁻³)` under the rounded `O(ε⁻²)` horizon. -/
private lemma finiteGradientBudget_isBigO (confidence : ℝ) :
    (fun ε : ℝ≥0 ↦
      (((
        (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε ⌈/⌉
          (SPIDER.refreshPeriod (iterationBudget (h := h) (oracle := oracle)
            (params := params) confidence ε) : ℕ)) *
            (SPIDER.refreshBatchSize
              (iterationBudget (h := h) (oracle := oracle) (params := params)
                confidence ε) : ℕ) +
          2 * iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε *
            (SPIDER.innerBatchSize h oracle params
              (iterationBudget (h := h) (oracle := oracle) (params := params)
                confidence ε) : ℕ) : ℕ) : ℝ)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
  let C : ℝ :=
    LALM.StochasticRun.complexityConstant h oracle params / (1 - confidence)
  let D : ℝ := |C| + 3
  let A : ℝ :=
    2 * LALM.StochasticRun.errorStepConstant h params *
      oracle.meanSquareLipschitz ^ 2
  let M : ℝ := D * ((D + 1) + 2 * (A * (D + 1) + 1))
  refine Asymptotics.IsBigO.of_bound M ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  let x : ℝ := (ε : ℝ)⁻¹
  let K : ℕ := iterationBudget (h := h) (oracle := oracle)
    (params := params) confidence ε
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact (one_le_inv₀ hεreal).2 hεrealOne
  have hxNonneg : 0 ≤ x := le_trans zero_le_one hx
  have hxSq : 1 ≤ x ^ 2 := by nlinarith
  have hxSqNonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [abs_nonneg C]
  have hDNonneg : 0 ≤ D := le_trans zero_le_one hD
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [LALM.FiniteStopped.StoppedAttemptAnalysis.errorStepConstant_pos
      h params]
  have hK : 2 ≤ K := by
    dsimp only [K]
    exact iterationBudget_ge_two (h := h) (oracle := oracle)
      (params := params) confidence ε
  have hKNonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hKBound : (K : ℝ) ≤ D * x ^ 2 := by
    dsimp only [K]
    rw [iterationBudget]
    by_cases hC : 0 ≤ C
    · have hargument : 0 ≤ C * x ^ 2 := mul_nonneg hC hxSqNonneg
      have hceiling := Nat.ceil_lt_add_one hargument
      have hCplus : 0 ≤ C + 3 := by positivity
      have hargEq :
          LALM.StochasticRun.complexityConstant h oracle params *
              (ε : ℝ)⁻¹ ^ 2 / (1 - confidence) = C * x ^ 2 := by
        dsimp only [C, x]
        ring
      have hceiling' :
          (Nat.ceil
              (LALM.StochasticRun.complexityConstant h oracle params *
                (ε : ℝ)⁻¹ ^ 2 / (1 - confidence)) : ℝ) <
            C * x ^ 2 + 1 := by
        rw [hargEq]
        exact hceiling
      rw [Nat.cast_add, Nat.cast_ofNat]
      dsimp only [D]
      rw [abs_of_nonneg hC]
      nlinarith [hceiling', mul_nonneg hCplus (sub_nonneg.mpr hxSq)]
    · have hargument : C * x ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hxSqNonneg
      have hceiling : Nat.ceil (C * x ^ 2) = 0 :=
        Nat.ceil_eq_zero.mpr hargument
      have hargEq :
          LALM.StochasticRun.complexityConstant h oracle params *
              (ε : ℝ)⁻¹ ^ 2 / (1 - confidence) = C * x ^ 2 := by
        dsimp only [C, x]
        ring
      have hceiling' :
          Nat.ceil
              (LALM.StochasticRun.complexityConstant h oracle params *
                (ε : ℝ)⁻¹ ^ 2 / (1 - confidence)) = 0 := by
        rw [hargEq]
        exact hceiling
      rw [hceiling', Nat.zero_add, Nat.cast_ofNat]
      dsimp only [D]
      have hcoefficient : 0 ≤ |C| + 3 := by positivity
      have hthree : (3 : ℝ) ≤ |C| + 3 := by
        linarith [abs_nonneg C]
      have hproduct : (3 : ℝ) * 1 ≤ (|C| + 3) * x ^ 2 :=
        mul_le_mul hthree hxSq zero_le_one hcoefficient
      nlinarith
  have hrefreshRaw := finiteRefreshPeriod_le_sqrt_add_one K hK
  have hDsq : D ≤ D ^ 2 := by nlinarith
  have hKSquare : (K : ℝ) ≤ (D * x) ^ 2 := by
    calc
      (K : ℝ) ≤ D * x ^ 2 := hKBound
      _ ≤ D ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hDsq hxSqNonneg
      _ = (D * x) ^ 2 := by ring
  have hsqrtK : Real.sqrt K ≤ D * x := by
    have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
    have hsqrtSquare := Real.sq_sqrt hKNonneg
    have hDxNonneg : 0 ≤ D * x := mul_nonneg hDNonneg hxNonneg
    nlinarith
  have hrefreshBound :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ (D + 1) * x := by
    calc
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := hrefreshRaw
      _ ≤ D * x + 1 := by
        simpa only [add_comm] using add_le_add_right hsqrtK 1
      _ ≤ (D + 1) * x := by nlinarith
  have hinnerRaw := finiteInnerBatchSize_le_linear h oracle params K
  have hinnerBound :
      ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
        (A * (D + 1) + 1) * x := by
    calc
      ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
          A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
        simpa only [A] using hinnerRaw
      _ ≤ A * ((D + 1) * x) + 1 := by
        gcongr
      _ ≤ (A * (D + 1) + 1) * x := by
        nlinarith [mul_nonneg hA (add_nonneg hDNonneg zero_le_one)]
  have hceilDiv := finiteCeilDiv_le_refreshPeriod K hK
  have hcountNat :
      (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
          (SPIDER.refreshBatchSize K : ℕ) +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) ≤
      (SPIDER.refreshPeriod K : ℕ) * K +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
    rw [SPIDER.refreshBatchSize_coe K hK]
    exact add_le_add (Nat.mul_le_mul_right K hceilDiv) le_rfl
  have hcountReal :
      (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ)) ≤
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
    exact_mod_cast hcountNat
  have hrefreshNonneg :
      0 ≤ ((SPIDER.refreshPeriod K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hinnerNonneg :
      0 ≤ ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hrefreshWork :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K ≤
        ((D + 1) * x) * (D * x ^ 2) := by
    exact mul_le_mul hrefreshBound hKBound hKNonneg
      (mul_nonneg (add_nonneg hDNonneg zero_le_one) hxNonneg)
  have hinnerCoefficientNonneg : 0 ≤ A * (D + 1) + 1 := by positivity
  have hinnerWork :
      (2 : ℝ) * K * (SPIDER.innerBatchSize h oracle params K : ℕ) ≤
        2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) := by
    gcongr
  have hcountBound :
      (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ)) ≤
      M * x ^ 3 := by
    calc
      (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ)) ≤
          ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
            2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := hcountReal
      _ ≤ ((D + 1) * x) * (D * x ^ 2) +
          2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) :=
        add_le_add hrefreshWork hinnerWork
      _ = M * x ^ 3 := by
        dsimp only [M]
        ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxNonneg 3)]
  simpa only [K, x] using hcountBound

/-- Corollary 3.8: expected total active transitions of the rounded canonical
restart are `O(ε⁻²)` for fixed confidence. -/
theorem expectedTotalIterations_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega,
        (StoppedSafeguardedRestart.totalIterations
          (epsilonRestart confidence ε X hX initial_mem h_region) omega : ℝ≥0∞)
        ∂canonicalStoppedRestartMeasure ν
          (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε)
          (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
            confidence ε)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  let bound : ℝ≥0 → ℝ := fun ε ↦
    (iterationBudget (h := h) (oracle := oracle) (params := params)
      confidence ε : ℝ) / (1 - confidence)
  have hboundNonneg (ε : ℝ≥0) : 0 ≤ bound ε := by
    dsimp only [bound]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr confidence_lt_one).le
  have hboundBigO :
      bound =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2) := by
    have hscaled := (iterationBudget_isBigO (h := h) (oracle := oracle)
      (params := params) confidence).const_mul_left
      ((1 - confidence)⁻¹)
    simpa only [bound, div_eq_mul_inv, mul_comm] using hscaled
  let cost : ℝ≥0 → CanonicalStoppedRestartSampleSpace Ξ → ℕ∞ := fun ε omega ↦
    StoppedSafeguardedRestart.totalIterations
      (epsilonRestart confidence ε X hX initial_mem h_region) omega
  let mu : ℝ≥0 → Measure (CanonicalStoppedRestartSampleSpace Ξ) := fun ε ↦
    canonicalStoppedRestartMeasure ν
      (iterationBudget (h := h) (oracle := oracle) (params := params)
        confidence ε)
      (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
        confidence ε)
  have hcost : ∀ ε, ∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂mu ε ≤
      ENNReal.ofReal (bound ε) := by
    intro ε
    have hsuccess : ∀ i,
        ENNReal.ofReal (1 - confidence) ≤
          canonicalStoppedRestartMeasure ν
            (iterationBudget (h := h) (oracle := oracle) (params := params)
              confidence ε)
            (iterationBudget_ge_two (h := h) (oracle := oracle)
              (params := params) confidence ε)
            (StoppedSafeguardedRestart.successEvent
              (epsilonRestart confidence ε X hX initial_mem h_region) i) :=
      fun i ↦ (certifiedRestart confidence
        (iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε)
        (iterationBudget_ge_two (h := h) (oracle := oracle)
          (params := params) confidence ε)
        X hX initial_mem h_region confidence_pos confidence_lt_one).attempt_successProbability_lower i
    simpa only [cost, mu, bound, epsilonRestart] using
      (StoppedSafeguardedRestart.expectedTotalIterations_le
        (epsilonRestart confidence ε X hX initial_mem h_region)
        confidence_pos confidence_lt_one
        hsuccess)
  have hresult := expectedCost_isBigO_of_bound cost mu bound
    (fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2) hboundNonneg hcost hboundBigO
  simpa only [cost, mu] using hresult

/-- Corollary 3.8: expected stochastic-gradient evaluations of the rounded
canonical restart are `O(ε⁻³)`. -/
theorem expectedGradientEvaluationCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega,
        (StoppedSafeguardedRestart.gradientEvaluationCount
          (epsilonRestart confidence ε X hX initial_mem h_region) omega : ℝ≥0∞)
        ∂canonicalStoppedRestartMeasure ν
          (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε)
          (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
            confidence ε)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
  let bound : ℝ≥0 → ℝ := fun ε ↦
    (((
      (iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε ⌈/⌉
        (SPIDER.refreshPeriod (iterationBudget (h := h) (oracle := oracle)
          (params := params) confidence ε) : ℕ)) *
          (SPIDER.refreshBatchSize
            (iterationBudget (h := h) (oracle := oracle) (params := params)
              confidence ε) : ℕ) +
        2 * iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε *
          (SPIDER.innerBatchSize h oracle params
            (iterationBudget (h := h) (oracle := oracle) (params := params)
              confidence ε) : ℕ) : ℕ) : ℝ) / (1 - confidence))
  have hboundNonneg (ε : ℝ≥0) : 0 ≤ bound ε := by
    dsimp only [bound]
    exact div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr confidence_lt_one).le
  have hboundBigO :
      bound =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3) := by
    have hscaled := (finiteGradientBudget_isBigO
      (h := h) (oracle := oracle) (params := params) confidence).const_mul_left
      ((1 - confidence)⁻¹)
    simpa only [bound, div_eq_mul_inv, mul_comm] using hscaled
  let cost : ℝ≥0 → CanonicalStoppedRestartSampleSpace Ξ → ℕ∞ := fun ε omega ↦
    StoppedSafeguardedRestart.gradientEvaluationCount
      (epsilonRestart confidence ε X hX initial_mem h_region) omega
  let mu : ℝ≥0 → Measure (CanonicalStoppedRestartSampleSpace Ξ) := fun ε ↦
    canonicalStoppedRestartMeasure ν
      (iterationBudget (h := h) (oracle := oracle) (params := params)
        confidence ε)
      (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
        confidence ε)
  have hcost : ∀ ε, ∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂mu ε ≤
      ENNReal.ofReal (bound ε) := by
    intro ε
    have hsuccess : ∀ i,
        ENNReal.ofReal (1 - confidence) ≤
          canonicalStoppedRestartMeasure ν
            (iterationBudget (h := h) (oracle := oracle) (params := params)
              confidence ε)
            (iterationBudget_ge_two (h := h) (oracle := oracle)
              (params := params) confidence ε)
            (StoppedSafeguardedRestart.successEvent
              (epsilonRestart confidence ε X hX initial_mem h_region) i) :=
      fun i ↦ (certifiedRestart confidence
        (iterationBudget (h := h) (oracle := oracle) (params := params)
          confidence ε)
        (iterationBudget_ge_two (h := h) (oracle := oracle)
          (params := params) confidence ε)
        X hX initial_mem h_region confidence_pos confidence_lt_one).attempt_successProbability_lower i
    simpa only [cost, mu, bound, epsilonRestart] using
      (StoppedSafeguardedRestart.expectedGradientEvaluationCount_le
        (epsilonRestart confidence ε X hX initial_mem h_region)
        confidence_pos confidence_lt_one hsuccess)
  have hresult := expectedCost_isBigO_of_bound cost mu bound
    (fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3) hboundNonneg hcost hboundBigO
  simpa only [cost, mu] using hresult

/-- Corollary 3.8: expected constraint evaluations of the rounded canonical
restart are `O(ε⁻²)`. -/
theorem expectedConstraintEvaluationCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega,
        (StoppedSafeguardedRestart.constraintEvaluationCount
          (epsilonRestart confidence ε X hX initial_mem h_region) omega : ℝ≥0∞)
        ∂canonicalStoppedRestartMeasure ν
          (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε)
          (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
            confidence ε)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  simpa only [StoppedSafeguardedRestart.constraintEvaluationCount,
    StoppedSafeguardedRestart.totalIterations] using
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem h_region

/-- Corollary 3.8: expected Jacobian evaluations of the rounded canonical
restart are `O(ε⁻²)`. -/
theorem expectedJacobianEvaluationCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega,
        (StoppedSafeguardedRestart.jacobianEvaluationCount
          (epsilonRestart confidence ε X hX initial_mem h_region) omega : ℝ≥0∞)
        ∂canonicalStoppedRestartMeasure ν
          (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε)
          (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
            confidence ε)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  simpa only [StoppedSafeguardedRestart.jacobianEvaluationCount,
    StoppedSafeguardedRestart.totalIterations] using
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem h_region

/-- Corollary 3.8: expected exact linear-system solves of the rounded canonical
restart are `O(ε⁻²)`. -/
theorem expectedLinearSystemSolveCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega,
        (StoppedSafeguardedRestart.linearSystemSolveCount
          (epsilonRestart confidence ε X hX initial_mem h_region) omega : ℝ≥0∞)
        ∂canonicalStoppedRestartMeasure ν
          (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε)
          (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
            confidence ε)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  simpa only [StoppedSafeguardedRestart.linearSystemSolveCount,
    StoppedSafeguardedRestart.totalIterations] using
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem h_region

/-- Corollary 3.8: expected localization membership tests of the rounded
canonical restart are `O(ε⁻²)`. -/
theorem expectedMembershipTestCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega,
        (StoppedSafeguardedRestart.membershipTestCount
          (epsilonRestart confidence ε X hX initial_mem h_region) omega : ℝ≥0∞)
        ∂canonicalStoppedRestartMeasure ν
          (iterationBudget (h := h) (oracle := oracle) (params := params)
            confidence ε)
          (iterationBudget_ge_two (h := h) (oracle := oracle) (params := params)
            confidence ε)))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  simpa only [StoppedSafeguardedRestart.membershipTestCount,
    StoppedSafeguardedRestart.totalIterations] using
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem h_region

end LALM.FiniteStopped.CanonicalFiniteStoppedCorollary

end
