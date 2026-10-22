/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_3_4.BatchSize

public section

open MeasureTheory

namespace SPIDER

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The SPIDER refresh period `Q = ⌈√K⌉`, represented as a positive natural. -/
noncomputable def refreshPeriod (K : ℕ) : ℕ+ :=
  (Nat.ceil (Real.sqrt K)).toPNat'

/-- For a horizon of at least two, the refresh period coerces to `⌈√K⌉`. -/
theorem refreshPeriod_coe (K : ℕ) (hK : 2 ≤ K) :
    (refreshPeriod K : ℕ) = Nat.ceil (Real.sqrt K) := by
  have hKReal : (0 : ℝ) < K := by
    positivity
  have hceil : 0 < Nat.ceil (Real.sqrt K) :=
    Nat.ceil_pos.mpr (Real.sqrt_pos.2 hKReal)
  rw [refreshPeriod, Nat.toPNat'_coe, if_pos hceil]

/-- The SPIDER refresh batch size `B = K`, represented as a positive natural. -/
def refreshBatchSize (K : ℕ) : ℕ+ :=
  K.toPNat'

/-- For a horizon of at least two, the refresh batch size coerces to `K`. -/
theorem refreshBatchSize_coe (K : ℕ) (hK : 2 ≤ K) :
    (refreshBatchSize K : ℕ) = K := by
  have hKPos : 0 < K := by
    omega
  rw [refreshBatchSize, Nat.toPNat'_coe, if_pos hKPos]

/-- The SPIDER inner batch size
`b = max 1 ⌈2 * D₁ * Lₛ ^ 2 * Q⌉` for the prescribed refresh period. -/
noncomputable def innerBatchSize
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) : ℕ+ :=
  (max 1 (Nat.ceil
    (2 * LALM.StochasticRun.errorStepConstant h params *
      oracle.meanSquareLipschitz ^ 2 * refreshPeriod K))).toPNat'

/-- The inner batch size coerces to the maximum in its defining formula. -/
theorem innerBatchSize_coe
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) :
    (innerBatchSize h oracle params K : ℕ) =
      max 1 (Nat.ceil
        (2 * LALM.StochasticRun.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 * refreshPeriod K)) := by
  have hmaxPos :
      0 < max 1 (Nat.ceil
        (2 * LALM.StochasticRun.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 * refreshPeriod K)) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  rw [innerBatchSize, Nat.toPNat'_coe, if_pos hmaxPos]

/-- The prescribed inner batch size satisfies the condition used by the
stochastic NR-LALM mean-square bounds. -/
theorem innerBatchSize_isSufficient
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) :
    IsSufficientInnerBatchSize h oracle params (refreshPeriod K)
      (innerBatchSize h oracle params K) := by
  rw [isSufficientInnerBatchSize_iff, innerBatchSize_coe]
  let threshold : ℝ :=
    2 * LALM.StochasticRun.errorStepConstant h params *
      oracle.meanSquareLipschitz ^ 2 * refreshPeriod K
  have hceil : threshold ≤ (Nat.ceil threshold : ℝ) :=
    Nat.le_ceil threshold
  have hceilMaxNat :
      Nat.ceil threshold ≤ max 1 (Nat.ceil threshold) :=
    le_max_right _ _
  have hceilMax :
      (Nat.ceil threshold : ℝ) ≤ (max 1 (Nat.ceil threshold) : ℕ) := by
    exact_mod_cast hceilMaxNat
  calc
    2 * LALM.StochasticRun.errorStepConstant h params *
        (refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 = threshold := by
      dsimp only [threshold]
      ring
    _ ≤ (Nat.ceil threshold : ℝ) := hceil
    _ ≤ (max 1 (Nat.ceil threshold) : ℕ) := hceilMax

/-- A stochastic NR-LALM run using the prescribed horizon-dependent SPIDER
refresh period and batch sizes. -/
abbrev ScheduledRun
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) :=
  LALM.StochasticRun h oracle ℙ x₀ multiplier₀ params
    (refreshPeriod K) (refreshBatchSize K) (innerBatchSize h oracle params K)

end SPIDER

end
