/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPrefixInvariant
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedPrefixInvariant

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.FiniteStopped.StoppedAttemptAnalysis

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
variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Theorem 3.7: the mean-square raw estimator error at a finite
stopped transition is the integral of the actual raw-error observable. -/
noncomputable def activeRawGradientErrorMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : ℝ :=
  ∫ omega, activeRawGradientErrorIntegrand attempt k omega ∂P

/-- Helper for Theorem 3.7: the mean-square clipped estimator error at a finite
stopped transition is the integral of the actual clipped-error observable. -/
noncomputable def activeGradientErrorMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : ℝ :=
  ∫ omega, activeGradientErrorIntegrand attempt k omega ∂P

/-- Helper for Theorem 3.7: the mean-square displacement at a finite stopped
transition is the integral of the actual stopped displacement observable. -/
noncomputable def activeDisplacementMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : ℝ :=
  ∫ omega, activeDisplacementIntegrand attempt k omega ∂P

/-- Helper for Theorem 3.7: the mean-square base-step energy at a finite
stopped transition is the integral of the actual stopped base-step observable. -/
noncomputable def activeBaseStepMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : ℝ :=
  ∫ omega, activeBaseStepIntegrand attempt k omega ∂P

/-- Helper for Theorem 3.7: the accumulated clipped estimator energy of a
finite stopped attempt. -/
noncomputable def stoppedGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : ℝ :=
  ∑ k ∈ Finset.range K, activeGradientErrorMeanSquare attempt k

/-- Helper for Theorem 3.7: the accumulated base-step energy of a finite
stopped attempt. -/
noncomputable def stoppedBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : ℝ :=
  ∑ k ∈ Finset.range K, activeBaseStepMeanSquare attempt k

/-- Helper for Theorem 3.7: the accumulated displacement energy of a finite
stopped attempt. -/
noncomputable def stoppedDisplacementEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : ℝ :=
  ∑ k ∈ Finset.range K, activeDisplacementMeanSquare attempt k

/-- The finite SPIDER recursion is stated directly for the observables of a
stopped attempt.  The fields are not free scalar witnesses: every bound refers
to the actual state, batch, and raw-estimate projections in `attempt`. -/
structure FiniteStoppedSPIDERRecursion
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- The raw-error observable is integrable at every charged index. -/
  raw_integrable : ∀ k, k < K →
    Integrable (activeRawGradientErrorIntegrand attempt k) P
  /-- A refresh resets the actual stopped raw-error moment to the batch-noise
  scale. -/
  refresh_bound : ∀ (k : ℕ), k < K → k % Q = 0 →
    activeRawGradientErrorMeanSquare attempt k ≤
      (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ)
  /-- A nonrefresh update bounds the actual stopped raw-error moment by the
  preceding stopped moment and the preceding displacement innovation. -/
  update_bound : ∀ (k : ℕ), k < K → 0 < k → k % Q ≠ 0 →
    activeRawGradientErrorMeanSquare attempt k ≤
      activeRawGradientErrorMeanSquare attempt (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementMeanSquare attempt (k - 1)

/-- The finite stopped energy coupling combines the canonical stopped-prefix
invariant with the actual state/batch SPIDER moment recursion. -/
structure FiniteStoppedEnergyCoupling
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- The pathwise localization and multiplier invariant for this attempt. -/
  pathInvariant : FiniteStoppedPrefixInvariant attempt
  /-- The moment recursion for the actual stopped raw-error observable. -/
  spiderRecursion : FiniteStoppedSPIDERRecursion attempt

/-- Helper for Theorem 3.7: the actual stopped clipped-error moment is bounded
by the actual stopped raw-error moment whenever the latter is integrable. -/
theorem activeGradientErrorMeanSquare_le_raw
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ)
    (hraw : Integrable (activeRawGradientErrorIntegrand attempt k) P) :
    activeGradientErrorMeanSquare attempt k ≤
      activeRawGradientErrorMeanSquare attempt k := by
  unfold activeGradientErrorMeanSquare activeRawGradientErrorMeanSquare
  exact integral_mono (integrable_activeGradientErrorIntegrand attempt k) hraw
    (activeGradientErrorIntegrand_le_activeRawGradientErrorIntegrand attempt k)

/-- Helper for Theorem 3.7: the displacement and base-step moments are equal
because the base stopped observable is defined as the endpoint displacement. -/
theorem activeDisplacementMeanSquare_eq_activeBaseStepMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    activeDisplacementMeanSquare attempt k =
      activeBaseStepMeanSquare attempt k := by
  unfold activeDisplacementMeanSquare activeBaseStepMeanSquare
  apply congrArg (fun g : Ω → ℝ ↦ ∫ omega, g omega ∂P)
  funext omega
  exact activeDisplacementIntegrand_eq_activeBaseStepIntegrand attempt k omega

/-- Helper for Theorem 3.7: a prefix invariant supplies the uniform step bound
needed by the finite energy integrability interfaces. -/
theorem norm_baseStep_le_of_prefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (k : Fin K) (omega : Ω) :
    ‖attempt.baseStep k omega‖ ≤ params.delta := by
  by_cases hactive : attempt.activeAt k.castSucc omega
  · have hkprefix : k.1 < canonicalPrefixLength attempt omega := by
      exact (activeAt_iff_lt_canonicalPrefixLength attempt omega k.1 k.isLt).mp
        hactive
    exact invariant.step_bound omega k hkprefix
  · have hfrozen := StoppedAttempt.frozen_successor_of_inactive
      attempt k omega hactive
    rw [hfrozen.2.2]
    simp

/-- Helper for Theorem 3.7: a prefix-invariant stopped attempt has integrable
base-step and displacement squares at every finite index. -/
theorem integrable_activeBaseStepMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (k : ℕ) :
    Integrable (activeBaseStepIntegrand attempt k) P := by
  apply integrable_activeBaseStepIntegrand_of_bound attempt k
  intro hk omega
  exact norm_baseStep_le_of_prefixInvariant attempt invariant ⟨k, hk⟩ omega

/-- Helper for Theorem 3.7: a prefix-invariant stopped attempt has integrable
displacement squares at every finite index. -/
theorem integrable_activeDisplacementMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (k : ℕ) :
    Integrable (activeDisplacementIntegrand attempt k) P := by
  apply integrable_activeDisplacementIntegrand_of_bound attempt k
  intro hk omega
  exact norm_baseStep_le_of_prefixInvariant attempt invariant ⟨k, hk⟩ omega

/-- Helper for Theorem 3.7: every finite displacement moment is nonnegative. -/
theorem activeDisplacementMeanSquare_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    0 ≤ activeDisplacementMeanSquare attempt k := by
  unfold activeDisplacementMeanSquare
  exact integral_nonneg fun omega ↦
    activeDisplacementIntegrand_nonneg attempt k omega

/-- Helper for Theorem 3.7: the raw SPIDER recursion accumulates only the
displacement innovations since its latest refresh. -/
theorem activeRawGradientErrorMeanSquare_le_lastRefresh
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (k : ℕ) (hk : k < K) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              activeDisplacementMeanSquare attempt j := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hrefresh : k % Q = 0
      · refine ⟨recursion.raw_integrable k hk, ?_⟩
        simpa only [hrefresh, Nat.sub_zero, Finset.Ico_self,
          Finset.sum_empty, mul_zero, add_zero] using
          recursion.refresh_bound k hk hrefresh
      · have hkPositive : 0 < k :=
          Nat.pos_of_ne_zero fun hkZero ↦
            hrefresh (by simp only [hkZero, Nat.zero_mod])
        have hkPrev : k - 1 < K := by omega
        have hprevious := ih (k - 1) (by omega) hkPrev
        refine ⟨recursion.raw_integrable k hk, ?_⟩
        have hkPredSucc : k - 1 + 1 = k := by omega
        have hQGtOne : 1 < (Q : ℕ) := by
          have hQPositive : 0 < (Q : ℕ) := Q.pos
          by_contra hnot
          have hQeq : (Q : ℕ) = 1 := by omega
          exact hrefresh (by rw [hQeq, Nat.mod_one])
        have hmodSucc :
            k % Q = ((k - 1) % Q + 1) % Q := by
          conv_lhs => rw [← hkPredSucc]
          rw [Nat.add_mod, Nat.mod_eq_of_lt hQGtOne]
        have hpreviousRemainderSucc : (k - 1) % Q + 1 < Q := by
          have hpreviousModLt : (k - 1) % Q < Q :=
            Nat.mod_lt (k - 1) Q.pos
          by_contra hnot
          have heq : (k - 1) % Q + 1 = Q := by omega
          apply hrefresh
          rw [hmodSucc, heq, Nat.mod_self]
        have hkModSucc : k % Q = (k - 1) % Q + 1 := by
          rw [hmodSucc, Nat.mod_eq_of_lt hpreviousRemainderSucc]
        have hblockStart : k - k % Q = (k - 1) - (k - 1) % Q := by
          omega
        have hstart_le : k - k % Q ≤ k - 1 := by
          have hkModPositive : 0 < k % Q := Nat.pos_of_ne_zero hrefresh
          omega
        have hblockSum :
            (∑ j ∈ Finset.Ico (k - k % Q) k,
                activeDisplacementMeanSquare attempt j) =
              (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  activeDisplacementMeanSquare attempt j) +
                activeDisplacementMeanSquare attempt (k - 1) := by
          calc
            (∑ j ∈ Finset.Ico (k - k % Q) k,
                activeDisplacementMeanSquare attempt j) =
                ∑ j ∈ Finset.Ico (k - k % Q) ((k - 1) + 1),
                  activeDisplacementMeanSquare attempt j := by
                    rw [hkPredSucc]
            _ = (∑ j ∈ Finset.Ico (k - k % Q) (k - 1),
                  activeDisplacementMeanSquare attempt j) +
                activeDisplacementMeanSquare attempt (k - 1) :=
              Finset.sum_Ico_succ_top hstart_le
                (activeDisplacementMeanSquare attempt)
            _ = (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  activeDisplacementMeanSquare attempt j) +
                activeDisplacementMeanSquare attempt (k - 1) := by
              rw [hblockStart]
        calc
          activeRawGradientErrorMeanSquare attempt k ≤
              activeRawGradientErrorMeanSquare attempt (k - 1) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  activeDisplacementMeanSquare attempt (k - 1) :=
            recursion.update_bound k hk hkPositive hrefresh
          _ ≤ ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                    activeDisplacementMeanSquare attempt j) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                activeDisplacementMeanSquare attempt (k - 1) :=
            add_le_add hprevious.2 le_rfl
          _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico (k - k % Q) k,
                    activeDisplacementMeanSquare attempt j := by
            rw [hblockSum]
            ring

/-! The counting estimate below is deliberately local to the base finite
    stopped layer.  It only uses finite interval arithmetic, so importing the
    corrected stochastic-estimator layer for this combinatorial fact would
    create an avoidable dependency from the base theorem to a later variant. -/

/-- Helper for Theorem 3.7: over a finite horizon, the latest-refresh prefix
sum charges each nonnegative index at most `q` times. -/
lemma sumLatestRefreshPrefixes_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (q K : ℕ) (hq : 0 < q) :
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j ≤
      (q : ℝ) * ∑ j ∈ Finset.range K, a j := by
  classical
  have interval_eq_filter (k : ℕ) (hk : k ∈ Finset.range K) :
      Finset.Ico (k - k % q) k =
        (Finset.range K).filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) := by
    have hk' : k < K := Finset.mem_range.mp hk
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  calc
    (∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j) =
        ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ j ∈ Finset.Ico (k - k % q) k, a j) =
            ∑ j ∈ (Finset.range K).filter
              (fun j ↦ j ∈ Finset.Ico (k - k % q) k), a j :=
          congrArg (fun s : Finset ℕ ↦ ∑ j ∈ s, a j)
            (interval_eq_filter k hk)
        _ = ∑ j ∈ Finset.range K,
              if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
          exact Finset.sum_filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) a
    _ = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range K, (q : ℝ) * a j := by
      apply Finset.sum_le_sum
      intro j hj
      have hsubset :
          (Finset.range K).filter (fun k ↦ j ∈ Finset.Ico (k - k % q) k) ⊆
            Finset.Ioc j (j + q) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
          Finset.mem_Ioc] at hk ⊢
        have hmod : k % q < q := Nat.mod_lt k hq
        omega
      have hcard :
          ((Finset.range K).filter
            (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤ q := by
        calc
          ((Finset.range K).filter
              (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤
              (Finset.Ioc j (j + q)).card := Finset.card_le_card hsubset
          _ = q := by simp
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcard) (ha j)
    _ = (q : ℝ) * ∑ j ∈ Finset.range K, a j := by
      rw [Finset.mul_sum]

/-- The finite stopped SPIDER energy coupling follows from the actual
refresh/update recursion and the finite block-counting inequality. -/
theorem stoppedGradientErrorEnergy_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (recursion : FiniteStoppedSPIDERRecursion attempt) :
    stoppedGradientErrorEnergy attempt ≤
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
        ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) *
          stoppedBaseStepEnergy attempt := by
  classical
  have hactiveBound (k : ℕ) (hk : k < K) :
      activeGradientErrorMeanSquare attempt k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              activeDisplacementMeanSquare attempt j := by
    have hraw := activeRawGradientErrorMeanSquare_le_lastRefresh
      attempt recursion k hk
    exact (activeGradientErrorMeanSquare_le_raw attempt k hraw.1).trans hraw.2
  have hblockCount := sumLatestRefreshPrefixes_le
    (fun j ↦ activeDisplacementMeanSquare attempt j)
    (fun j ↦ activeDisplacementMeanSquare_nonneg attempt j) Q K Q.pos
  have hvarianceCoefficient :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  have hblockCoefficient :
      0 ≤ (Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) hvarianceCoefficient
  have hsumBound :
      (∑ k ∈ Finset.range K, activeGradientErrorMeanSquare attempt k) ≤
        (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ k ∈ Finset.range K,
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                activeDisplacementMeanSquare attempt j := by
    calc
      (∑ k ∈ Finset.range K, activeGradientErrorMeanSquare attempt k) ≤
          ∑ k ∈ Finset.range K,
            ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                ∑ j ∈ Finset.Ico (k - k % Q) k,
                  activeDisplacementMeanSquare attempt j) := by
        exact Finset.sum_le_sum fun k hk ↦
          hactiveBound k (Finset.mem_range.mp hk)
      _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ∑ k ∈ Finset.range K,
                ∑ j ∈ Finset.Ico (k - k % Q) k,
                  activeDisplacementMeanSquare attempt j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, Finset.mul_sum]
        ring
  have hdispToBase :
      (∑ k ∈ Finset.range K, activeDisplacementMeanSquare attempt k) =
        stoppedBaseStepEnergy attempt := by
    unfold stoppedBaseStepEnergy
    apply Finset.sum_congr rfl
    intro k hk
    exact activeDisplacementMeanSquare_eq_activeBaseStepMeanSquare attempt k
  unfold stoppedGradientErrorEnergy
  calc
    (∑ k ∈ Finset.range K, activeGradientErrorMeanSquare attempt k) ≤
        (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ((Q : ℝ) * ∑ k ∈ Finset.range K,
              activeDisplacementMeanSquare attempt k) := by
      calc
        _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                ∑ k ∈ Finset.range K,
                  ∑ j ∈ Finset.Ico (k - k % Q) k,
                    activeDisplacementMeanSquare attempt j := hsumBound
        _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                ((Q : ℝ) * ∑ k ∈ Finset.range K,
                  activeDisplacementMeanSquare attempt k) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left hblockCount hvarianceCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) *
            stoppedBaseStepEnergy attempt := by
      rw [hdispToBase]
      ring

/-- The finite stopped energy coupling yields the aggregate clipped-error
bound used by the theorem-level Lyapunov argument. -/
theorem FiniteStoppedEnergyCoupling.gradientErrorEnergy_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (coupling : FiniteStoppedEnergyCoupling attempt) :
    stoppedGradientErrorEnergy attempt ≤
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
        ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) *
          stoppedBaseStepEnergy attempt := by
  exact stoppedGradientErrorEnergy_le attempt coupling.spiderRecursion

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
