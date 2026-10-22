/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorActiveState

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction.StochasticRun.Localization

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
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+} {confidence : ℝ}

/-- Helper for Corollary 4.2: survival at a successor horizon is survival at
the preceding horizon together with localization of the new corrected point. -/
theorem mem_survivalEvent_succ_iff
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω) :
    omega ∈ survivalEvent run X (k + 1) ↔
      omega ∈ survivalEvent run X k ∧ run.point (k + 1) omega ∈ X := by
  -- Split the finite one-based interval at its last index.
  rw [mem_survivalEvent, mem_survivalEvent]
  constructor
  · intro hsurvival
    constructor
    · intro j hj
      exact hsurvival j ⟨hj.1, Nat.le.step hj.2⟩
    · exact hsurvival (k + 1) ⟨Nat.succ_pos k, le_rfl⟩
  · rintro ⟨hprevious, hlast⟩ j hj
    rcases hj with ⟨hjOne, hjTop⟩
    by_cases hjPrevious : j ≤ k
    · exact hprevious j ⟨hjOne, hjPrevious⟩
    · have hjLast : j = k + 1 := by omega
      simpa only [hjLast] using hlast

/-- Helper for Corollary 4.2: survival through horizon zero is automatic. -/
theorem mem_survivalEvent_zero
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (omega : Ω) :
    omega ∈ survivalEvent run X 0 := by
  -- The defining one-based interval through zero is empty.
  rw [mem_survivalEvent]
  intro j hj
  rcases hj with ⟨hjOne, hjZero⟩
  omega

/-- Helper for Corollary 4.2: the numerical state before the initial batch. -/
def initialPreBatchData : PreBatchData (n := n) (m := m) :=
  preBatchDataOfComponents x₀ x₀ multiplier₀ 0

/-- Helper for Corollary 4.2: the initial numerical state satisfies every
clause required by the corrected active transition. -/
theorem initialPreBatchInvariant
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    ActivePreBatchInvariant h params X
      (initialPreBatchData (x₀ := x₀) (multiplier₀ := multiplier₀)) := by
  have hxRegion : x₀ ∈ h.region :=
    h_region.thickening_subset
      (Metric.self_subset_cthickening X initial_mem)
  have heffective :
      ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
        3 * params.multiplierBound := by
    calc
      ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
          ‖multiplier₀‖ + ‖(params.rho : ℝ) • c x₀‖ := norm_add_le _ _
      _ = ‖multiplier₀‖ + params.rho * ‖c x₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1]
      _ ≤ 3 * params.multiplierBound := by
        have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
        linarith [params.norm_multiplier₀_le, params.initialResidual_le]
  -- The two parameter initialization bounds close the multiplier clauses.
  unfold initialPreBatchData
  exact (activePreBatchInvariant_preBatchDataOfComponents_iff
    h params X x₀ x₀ multiplier₀ 0).2
      ⟨initial_mem, hxRegion, params.norm_multiplier₀_le, heffective⟩

/-- Helper for Corollary 4.2: the initial active state packages the verified
initial corrected invariant. -/
noncomputable def initialActivePreBatchState
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    ActivePreBatchState h params X :=
  ⟨initialPreBatchData,
    initialPreBatchInvariant initial_mem h_region⟩

/-- Helper for Corollary 4.2: the initialized active package exposes the
initial current point. -/
theorem initialActivePreBatchState_current
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    (initialActivePreBatchState initial_mem h_region).1.1 = x₀ := by
  unfold initialActivePreBatchState initialPreBatchData
  exact preBatchDataOfComponents_current _ _ _ _

/-- Helper for Corollary 4.2: the initialized active package exposes the
initial preceding point. -/
theorem initialActivePreBatchState_previous
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    (initialActivePreBatchState initial_mem h_region).1.2.1 = x₀ := by
  unfold initialActivePreBatchState initialPreBatchData
  exact preBatchDataOfComponents_previous _ _ _ _

/-- Helper for Corollary 4.2: the initialized active package exposes the
initial multiplier. -/
theorem initialActivePreBatchState_multiplier
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    (initialActivePreBatchState initial_mem h_region).1.2.2.1 = multiplier₀ := by
  unfold initialActivePreBatchState initialPreBatchData
  exact preBatchDataOfComponents_multiplier _ _ _ _

/-- Helper for Corollary 4.2: the initialized active package starts with a
zero preceding raw estimate. -/
theorem initialActivePreBatchState_rawEstimate
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    (initialActivePreBatchState initial_mem h_region).1.2.2.2 = 0 := by
  unfold initialActivePreBatchState initialPreBatchData
  exact preBatchDataOfComponents_rawEstimate _ _ _ _

/-- Helper for Corollary 4.2: the numerical state fixed before an actual run
batch stores the preceding raw estimate and the corrected run fields. -/
noncomputable def actualPreBatchData
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) : PreBatchData (n := n) (m := m) :=
  preBatchDataOfComponents
    (run.point k omega) (run.point (k - 1) omega) (run.multiplier k omega)
    (if k = 0 then 0 else
      SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) omega)

/-- Helper for Corollary 4.2: the actual numerical package exposes the
current corrected point. -/
theorem actualPreBatchData_current
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    (actualPreBatchData run k omega).1 = run.point k omega := by
  -- Project the current-point component through the packaging definition.
  unfold actualPreBatchData
  exact preBatchDataOfComponents_current _ _ _ _

/-- Helper for Corollary 4.2: the actual numerical package exposes the
preceding corrected point. -/
theorem actualPreBatchData_previous
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    (actualPreBatchData run k omega).2.1 = run.point (k - 1) omega := by
  -- Project the preceding-point component through the packaging definition.
  unfold actualPreBatchData
  exact preBatchDataOfComponents_previous _ _ _ _

/-- Helper for Corollary 4.2: the actual numerical package exposes the
current corrected multiplier. -/
theorem actualPreBatchData_multiplier
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    (actualPreBatchData run k omega).2.2.1 = run.multiplier k omega := by
  -- Project the multiplier component through the packaging definition.
  unfold actualPreBatchData
  exact preBatchDataOfComponents_multiplier _ _ _ _

/-- Helper for Corollary 4.2: the actual numerical package exposes its
preceding raw SPIDER estimate. -/
theorem actualPreBatchData_rawEstimate
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    (actualPreBatchData run k omega).2.2.2 =
      if k = 0 then 0 else
        SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) omega := by
  -- Project the raw-estimate component through the packaging definition.
  unfold actualPreBatchData
  exact preBatchDataOfComponents_rawEstimate _ _ _ _

/-- Helper for Corollary 4.2: a surviving run lies in the localization set at
its current horizon, including the initialized zero horizon. -/
theorem currentPoint_mem_of_survival
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    run.point k omega ∈ X := by
  -- At positive horizons this is the final point in the survival interval.
  cases k with
  | zero => simpa only [run.point_zero] using initial_mem
  | succ k =>
      exact (mem_survivalEvent run X (k + 1) omega).mp homega (k + 1)
        ⟨Nat.succ_pos k, le_rfl⟩

/-- Helper for Corollary 4.2: on survival, the actual numerical pre-batch
state satisfies the active corrected invariant. -/
theorem actualPreBatchInvariant
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    ActivePreBatchInvariant h params X (actualPreBatchData run k omega) := by
  have hcurrent := currentPoint_mem_of_survival run X initial_mem k omega homega
  have hpreviousSurvival : omega ∈ survivalEvent run X (k - 1) :=
    survivalEvent_antitone run X (Nat.sub_le k 1) homega
  have hpreviousX := currentPoint_mem_of_survival run X initial_mem
    (k - 1) omega hpreviousSurvival
  have hpreviousRegion : run.point (k - 1) omega ∈ h.region :=
    h_region.thickening_subset
      (Metric.self_subset_cthickening X hpreviousX)
  have hbounds := preExitPrefixBounds run X initial_mem h_region omega k homega
  have hkSucc : k ≤ k + 1 := Nat.le_succ k
  have hmultiplier : ‖run.multiplier k omega‖ ≤ params.multiplierBound :=
    hbounds.2.2 k hkSucc
  have heffective :
      ‖run.multiplier k omega +
          (params.rho : ℝ) • c (run.point k omega)‖ ≤
        3 * params.multiplierBound :=
    run.normEffectiveMultiplier_le k omega fun j hj ↦
      hbounds.2.2 j (hj.trans hkSucc)
  -- Unfold only the numerical packaging; the analytic bounds remain named.
  unfold actualPreBatchData
  exact (activePreBatchInvariant_preBatchDataOfComponents_iff
    h params X (run.point k omega) (run.point (k - 1) omega)
      (run.multiplier k omega) _).2
        ⟨hcurrent, hpreviousRegion, hmultiplier, heffective⟩

/-- Helper for Corollary 4.2: a surviving run state is bundled as an active
state with its corrected invariant. -/
noncomputable def actualActivePreBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    ActivePreBatchState h params X :=
  ⟨actualPreBatchData run k omega,
    actualPreBatchInvariant run X initial_mem h_region k omega homega⟩

/-- Helper for Corollary 4.2: coercing the bundled actual state recovers its
numerical pre-batch data. -/
theorem actualActivePreBatchState_coe
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    (actualActivePreBatchState run X initial_mem h_region k omega homega).1 =
      actualPreBatchData run k omega := by
  -- The subtype constructor stores the numerical package unchanged.
  rfl

/-- Helper for Corollary 4.2: the actual localized pre-batch state is active
exactly on the corrected survival event. -/
noncomputable def localizedPreBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) : LocalizedPreBatchState h params X :=
  @dite (LocalizedPreBatchState h params X)
    (omega ∈ survivalEvent run X k) (Classical.propDecidable _)
    (fun homega ↦ Sum.inr
      (actualActivePreBatchState run X initial_mem h_region k omega homega))
    (fun _ ↦ Sum.inl ())

/-- Helper for Corollary 4.2: on survival, the localized pre-batch state is
the bundled active run state. -/
theorem localizedPreBatchState_of_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    localizedPreBatchState run X initial_mem h_region k omega =
      Sum.inr (actualActivePreBatchState
        run X initial_mem h_region k omega homega) := by
  -- Select the active branch once at the construction owner.
  unfold localizedPreBatchState
  rw [dif_pos homega]

/-- Helper for Corollary 4.2: off the survival event, the localized pre-batch
state is the inactive unit state. -/
theorem localizedPreBatchState_of_not_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∉ survivalEvent run X k) :
    localizedPreBatchState run X initial_mem h_region k omega = Sum.inl () := by
  -- Select the inactive branch once at the construction owner.
  unfold localizedPreBatchState
  rw [dif_neg homega]

/-- Helper for Corollary 4.2: the canonical localized state is generated from
exactly the batches preceding its index. -/
noncomputable def canonicalLocalizedPreBatchState
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    (k : ℕ) → (Fin k → ℕ → Ξ) → LocalizedPreBatchState h params X
  | 0, _ => Sum.inr (initialActivePreBatchState initial_mem h_region)
  | k + 1, samples =>
      canonicalLocalizedTransition h oracle params Q B b X h_region k
        (canonicalLocalizedPreBatchState h oracle params Q B b X
          initial_mem h_region k (fun t i ↦ samples t.castSucc i),
        samples (Fin.last k))

/-- Helper for Corollary 4.2: the canonical localized finite-history recursion
starts from the bundled active initial state. -/
theorem canonicalLocalizedPreBatchState_zero
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (samples : Fin 0 → ℕ → Ξ) :
    canonicalLocalizedPreBatchState h oracle params Q B b X initial_mem h_region 0
        samples =
      Sum.inr (initialActivePreBatchState initial_mem h_region) := by
  rfl

/-- Helper for Corollary 4.2: one successor of the canonical localized
finite-history recursion applies the localized transition to the prefix state
and the final fresh batch. -/
theorem canonicalLocalizedPreBatchState_succ
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (samples : Fin (k + 1) → ℕ → Ξ) :
    canonicalLocalizedPreBatchState h oracle params Q B b X initial_mem h_region
        (k + 1) samples =
      canonicalLocalizedTransition h oracle params Q B b X h_region k
        (canonicalLocalizedPreBatchState h oracle params Q B b X initial_mem h_region k
          (fun t i ↦ samples t.castSucc i), samples (Fin.last k)) := by
  rfl

/-- Helper for Corollary 4.2: the canonical localized state is measurable in
its finite history of preceding batches. -/
theorem measurable_canonicalLocalizedPreBatchState
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Measurable (canonicalLocalizedPreBatchState h oracle params Q B b X
      initial_mem h_region k) := by
  -- Restrict a successor history to its prefix and expose its final batch.
  induction k with
  | zero =>
      simpa only [canonicalLocalizedPreBatchState] using
        (measurable_const : Measurable (fun _ : Fin 0 → ℕ → Ξ ↦
          (Sum.inr (initialActivePreBatchState initial_mem h_region) :
            LocalizedPreBatchState h params X)))
  | succ k ih =>
      let restrictHistory : (Fin (k + 1) → ℕ → Ξ) → Fin k → ℕ → Ξ :=
        fun samples t i ↦ samples t.castSucc i
      have hrestrictHistory : Measurable restrictHistory := by
        apply measurable_pi_lambda
        intro t
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i).comp (measurable_pi_apply t.castSucc)
      have hstate : Measurable (fun samples ↦
          canonicalLocalizedPreBatchState h oracle params Q B b X
            initial_mem h_region k (restrictHistory samples)) :=
        ih.comp hrestrictHistory
      have hbatch : Measurable (fun samples : Fin (k + 1) → ℕ → Ξ ↦
          samples (Fin.last k)) := measurable_pi_apply (Fin.last k)
      -- The active-state module provides the measurable corrected transition.
      simpa only [canonicalLocalizedPreBatchState, restrictHistory,
        Function.comp_def] using
        (measurable_canonicalLocalizedTransition
          (Q := Q) (B := B) (b := b) X hX h_region k).comp
            (hstate.prodMk hbatch)

/-- Helper for Corollary 4.2: the canonical raw transition reproduces the
actual SPIDER raw estimate on every run path. -/
theorem canonicalRawEstimateAt_apply_samples
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    canonicalRawEstimateAt oracle Q B b k (actualPreBatchData run k omega)
        (fun i ↦ run.sample k i omega) =
      SPIDER.rawEstimate oracle run.point run.sample Q B b k omega := by
  -- The deterministic schedule splits into the public refresh and update equations.
  by_cases hrefresh : k % Q = 0
  · rw [canonicalRawEstimateAt_of_refresh oracle Q B b k
        (actualPreBatchData run k omega) (fun i ↦ run.sample k i omega) hrefresh,
      SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b k omega
        hrefresh]
    simp only [actualPreBatchData, preBatchDataOfComponents_current]
  · have hkPositive : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkZero
      have hkMod : k % Q = 0 := by simp only [hkZero, Nat.zero_mod]
      exact hrefresh hkMod
    have hkPredSucc : k - 1 + 1 = k := by omega
    have hnonrefreshPred : (k - 1 + 1) % Q ≠ 0 := by
      simpa only [hkPredSucc] using hrefresh
    rw [canonicalRawEstimateAt_of_update oracle Q B b k
        (actualPreBatchData run k omega) (fun i ↦ run.sample k i omega) hrefresh,
      ← hkPredSucc,
      SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b (k - 1)
        omega hnonrefreshPred]
    simp only [actualPreBatchData, preBatchDataOfComponents_current,
      preBatchDataOfComponents_previous, preBatchDataOfComponents_rawEstimate,
      if_neg (ne_of_gt hkPositive), hkPredSucc]

/-- Helper for Corollary 4.2: on a surviving path, the canonical active
model solver reproduces the run's chosen minimizing base step. -/
theorem canonicalActiveBaseStepAt_actual
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    canonicalActiveBaseStepAt h oracle params Q B b k
        (actualActivePreBatchState run X initial_mem h_region k omega homega,
          fun i ↦ run.sample k i omega) =
      run.baseStep k omega := by
  -- Normalize the stored state and raw transition, then use uniqueness of the model minimizer.
  rw [canonicalActiveBaseStepAt_apply, actualActivePreBatchState_coe,
    actualPreBatchData_current, actualPreBatchData_multiplier,
    canonicalRawEstimateAt_apply_samples]
  simpa only [SPIDER.estimate_apply] using
    canonicalBaseStep_eq_of_minimizes c params.rho params.beta
      (run.point k omega)
      (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k omega)
      (run.multiplier k omega) (run.baseStep k omega)
      params.spec.1.2.2.1 params.spec.1.2.1 (run.minimizes_baseStep k omega)

/-- Helper for Corollary 4.2: on a surviving path, the canonical active
corrected point is the run's next point. -/
theorem canonicalActiveNextPointAt_actual
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    canonicalActiveNextPointAt h oracle params Q B b k
        (actualActivePreBatchState run X initial_mem h_region k omega homega,
          fun i ↦ run.sample k i omega) =
      run.point (k + 1) omega := by
  -- Rewrite the canonical step and finish with the run's corrected point equation.
  rw [canonicalActiveNextPointAt_apply, actualActivePreBatchState_coe,
    actualPreBatchData_current,
    canonicalActiveBaseStepAt_actual run X initial_mem h_region k omega homega,
    ← run.point_succ k omega]

/-- Helper for Corollary 4.2: on a surviving path, the canonical active
multiplier is the run's next multiplier. -/
theorem canonicalActiveNextMultiplierAt_actual
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    canonicalActiveNextMultiplierAt h oracle params Q B b k
        (actualActivePreBatchState run X initial_mem h_region k omega homega,
          fun i ↦ run.sample k i omega) =
      run.multiplier (k + 1) omega := by
  -- Rewrite the canonical step and finish with the run's corrected multiplier equation.
  rw [canonicalActiveNextMultiplierAt_apply, actualActivePreBatchState_coe,
    actualPreBatchData_current, actualPreBatchData_multiplier,
    canonicalActiveBaseStepAt_actual run X initial_mem h_region k omega homega,
    ← run.multiplier_succ k omega]

/-- Helper for Corollary 4.2: one canonical active transition on actual
samples produces exactly the next actual numerical pre-batch package. -/
theorem canonicalActiveNextDataAt_actual
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) (homega : omega ∈ survivalEvent run X k) :
    canonicalActiveNextDataAt h oracle params Q B b k
        (actualActivePreBatchState run X initial_mem h_region k omega homega,
          fun i ↦ run.sample k i omega) =
      actualPreBatchData run (k + 1) omega := by
  -- Compare the four numerical fields using their owner projection equations.
  apply Prod.ext
  · rw [canonicalActiveNextDataAt_current,
      canonicalActiveNextPointAt_actual run X initial_mem h_region k omega homega,
      actualPreBatchData_current]
  · apply Prod.ext
    · rw [canonicalActiveNextDataAt_previous, actualActivePreBatchState_coe,
        actualPreBatchData_current, actualPreBatchData_previous,
        Nat.add_sub_cancel]
    · apply Prod.ext
      · rw [canonicalActiveNextDataAt_multiplier,
          canonicalActiveNextMultiplierAt_actual run X initial_mem h_region k omega homega,
          actualPreBatchData_multiplier]
      · rw [canonicalActiveNextDataAt_rawEstimate, actualActivePreBatchState_coe,
          canonicalRawEstimateAt_apply_samples, actualPreBatchData_rawEstimate]
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]

/-- Helper for Corollary 4.2: the initial actual numerical package agrees
with the canonical initialized package. -/
theorem actualPreBatchData_zero
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (omega : Ω) :
    actualPreBatchData run 0 omega =
      initialPreBatchData (x₀ := x₀) (multiplier₀ := multiplier₀) := by
  -- Compare initialized points, multiplier, and the zero raw-estimate field.
  apply Prod.ext
  · rw [actualPreBatchData_current, run.point_zero]
    exact (preBatchDataOfComponents_current _ _ _ _).symm
  · apply Prod.ext
    · rw [actualPreBatchData_previous, Nat.zero_sub, run.point_zero]
      exact (preBatchDataOfComponents_previous _ _ _ _).symm
    · apply Prod.ext
      · rw [actualPreBatchData_multiplier, run.multiplier_zero]
        exact (preBatchDataOfComponents_multiplier _ _ _ _).symm
      · rw [actualPreBatchData_rawEstimate]
        exact (preBatchDataOfComponents_rawEstimate _ _ _ _).symm

/-- Helper for Corollary 4.2: evaluating the canonical finite-history
recursion on a run's actual samples gives its survival-bundled actual state. -/
theorem canonicalLocalizedPreBatchState_apply_samples
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) :
    canonicalLocalizedPreBatchState h oracle params Q B b X initial_mem h_region k
        (fun t i ↦ run.sample t i omega) =
      localizedPreBatchState run X initial_mem h_region k omega := by
  -- Inductively identify the prior active state and split survival at the new point.
  classical
  induction k with
  | zero =>
      have hzero := mem_survivalEvent_zero run X omega
      rw [canonicalLocalizedPreBatchState, localizedPreBatchState, dif_pos hzero]
      apply congrArg Sum.inr
      apply Subtype.ext
      rw [actualActivePreBatchState_coe, actualPreBatchData_zero]
      rfl
  | succ k ih =>
      rw [canonicalLocalizedPreBatchState]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      by_cases hprevious : omega ∈ survivalEvent run X k
      · by_cases hnext : run.point (k + 1) omega ∈ X
        · have hsuccessor : omega ∈ survivalEvent run X (k + 1) :=
            (mem_survivalEvent_succ_iff run X k omega).2 ⟨hprevious, hnext⟩
          have hcanonicalNext :
              canonicalActiveNextPointAt h oracle params Q B b k
                  (actualActivePreBatchState run X initial_mem h_region k omega hprevious,
                    fun i ↦ run.sample k i omega) ∈ X := by
            rw [canonicalActiveNextPointAt_actual run X initial_mem h_region k omega hprevious]
            exact hnext
          rw [localizedPreBatchState, dif_pos hprevious,
            canonicalLocalizedTransition_active_of_mem X h_region k
              (actualActivePreBatchState run X initial_mem h_region k omega hprevious)
              (fun i ↦ run.sample k i omega) hcanonicalNext,
            localizedPreBatchState, dif_pos hsuccessor]
          apply congrArg Sum.inr
          apply Subtype.ext
          exact canonicalActiveNextDataAt_actual run X initial_mem h_region k omega hprevious
        · have hsuccessor : omega ∉ survivalEvent run X (k + 1) := by
            intro hmem
            exact hnext ((mem_survivalEvent_succ_iff run X k omega).1 hmem).2
          have hcanonicalNext :
              canonicalActiveNextPointAt h oracle params Q B b k
                  (actualActivePreBatchState run X initial_mem h_region k omega hprevious,
                    fun i ↦ run.sample k i omega) ∉ X := by
            rw [canonicalActiveNextPointAt_actual run X initial_mem h_region k omega hprevious]
            exact hnext
          rw [localizedPreBatchState, dif_pos hprevious,
            canonicalLocalizedTransition_active_of_not_mem X h_region k
              (actualActivePreBatchState run X initial_mem h_region k omega hprevious)
              (fun i ↦ run.sample k i omega) hcanonicalNext,
            localizedPreBatchState, dif_neg hsuccessor]
      · have hsuccessor : omega ∉ survivalEvent run X (k + 1) := by
          intro hmem
          exact hprevious ((mem_survivalEvent_succ_iff run X k omega).1 hmem).1
        rw [localizedPreBatchState, dif_neg hprevious,
          canonicalLocalizedTransition_inactive X h_region k
            (fun i ↦ run.sample k i omega),
          localizedPreBatchState, dif_neg hsuccessor]

/-- Helper for Corollary 4.2: each oracle-sample coordinate has a canonical
measurable version. -/
private noncomputable def measurableSampleCoordinate
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) : Ω → Ξ :=
  (run.hasLaw_sample ki.1 ki.2).aemeasurable.mk
    (run.sample ki.1 ki.2)

/-- Helper for Corollary 4.2: every canonical sample coordinate is
measurable. -/
private theorem measurable_measurableSampleCoordinate
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) : Measurable (measurableSampleCoordinate run ki) := by
  -- Use the measurable representative supplied by the coordinate law.
  exact (run.hasLaw_sample ki.1 ki.2).aemeasurable.measurable_mk

/-- Helper for Corollary 4.2: each measurable coordinate agrees almost
everywhere with the corresponding run sample. -/
private theorem measurableSampleCoordinate_ae_eq
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) :
    measurableSampleCoordinate run ki =ᵐ[P] run.sample ki.1 ki.2 := by
  -- Orient the standard measurable-modification identity toward the original sample.
  exact (run.hasLaw_sample ki.1 ki.2).aemeasurable.ae_eq_mk.symm

/-- Helper for Corollary 4.2: measurable modification preserves mutual
independence of the full coordinate family. -/
private theorem iIndepFun_measurableSampleCoordinate
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) :
    ProbabilityTheory.iIndepFun
      (fun ki : ℕ × ℕ ↦ measurableSampleCoordinate run ki) P := by
  -- Transfer independence coordinatewise along almost-everywhere equality.
  exact ProbabilityTheory.iIndepFun.congr
    (fun ki ↦ (measurableSampleCoordinate_ae_eq run ki).symm)
    run.independent_sample

/-- Helper for Corollary 4.2: the sigma-algebra of one measurable sample
coordinate is the pullback of the oracle sample space. -/
private noncomputable abbrev sampleCoordinateSigma
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) : MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace Ξ).comap
    (measurableSampleCoordinate run ki)

/-- Helper for Corollary 4.2: each coordinate sigma-algebra lies below the
ambient sample-space sigma-algebra. -/
private theorem sampleCoordinateSigma_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) :
    sampleCoordinateSigma run ki ≤ (inferInstance : MeasurableSpace Ω) := by
  -- Ambient measurability is precisely the required comap inequality.
  unfold sampleCoordinateSigma
  exact (measurable_measurableSampleCoordinate run ki).comap_le

/-- Helper for Corollary 4.2: the measurable coordinate sigma-algebras are
mutually independent. -/
private theorem iIndep_sampleCoordinateSigma
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) :
    ProbabilityTheory.iIndep (fun ki : ℕ × ℕ ↦
      sampleCoordinateSigma run ki) P := by
  -- Independence of functions is independence of their pulled-back spaces.
  simpa only [sampleCoordinateSigma] using
    (iIndepFun_measurableSampleCoordinate run).iIndep

/-- Helper for Corollary 4.2: indices with time strictly before a fixed
batch horizon. -/
private def pastSampleIndexSet (k : ℕ) : Set (ℕ × ℕ) :=
  {ki | ki.1 < k}

/-- Helper for Corollary 4.2: all sample indices in one current batch. -/
private def currentSampleIndexSet (k : ℕ) : Set (ℕ × ℕ) :=
  {ki | ki.1 = k}

/-- Helper for Corollary 4.2: past and current-batch sample indices are
disjoint. -/
private theorem pastSampleIndexSet_disjoint_currentSampleIndexSet (k : ℕ) :
    Disjoint (pastSampleIndexSet k) (currentSampleIndexSet k) := by
  -- The first coordinate cannot be both strictly below and equal to the horizon.
  rw [Set.disjoint_left]
  rintro ⟨t, i⟩ htPast htCurrent
  simp only [pastSampleIndexSet, Set.mem_setOf_eq] at htPast
  simp only [currentSampleIndexSet, Set.mem_setOf_eq] at htCurrent
  omega

/-- Helper for Corollary 4.2: the past sigma-algebra is generated by sample
coordinates whose time is strictly before the horizon. -/
private noncomputable abbrev pastSampleSigma
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    MeasurableSpace Ω :=
  ⨆ ki ∈ pastSampleIndexSet k, sampleCoordinateSigma run ki

/-- Helper for Corollary 4.2: the current sigma-algebra is generated by all
sample coordinates at the horizon. -/
private noncomputable abbrev currentSampleSigma
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    MeasurableSpace Ω :=
  ⨆ ki ∈ currentSampleIndexSet k, sampleCoordinateSigma run ki

/-- Helper for Corollary 4.2: the measurable finite history collects the
modified batches strictly before its horizon. -/
private noncomputable def measurablePastSampleHistory
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → Fin k → ℕ → Ξ :=
  fun omega t i ↦ measurableSampleCoordinate run (t, i) omega

/-- Helper for Corollary 4.2: the measurable current batch collects the
modified coordinates at its horizon. -/
private noncomputable def measurableCurrentSampleBatch
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → ℕ → Ξ :=
  fun omega i ↦ measurableSampleCoordinate run (k, i) omega

/-- Helper for Corollary 4.2: the modified finite history is measurable with
respect to the sigma-algebra generated by past coordinates. -/
private theorem measurable_measurablePastSampleHistory
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    Measurable[pastSampleSigma run k] (measurablePastSampleHistory run k) := by
  -- Expand both function-space comaps and select the corresponding generator.
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro t
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  have hmem : ((t : ℕ), i) ∈ pastSampleIndexSet k := by
    simp only [pastSampleIndexSet, Set.mem_setOf_eq]
    exact t.isLt
  unfold measurablePastSampleHistory pastSampleSigma sampleCoordinateSigma
  exact le_iSup_of_le ((t : ℕ), i) (le_iSup_of_le hmem le_rfl)

/-- Helper for Corollary 4.2: the modified current batch is measurable with
respect to the sigma-algebra generated at its horizon. -/
private theorem measurable_measurableCurrentSampleBatch
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    Measurable[currentSampleSigma run k]
      (measurableCurrentSampleBatch run k) := by
  -- Expand the function-space comap and select each current-coordinate generator.
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  have hmem : (k, i) ∈ currentSampleIndexSet k := by
    simp only [currentSampleIndexSet, Set.mem_setOf_eq]
  unfold measurableCurrentSampleBatch currentSampleSigma sampleCoordinateSigma
  exact le_iSup_of_le (k, i) (le_iSup_of_le hmem le_rfl)

/-- Helper for Corollary 4.2: the modified past history agrees almost
everywhere with the run's actual finite history. -/
private theorem measurablePastSampleHistory_ae_eq
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    measurablePastSampleHistory run k =ᵐ[P]
      (fun omega t i ↦ run.sample t i omega) := by
  -- Countability combines every coordinatewise measurable-modification identity.
  have hall : ∀ᵐ omega ∂P, ∀ t : Fin k, ∀ i : ℕ,
      measurableSampleCoordinate run (t, i) omega = run.sample t i omega :=
    ae_all_iff.mpr (fun t ↦ ae_all_iff.mpr (fun i ↦
      measurableSampleCoordinate_ae_eq run (t, i)))
  filter_upwards [hall] with omega homega
  funext t i
  exact homega t i

/-- Helper for Corollary 4.2: the modified current batch agrees almost
everywhere with the run's actual current batch. -/
private theorem measurableCurrentSampleBatch_ae_eq
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    measurableCurrentSampleBatch run k =ᵐ[P]
      (fun omega i ↦ run.sample k i omega) := by
  -- Countability combines every current-coordinate modification identity.
  have hall : ∀ᵐ omega ∂P, ∀ i : ℕ,
      measurableSampleCoordinate run (k, i) omega = run.sample k i omega :=
    ae_all_iff.mpr (fun i ↦ measurableSampleCoordinate_ae_eq run (k, i))
  filter_upwards [hall] with omega homega
  funext i
  exact homega i

/-- Helper for Corollary 4.2: the measurable past history is independent of
the measurable current batch. -/
private theorem indepFun_measurablePastHistory_currentBatch
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    ProbabilityTheory.IndepFun (measurablePastSampleHistory run k)
      (measurableCurrentSampleBatch run k) P := by
  have hgrouped : ProbabilityTheory.Indep (pastSampleSigma run k)
      (currentSampleSigma run k) P := by
    -- Group the independent coordinate spaces along the disjoint time partition.
    unfold pastSampleSigma currentSampleSigma
    exact ProbabilityTheory.indep_iSup_of_disjoint
      (sampleCoordinateSigma_le run)
      (iIndep_sampleCoordinateSigma run)
      (pastSampleIndexSet_disjoint_currentSampleIndexSet k)
  -- Each grouped history map generates a sub-sigma-algebra of its side.
  unfold ProbabilityTheory.IndepFun
  exact ProbabilityTheory.indep_of_indep_of_le hgrouped
    (measurable_measurablePastSampleHistory run k).comap_le
    (measurable_measurableCurrentSampleBatch run k).comap_le

/-- Helper for Corollary 4.2: the survival-adapted corrected pre-batch state
is independent of its fresh oracle batch. -/
theorem indepFun_localizedPreBatchState_freshBatch
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (localizedPreBatchState run X initial_mem h_region k)
      (fun omega i ↦ run.sample k i omega) P := by
  have hindependent : ProbabilityTheory.IndepFun
      (canonicalLocalizedPreBatchState h oracle params Q B b X
          initial_mem h_region k ∘ measurablePastSampleHistory run k)
      (id ∘ measurableCurrentSampleBatch run k) P :=
    (indepFun_measurablePastHistory_currentBatch run k).comp
      (measurable_canonicalLocalizedPreBatchState X hX initial_mem h_region k)
      measurable_id
  have hstateAE :
      canonicalLocalizedPreBatchState h oracle params Q B b X
            initial_mem h_region k ∘ measurablePastSampleHistory run k =ᵐ[P]
        localizedPreBatchState run X initial_mem h_region k := by
    -- Replace the measurable past history and invoke the pointwise recursion specification.
    filter_upwards [measurablePastSampleHistory_ae_eq run k] with omega homega
    rw [Function.comp_apply, homega,
      canonicalLocalizedPreBatchState_apply_samples
        run X initial_mem h_region k omega]
  have hbatchIdentity :
      id ∘ measurableCurrentSampleBatch run k =ᵐ[P]
        (fun omega i ↦ run.sample k i omega) := by
    -- Replace the measurable current batch by the actual batch coordinatewise.
    filter_upwards [measurableCurrentSampleBatch_ae_eq run k] with omega homega
    simpa only [Function.comp_apply, id_eq] using homega
  -- Congruence transfers grouped independence to both actual run fields.
  exact hindependent.congr hstateAE hbatchIdentity

/-- Helper for Corollary 4.2: the survival-adapted corrected pre-batch state
has an almost-everywhere measurable representative. -/
theorem aemeasurable_localizedPreBatchState
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    AEMeasurable (localizedPreBatchState run X initial_mem h_region k) P := by
  let past : Ω → Fin k → ℕ → Ξ :=
    fun omega t i ↦ run.sample t i omega
  have hpast : AEMeasurable past P := by
    -- Assemble the actual finite history from coordinatewise measurability.
    apply aemeasurable_pi_lambda
    intro t
    apply aemeasurable_pi_lambda
    intro i
    exact (run.hasLaw_sample t i).aemeasurable
  have hcanonical : AEMeasurable
      (canonicalLocalizedPreBatchState h oracle params Q B b X
        initial_mem h_region k ∘ past) P :=
    (measurable_canonicalLocalizedPreBatchState X hX initial_mem h_region k).comp_aemeasurable
      hpast
  have hspec :
      canonicalLocalizedPreBatchState h oracle params Q B b X
            initial_mem h_region k ∘ past =ᵐ[P]
        localizedPreBatchState run X initial_mem h_region k := by
    -- Identify the canonical history map with the actual localized state pointwise.
    exact Filter.Eventually.of_forall fun omega ↦ by
      simpa only [Function.comp_apply, past] using
        canonicalLocalizedPreBatchState_apply_samples
          run X initial_mem h_region k omega
  exact hcanonical.congr hspec

end LALM.Correction.StochasticRun.Localization

end
