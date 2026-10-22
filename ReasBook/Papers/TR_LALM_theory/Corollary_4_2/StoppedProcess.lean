/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizationGeometry

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
variable {params : Parameters h x₀ multiplier₀} {Q B b : ℕ+}
variable {confidence : ℝ}

/-- Helper for Corollary 4.2: the event that a corrected stochastic run does
not leave the localization set through the given horizon. -/
def survivalEvent
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) : Set Ω :=
  {ω | (K : ℕ∞) < exitTime run X ω}

/-- Helper for Corollary 4.2: survival membership is the corresponding strict
comparison with the corrected localization exit time. -/
theorem mem_survivalEvent_iff_lt_exitTime
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) :
    ω ∈ survivalEvent run X K ↔ (K : ℕ∞) < exitTime run X ω := by
  -- Expose the owner definition without unfolding it in analytic consumers.
  rfl

/-- Helper for Corollary 4.2: survival through `K` is membership in the
localization set at every one-based index through `K`. -/
theorem mem_survivalEvent
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) :
    ω ∈ survivalEvent run X K ↔
      ∀ j ∈ Set.Icc 1 K, run.point j ω ∈ X := by
  -- Negate the finite-horizon exit characterization.
  rw [survivalEvent, Set.mem_setOf_eq, ← not_le, exitTime_le_iff]
  simp

/-- Helper for Corollary 4.2: point membership through a finite prefix gives
corrected admissibility, base-step bounds, and multiplier bounds together. -/
theorem prefixBounds_of_points_mem
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (N : ℕ)
    (hpoints : ∀ j < N, run.point j ω ∈ X) :
    (∀ j < N, IsAdmissible h (run.point j ω) (run.baseStep j ω)) ∧
      (∀ j < N, ‖run.baseStep j ω‖ ≤ params.delta) ∧
      (∀ j ≤ N, ‖run.multiplier j ω‖ ≤ params.multiplierBound) := by
  -- Carry all three mutually dependent bounds in one induction.
  induction N with
  | zero =>
      constructor
      · intro j hj
        omega
      · constructor
        · intro j hj
          omega
        · intro j hj
          have hjZero : j = 0 := by omega
          subst j
          rw [run.multiplier_zero]
          exact params.norm_multiplier₀_le
  | succ N ih =>
      have hpointsPrev : ∀ j < N, run.point j ω ∈ X := by
        intro j hj
        exact hpoints j (by omega)
      have hprev := ih hpointsPrev
      have hpointX : run.point N ω ∈ X := hpoints N (Nat.lt_succ_self N)
      have hpointRegion : run.point N ω ∈ h.region :=
        h_region.thickening_subset
          (Metric.self_subset_cthickening X hpointX)
      have heffective := run.normEffectiveMultiplier_le N ω hprev.2.2
      have hstep :=
        run.normBaseStep_le_of_normEffectiveMultiplier_le N ω hpointRegion heffective
      have hadmissible :=
        h_region.isAdmissible_of_mem_of_norm_le
          (run.point N ω) (run.baseStep N ω) hpointX hstep
      have hnewMultiplier :=
        run.normMultiplier_succ_le_of_normBaseStep_le N ω hadmissible hstep
      constructor
      · intro j hj
        by_cases hjOld : j < N
        · exact hprev.1 j hjOld
        · have hjEq : j = N := by omega
          simpa only [hjEq] using hadmissible
      · constructor
        · intro j hj
          by_cases hjOld : j < N
          · exact hprev.2.1 j hjOld
          · have hjEq : j = N := by omega
            simpa only [hjEq] using hstep
        · intro j hj
          by_cases hjOld : j ≤ N
          · exact hprev.2.2 j hjOld
          · have hjEq : j = N + 1 := by omega
            simpa only [hjEq] using hnewMultiplier

/-- Helper for Corollary 4.2: survival through iteration `k` supplies the
complete corrected invariant needed by the active transition at `k`. -/
theorem preExitPrefixBounds
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hω : ω ∈ survivalEvent run X k) :
    (∀ j < k + 1, IsAdmissible h (run.point j ω) (run.baseStep j ω)) ∧
      (∀ j < k + 1, ‖run.baseStep j ω‖ ≤ params.delta) ∧
      (∀ j ≤ k + 1, ‖run.multiplier j ω‖ ≤ params.multiplierBound) := by
  -- Add the initial point to the one-based membership facts from survival.
  apply prefixBounds_of_points_mem run X h_region ω (k + 1)
  intro j hj
  by_cases hjZero : j = 0
  · subst j
    simpa only [run.point_zero] using initial_mem
  · exact (mem_survivalEvent run X k ω).mp hω j
      ⟨Nat.one_le_iff_ne_zero.mpr hjZero, by omega⟩

/-- Helper for Corollary 4.2: the active corrected transition is admissible
on its survival event. -/
theorem preExitAdmissible
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hω : ω ∈ survivalEvent run X k) :
    IsAdmissible h (run.point k ω) (run.baseStep k ω) :=
  (preExitPrefixBounds run X initial_mem h_region ω k hω).1 k
    (Nat.lt_succ_self k)

/-- Helper for Corollary 4.2: the active corrected base step has norm at most
the prescribed localization radius. -/
theorem preExitBaseStepNorm_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hω : ω ∈ survivalEvent run X k) :
    ‖run.baseStep k ω‖ ≤ params.delta :=
  (preExitPrefixBounds run X initial_mem h_region ω k hω).2.1 k
    (Nat.lt_succ_self k)

/-- Helper for Corollary 4.2: multiplier bounds on a surviving corrected prefix
imply the feasibility bound at every positive-index endpoint. -/
theorem constraintNorm_le_of_survival
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hk : 1 ≤ k)
    (hω : ω ∈ survivalEvent run X (k - 1)) :
    ‖c (run.point k ω)‖ ≤ 2 * params.multiplierBound / params.rho := by
  obtain ⟨j, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  have hsurvival : ω ∈ survivalEvent run X j := by
    simpa using hω
  have hbounds := preExitPrefixBounds run X initial_mem h_region ω j hsurvival
  have hprevious := hbounds.2.2 j (by omega)
  have hcurrent := hbounds.2.2 (j + 1) (by omega)
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point (j + 1) ω) =
        run.multiplier (j + 1) ω - run.multiplier j ω := by
    have hupdate :
        run.multiplier (j + 1) ω = run.multiplier j ω +
          (params.rho : ℝ) • c (run.point (j + 1) ω) :=
      by
        rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
    rw [hupdate]
    module
  apply (le_div_iff₀ params.spec.1.2.2.1).2
  calc
    ‖c (run.point (j + 1) ω)‖ * params.rho =
        params.rho * ‖c (run.point (j + 1) ω)‖ := by ring
    _ = ‖(params.rho : ℝ) • c (run.point (j + 1) ω)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1]
    _ = ‖run.multiplier (j + 1) ω - run.multiplier j ω‖ :=
      congrArg norm hresidualIdentity
    _ ≤ ‖run.multiplier (j + 1) ω‖ + ‖run.multiplier j ω‖ := norm_sub_le _ _
    _ ≤ 2 * params.multiplierBound := by linarith

/-- Helper for Corollary 4.2: corrected survival events decrease with the
horizon. -/
theorem survivalEvent_antitone
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) {j k : ℕ} (hjk : j ≤ k) :
    survivalEvent run X k ⊆ survivalEvent run X j := by
  -- Restrict the one-based membership interval to the shorter horizon.
  intro ω hω
  rw [mem_survivalEvent] at hω ⊢
  intro t ht
  exact hω t ⟨ht.1, ht.2.trans hjk⟩

/-- Helper for Corollary 4.2: a measurable localization set gives a
null-measurable corrected survival event. -/
theorem nullMeasurableSet_survivalEvent
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (K : ℕ) :
    NullMeasurableSet (survivalEvent run X K) P := by
  let exitEvent : Set Ω := {ω | exitTime run X ω ≤ K}
  have hexitEvent :
      exitEvent = ⋃ j ∈ Finset.Icc 1 K, run.point j ⁻¹' Xᶜ := by
    ext ω
    simp only [exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  -- Each finite point-preimage exit event is null measurable.
  have hexitNullMeasurable : NullMeasurableSet exitEvent P := by
    rw [hexitEvent]
    exact (Finset.Icc 1 K).nullMeasurableSet_biUnion fun j _hj ↦
      (run.aemeasurable_point j).nullMeasurableSet_preimage hX.compl
  have hsurvival : survivalEvent run X K = exitEventᶜ := by
    ext ω
    rw [mem_survivalEvent]
    simp only [Set.mem_compl_iff, exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  rw [hsurvival]
  exact hexitNullMeasurable.compl

/-- Helper for Corollary 4.2: clipping to a closed norm ball is measurable. -/
private lemma measurableClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  -- Split the clipping formula along its measurable norm comparison.
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Corollary 4.2: the squared corrected base step is integrable on
the event where its transition remains active. -/
theorem integrableOn_baseStepSquare_preExit
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    IntegrableOn (fun ω ↦ ‖run.baseStep k ω‖ ^ 2)
      (survivalEvent run X k) P := by
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.baseStep k ω‖ ^ 2) P :=
    ((run.aemeasurable_baseStep k).norm.pow_const 2).aestronglyMeasurable
  let C : ℝ := (params.delta : ℝ) ^ 2
  -- The pathwise invariant bounds the active square by the constant radius square.
  have hbound (ω : Ω) (hω : ω ∈ survivalEvent run X k) :
      ‖(‖run.baseStep k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    have hstep := preExitBaseStepNorm_le run X initial_mem h_region ω k hω
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg params.delta)).2 hstep
    simpa only [C, Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  have hboundAE :
      ∀ᵐ ω ∂P.restrict (survivalEvent run X k),
        ‖(‖run.baseStep k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    filter_upwards
      [ae_restrict_mem₀ (nullMeasurableSet_survivalEvent run X hX k)]
      with ω hω
    exact hbound ω hω
  have hconst : Integrable (fun _ : Ω ↦ C)
      (P.restrict (survivalEvent run X k)) := integrable_const C
  exact Integrable.mono' hconst hsquareMeasurable.restrict hboundAE

/-- Helper for Corollary 4.2: the squared corrected estimator error is
integrable on the event where its iteration remains active. -/
theorem integrableOn_gradientErrorSquare_preExit
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    IntegrableOn (fun ω ↦ ‖run.gradientError k ω‖ ^ 2)
      (survivalEvent run X k) P := by
  have hestimate : AEMeasurable (run.gradientEstimate k) P := by
    have hcomposed := (measurableClip h.gradientBound).comp_aemeasurable
      (run.aemeasurable_rawEstimate k)
    have hestimateEq :
        run.gradientEstimate k =
          SPIDER.clip h.gradientBound ∘
            SPIDER.rawEstimate oracle run.point run.sample Q B b k := by
      funext ω
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      rfl
    rw [hestimateEq]
    exact hcomposed
  have hgradientExtension :
      AEMeasurable
        (fun ω ↦ h.objectiveGradientExtension (run.point k ω))
        (P.restrict (survivalEvent run X k)) :=
    (h.measurable_objectiveGradientExtension.comp_aemeasurable
      (run.aemeasurable_point k)).restrict
  have hgradient :
      AEMeasurable (fun ω ↦ gradient f (run.point k ω))
        (P.restrict (survivalEvent run X k)) := by
    apply hgradientExtension.congr
    filter_upwards
      [ae_restrict_mem₀ (nullMeasurableSet_survivalEvent run X hX k)]
      with ω hω
    have hadmissible := preExitAdmissible run X initial_mem h_region ω k hω
    have hx : run.point k ω ∈ h.region :=
      base_mem_region h (run.point k ω) (run.baseStep k ω) hadmissible
    exact h.objectiveGradientExtension_eq hx
  have herror : AEMeasurable (run.gradientError k)
      (P.restrict (survivalEvent run X k)) := by
    have herrorEq :
        run.gradientError k =
          fun ω ↦ run.gradientEstimate k ω - gradient f (run.point k ω) := by
      funext ω
      exact run.gradientError_apply k ω
    rw [herrorEq]
    exact hestimate.restrict.sub hgradient
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2)
        (P.restrict (survivalEvent run X k)) :=
    (herror.norm.pow_const 2).aestronglyMeasurable
  let C : ℝ := (2 * (h.gradientBound : ℝ)) ^ 2
  -- Admissibility bounds the true gradient, while clipping bounds the estimate.
  have hbound (ω : Ω) (hω : ω ∈ survivalEvent run X k) :
      ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    have hadmissible := preExitAdmissible run X initial_mem h_region ω k hω
    have hx : run.point k ω ∈ h.region :=
      base_mem_region h (run.point k ω) (run.baseStep k ω) hadmissible
    have hestimateNorm : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      exact SPIDER.norm_clip_le h.gradientBound _
    have hgradientNorm : ‖gradient f (run.point k ω)‖ ≤ h.gradientBound :=
      h.norm_gradient_le _ hx
    have herrorNorm :
        ‖run.gradientError k ω‖ ≤ 2 * (h.gradientBound : ℝ) := by
      rw [run.gradientError_apply]
      calc
        ‖run.gradientEstimate k ω - gradient f (run.point k ω)‖ ≤
            ‖run.gradientEstimate k ω‖ + ‖gradient f (run.point k ω)‖ :=
          norm_sub_le _ _
        _ ≤ 2 * (h.gradientBound : ℝ) := by linarith
    have hclipBoundNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) := by positivity
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) hclipBoundNonneg).2 herrorNorm
    simpa only [C, Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  have hboundAE :
      ∀ᵐ ω ∂P.restrict (survivalEvent run X k),
        ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    filter_upwards
      [ae_restrict_mem₀ (nullMeasurableSet_survivalEvent run X hX k)]
      with ω hω
    exact hbound ω hω
  have hconst : Integrable (fun _ : Ω ↦ C)
      (P.restrict (survivalEvent run X k)) := integrable_const C
  exact Integrable.mono' hconst hsquareMeasurable hboundAE

/-- Helper for Corollary 4.2: the expected corrected base-step energy
accumulated while the run survives. -/
noncomputable def stoppedBaseStepEnergy
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ∫ ω in survivalEvent run X k, ‖run.baseStep k ω‖ ^ 2 ∂P

/-- Helper for Corollary 4.2: stopped corrected base-step energy exposes its
finite sum of restricted integrals. -/
theorem stoppedBaseStepEnergy_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) :
    stoppedBaseStepEnergy run X K =
      ∑ k ∈ Finset.range K,
        ∫ omega in survivalEvent run X k, ‖run.baseStep k omega‖ ^ 2 ∂P := by
  -- Expose the proof-free stopped base-step energy definition once.
  rfl

/-- Helper for Corollary 4.2: the expected corrected estimator-error energy
accumulated while the run survives. -/
noncomputable def stoppedGradientErrorEnergy
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ∫ ω in survivalEvent run X k, ‖run.gradientError k ω‖ ^ 2 ∂P

/-- Helper for Corollary 4.2: stopped corrected estimator-error energy exposes
its finite sum of restricted integrals. -/
theorem stoppedGradientErrorEnergy_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) :
    stoppedGradientErrorEnergy run X K =
      ∑ k ∈ Finset.range K,
        ∫ omega in survivalEvent run X k, ‖run.gradientError k omega‖ ^ 2 ∂P := by
  -- Expose the proof-free stopped estimator-error energy definition once.
  rfl

/-- Helper for Corollary 4.2: stopped corrected base-step energy is
nonnegative. -/
theorem stoppedBaseStepEnergy_nonneg
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) :
    0 ≤ stoppedBaseStepEnergy run X K := by
  -- Sum the pointwise nonnegative squared-norm integrals.
  rw [stoppedBaseStepEnergy]
  exact Finset.sum_nonneg fun k _hk ↦ integral_nonneg fun ω ↦ sq_nonneg _

/-- Helper for Corollary 4.2: stopped corrected estimator-error energy is
nonnegative. -/
theorem stoppedGradientErrorEnergy_nonneg
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) :
    0 ≤ stoppedGradientErrorEnergy run X K := by
  -- Sum the pointwise nonnegative squared-norm integrals.
  rw [stoppedGradientErrorEnergy]
  exact Finset.sum_nonneg fun k _hk ↦ integral_nonneg fun ω ↦ sq_nonneg _

end LALM.Correction.StochasticRun.Localization

end
