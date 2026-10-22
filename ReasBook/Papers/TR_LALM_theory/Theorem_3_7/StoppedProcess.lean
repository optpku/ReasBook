/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Lemma_3_4
public import TR_LALM_theory.Theorem_3_7.Localization

public section

open MeasureTheory
open scoped NNReal

namespace LALM.StochasticRun.Localization

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
variable {params : LALM.Parameters h x₀ multiplier₀} {Q B b : ℕ+}
variable {confidence : ℝ}

private lemma measurableClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- If every point used by a finite prefix lies in the localization set, then
all its segments are admissible and its steps and multipliers satisfy the
uniform bounds from Lemma 3.4. -/
theorem prefixBounds_of_points_mem
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (N : ℕ)
    (hpoints : ∀ j < N, run.point j ω ∈ X) :
    (∀ j < N,
        segment ℝ (run.point j ω) (run.point (j + 1) ω) ⊆ h.region) ∧
      (∀ j < N, ‖run.step j ω‖ ≤ params.delta) ∧
      (∀ j ≤ N, ‖run.multiplier j ω‖ ≤ params.multiplierBound) := by
  induction N with
  | zero =>
      constructor
      · intro j hj
        omega
      · constructor
        · intro j hj
          omega
        · intro j hj
          have hj_zero : j = 0 := by omega
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
      have heffective := normEffectiveMultiplier_le run N ω hprev.2.2
      have hstep :=
        normStep_le_of_normEffectiveMultiplier_le run N ω hpointRegion heffective
      have hstepDistance :
          dist (run.point N ω) (run.point (N + 1) ω) ≤ params.delta := by
        calc
          dist (run.point N ω) (run.point (N + 1) ω) =
              dist (run.point (N + 1) ω) (run.point N ω) := dist_comm _ _
          _ = ‖run.step N ω‖ := by
            rw [run.point_succ, dist_eq_norm, add_sub_cancel_left]
          _ ≤ params.delta := hstep
      have hsegment :
          segment ℝ (run.point N ω) (run.point (N + 1) ω) ⊆ h.region := by
        intro y hy
        apply h_region.thickening_subset
        apply Metric.mem_cthickening_of_dist_le y (run.point N ω) params.delta X hpointX
        exact (Metric.mem_closedBall.mp
          (segment_subset_closedBall_left
            (run.point N ω) (run.point (N + 1) ω) hy)).trans hstepDistance
      have hnewMultiplier :=
        normMultiplier_succ_le_of_normStep_le run N ω hsegment hstep
      constructor
      · intro j hj
        by_cases hj_old : j < N
        · exact hprev.1 j hj_old
        · have hj_eq : j = N := by omega
          simpa only [hj_eq] using hsegment
      · constructor
        · intro j hj
          by_cases hj_old : j < N
          · exact hprev.2.1 j hj_old
          · have hj_eq : j = N := by omega
            simpa only [hj_eq] using hstep
        · intro j hj
          by_cases hj_old : j ≤ N
          · exact hprev.2.2 j hj_old
          · have hj_eq : j = N + 1 := by omega
            simpa only [hj_eq] using hnewMultiplier

/-- Survival through iteration `k` supplies the pathwise bounds needed for the
active step at iteration `k`. -/
theorem preExitPrefixBounds
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hω : ω ∈ survivalEvent run X k) :
    (∀ j < k + 1,
        segment ℝ (run.point j ω) (run.point (j + 1) ω) ⊆ h.region) ∧
      (∀ j < k + 1, ‖run.step j ω‖ ≤ params.delta) ∧
      (∀ j ≤ k + 1, ‖run.multiplier j ω‖ ≤ params.multiplierBound) := by
  apply prefixBounds_of_points_mem run X h_region ω (k + 1)
  intro j hj
  by_cases hj_zero : j = 0
  · subst j
    simpa only [run.point_zero] using initial_mem
  · exact (mem_survivalEvent run X k ω).mp hω j
      ⟨Nat.one_le_iff_ne_zero.mpr hj_zero, by omega⟩

/-- On the active event at iteration `k`, the next step segment is admissible. -/
theorem preExitSegment
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hω : ω ∈ survivalEvent run X k) :
    segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region :=
  (preExitPrefixBounds run X initial_mem h_region ω k hω).1 k (Nat.lt_succ_self k)

/-- On the active event at iteration `k`, the next primal step has norm at
most the localization radius. -/
theorem preExitStepNorm_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (k : ℕ) (hω : ω ∈ survivalEvent run X k) :
    ‖run.step k ω‖ ≤ params.delta :=
  (preExitPrefixBounds run X initial_mem h_region ω k hω).2.1 k
    (Nat.lt_succ_self k)

/-- The multiplier bounds on a surviving prefix imply the feasibility bound
for every positive-index point at its endpoint. -/
theorem constraintNorm_le_of_survival
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
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
      run.multiplier_succ j ω
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

/-- Survival events decrease with the horizon. -/
theorem survivalEvent_antitone
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) {j k : ℕ} (hjk : j ≤ k) :
    survivalEvent run X k ⊆ survivalEvent run X j := by
  intro ω hω
  rw [mem_survivalEvent] at hω ⊢
  intro t ht
  exact hω t ⟨ht.1, ht.2.trans hjk⟩

/-- A measurable localization set gives a null-measurable survival event. -/
theorem nullMeasurableSet_survivalEvent
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (K : ℕ) :
    NullMeasurableSet (survivalEvent run X K) ℙ := by
  let exitEvent : Set Ω := {ω | exitTime run X ω ≤ K}
  have hexitEvent :
      exitEvent = ⋃ j ∈ Finset.Icc 1 K, run.point j ⁻¹' Xᶜ := by
    ext ω
    simp only [exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  have hexitNullMeasurable : NullMeasurableSet exitEvent ℙ := by
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

/-- Helper for Theorem 3.7: the squared primal step is integrable on the event
where its iteration is still active. -/
theorem integrableOn_stepSquare_preExit
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    IntegrableOn (fun ω ↦ ‖run.step k ω‖ ^ 2)
      (survivalEvent run X k) ℙ := by
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.step k ω‖ ^ 2) ℙ :=
    ((run.aemeasurable_step k).norm.pow_const 2).aestronglyMeasurable
  let C : ℝ := (params.delta : ℝ) ^ 2
  have hbound (ω : Ω) (hω : ω ∈ survivalEvent run X k) :
      ‖(‖run.step k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    have hstep := preExitStepNorm_le run X initial_mem h_region ω k hω
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg params.delta)).2 hstep
    simpa only [C, Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  have hboundAE :
      ∀ᵐ ω ∂ℙ.restrict (survivalEvent run X k),
        ‖(‖run.step k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    filter_upwards
      [ae_restrict_mem₀ (nullMeasurableSet_survivalEvent run X hX k)]
      with ω hω
    exact hbound ω hω
  have hconst : Integrable (fun _ : Ω ↦ C)
      (ℙ.restrict (survivalEvent run X k)) := integrable_const C
  exact Integrable.mono' hconst hsquareMeasurable.restrict hboundAE

/-- The squared projected-gradient error is integrable on the event where its
iteration is still active. -/
theorem integrableOn_gradientErrorSquare_preExit
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    IntegrableOn (fun ω ↦ ‖run.gradientError k ω‖ ^ 2)
      (survivalEvent run X k) ℙ := by
  have hestimate : AEMeasurable (run.gradientEstimate k) ℙ := by
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
        (ℙ.restrict (survivalEvent run X k)) :=
    (h.measurable_objectiveGradientExtension.comp_aemeasurable
      (run.aemeasurable_point k)).restrict
  have hgradient :
      AEMeasurable (fun ω ↦ gradient f (run.point k ω))
        (ℙ.restrict (survivalEvent run X k)) := by
    apply hgradientExtension.congr
    filter_upwards
      [ae_restrict_mem₀ (nullMeasurableSet_survivalEvent run X hX k)]
      with ω hω
    have hx : run.point k ω ∈ h.region :=
      preExitSegment run X initial_mem h_region ω k hω
        (left_mem_segment ℝ _ _)
    exact h.objectiveGradientExtension_eq hx
  have herror : AEMeasurable (run.gradientError k)
      (ℙ.restrict (survivalEvent run X k)) := by
    have herrorEq :
        run.gradientError k =
          fun ω ↦ run.gradientEstimate k ω - gradient f (run.point k ω) := by
      funext ω
      exact run.gradientError_apply k ω
    rw [herrorEq]
    exact hestimate.restrict.sub hgradient
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2)
        (ℙ.restrict (survivalEvent run X k)) :=
    (herror.norm.pow_const 2).aestronglyMeasurable
  let C : ℝ := (2 * (h.gradientBound : ℝ)) ^ 2
  have hbound (ω : Ω) (hω : ω ∈ survivalEvent run X k) :
      ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    have hx : run.point k ω ∈ h.region :=
      preExitSegment run X initial_mem h_region ω k hω
        (left_mem_segment ℝ _ _)
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
      ∀ᵐ ω ∂ℙ.restrict (survivalEvent run X k),
        ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤ C := by
    filter_upwards
      [ae_restrict_mem₀ (nullMeasurableSet_survivalEvent run X hX k)]
      with ω hω
    exact hbound ω hω
  have hconst : Integrable (fun _ : Ω ↦ C)
      (ℙ.restrict (survivalEvent run X k)) := integrable_const C
  exact Integrable.mono' hconst hsquareMeasurable hboundAE

/-- The expected active-step energy accumulated before exit. -/
@[expose] noncomputable def stoppedStepEnergy
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ∫ ω in survivalEvent run X k, ‖run.step k ω‖ ^ 2 ∂ℙ

/-- The expected active estimator-error energy accumulated before exit. -/
@[expose] noncomputable def stoppedErrorEnergy
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    ∫ ω in survivalEvent run X k, ‖run.gradientError k ω‖ ^ 2 ∂ℙ

theorem stoppedStepEnergy_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) :
    0 ≤ stoppedStepEnergy run X K := by
  rw [stoppedStepEnergy]
  exact Finset.sum_nonneg fun k _hk ↦ integral_nonneg fun ω ↦ sq_nonneg _

theorem stoppedErrorEnergy_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) :
    0 ≤ stoppedErrorEnergy run X K := by
  rw [stoppedErrorEnergy]
  exact Finset.sum_nonneg fun k _hk ↦ integral_nonneg fun ω ↦ sq_nonneg _

end LALM.StochasticRun.Localization

end

open LALM.StochasticRun
