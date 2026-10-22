/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedSemantics
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedSemantics

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

/-- Helper for Theorem 3.7: the squared active raw-estimator error at a
finite transition index, with inactive and out-of-horizon branches set to
zero.  The measurable gradient extension is used only to make the observable
globally measurable. -/
noncomputable def activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  if hk : k < K then
    @ite ℝ (attempt.activeAt ⟨k, Nat.lt_succ_of_lt hk⟩ omega)
        (Classical.propDecidable _) (
      ‖rawEstimateAt oracle Q B b k
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega).2.1
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega).2.2.1
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega).2.2.2.2
          (attempt.batch k omega) -
        h.objectiveGradientExtension
          (attempt.point ⟨k, Nat.lt_succ_of_lt hk⟩ omega)‖ ^ 2) 0
  else 0

/-- Helper for Theorem 3.7: the squared active clipped-estimator error at a
finite transition index, again zero after localization stops or after the
horizon. -/
noncomputable def activeGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  if hk : k < K then
    @ite ℝ (attempt.activeAt ⟨k, Nat.lt_succ_of_lt hk⟩ omega)
        (Classical.propDecidable _) (
      ‖clippedEstimateAt h oracle Q B b k
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
            attempt.batch k omega) -
        h.objectiveGradientExtension
          (attempt.point ⟨k, Nat.lt_succ_of_lt hk⟩ omega)‖ ^ 2) 0
  else 0

/-- Helper for Theorem 3.7: the squared stopped base step at a finite
transition index. -/
noncomputable def activeBaseStepIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  if hk : k < K then ‖attempt.baseStep ⟨k, hk⟩ omega‖ ^ 2 else 0

/-- Helper for Theorem 3.7: the squared displacement between the endpoints
of a finite stopped transition. -/
noncomputable def activeDisplacementIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  if hk : k < K then
    ‖attempt.point (⟨k, hk⟩ : Fin K).succ omega -
      attempt.point (⟨k, hk⟩ : Fin K).castSucc omega‖ ^ 2
  else 0

/-- Helper for Theorem 3.7: each active raw-error square is nonnegative. -/
theorem activeRawGradientErrorIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeRawGradientErrorIntegrand attempt k omega := by
  unfold activeRawGradientErrorIntegrand
  split
  · split
    · exact sq_nonneg _
    · exact le_rfl
  · exact le_rfl

/-- Helper for Theorem 3.7: each active clipped-error square is nonnegative. -/
theorem activeGradientErrorIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeGradientErrorIntegrand attempt k omega := by
  unfold activeGradientErrorIntegrand
  split
  · split
    · exact sq_nonneg _
    · exact le_rfl
  · exact le_rfl

/-- Helper for Theorem 3.7: each stopped base-step square is nonnegative. -/
theorem activeBaseStepIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeBaseStepIntegrand attempt k omega := by
  unfold activeBaseStepIntegrand
  split
  · exact sq_nonneg _
  · exact le_rfl

/-- Helper for Theorem 3.7: each stopped displacement square is nonnegative. -/
theorem activeDisplacementIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeDisplacementIntegrand attempt k omega := by
  unfold activeDisplacementIntegrand
  split
  · exact sq_nonneg _
  · exact le_rfl

/-- Helper for Theorem 3.7: every finite stopped point observable is
measurable. -/
theorem measurable_point
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) : Measurable (attempt.point k) := by
  unfold StoppedAttempt.point
  exact measurable_fst.comp (measurable_snd.comp (attempt.measurable_state k))

/-- Helper for Theorem 3.7: every finite stopped base-step observable is
measurable. -/
theorem measurable_baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) : Measurable (attempt.baseStep k) := by
  unfold StoppedAttempt.baseStep
  exact (measurable_point attempt k.succ).sub
    (measurable_point attempt k.castSucc)

/-- Helper for Theorem 3.7: the finite active raw-error integrand is
measurable, including its two zero branches. -/
theorem measurable_activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : Measurable (activeRawGradientErrorIntegrand attempt k) := by
  by_cases hk : k < K
  · let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
    have hstateBatch : Measurable (fun omega ↦
        (attempt.state kfin omega, attempt.batch k omega)) :=
      (attempt.measurable_state kfin).prodMk (attempt.measurable_batch k)
    have hraw : Measurable (fun omega ↦ rawEstimateAt oracle Q B b k
        (attempt.state kfin omega).2.1
        (attempt.state kfin omega).2.2.1
        (attempt.state kfin omega).2.2.2.2
        (attempt.batch k omega)) :=
      (measurable_rawEstimateAt oracle Q B b k).comp hstateBatch
    have hgradient : Measurable (fun omega ↦
        h.objectiveGradientExtension (attempt.point kfin omega)) :=
      h.measurable_objectiveGradientExtension.comp (measurable_point attempt kfin)
    have herror : Measurable (fun omega ↦
        ‖rawEstimateAt oracle Q B b k
            (attempt.state kfin omega).2.1
            (attempt.state kfin omega).2.2.1
            (attempt.state kfin omega).2.2.2.2
            (attempt.batch k omega) -
          h.objectiveGradientExtension (attempt.point kfin omega)‖ ^ 2) :=
      (hraw.sub hgradient).norm.pow_const 2
    have hevent : MeasurableSet {omega | attempt.activeAt kfin omega} :=
      attempt.measurableSet_activeAt kfin
    have heq : activeRawGradientErrorIntegrand attempt k = fun omega ↦
        @ite ℝ (attempt.activeAt kfin omega) (Classical.propDecidable _) (
          ‖rawEstimateAt oracle Q B b k
              (attempt.state kfin omega).2.1
              (attempt.state kfin omega).2.2.1
              (attempt.state kfin omega).2.2.2.2
              (attempt.batch k omega) -
            h.objectiveGradientExtension (attempt.point kfin omega)‖ ^ 2) 0 := by
      funext omega
      simp only [activeRawGradientErrorIntegrand, dif_pos hk, kfin]
    rw [heq]
    apply Measurable.ite
    · exact hevent
    · exact herror
    · exact measurable_const
  · have heq : activeRawGradientErrorIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      rw [activeRawGradientErrorIntegrand, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Theorem 3.7: the finite active clipped-error integrand is
measurable, including its two zero branches. -/
theorem measurable_activeGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : Measurable (activeGradientErrorIntegrand attempt k) := by
  by_cases hk : k < K
  · let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
    have hstateBatch : Measurable (fun omega ↦
        (attempt.state kfin omega, attempt.batch k omega)) :=
      (attempt.measurable_state kfin).prodMk (attempt.measurable_batch k)
    have hclipped : Measurable (fun omega ↦ clippedEstimateAt h oracle Q B b k
        (attempt.state kfin omega, attempt.batch k omega)) :=
      (measurable_clippedEstimateAt k).comp hstateBatch
    have hgradient : Measurable (fun omega ↦
        h.objectiveGradientExtension (attempt.point kfin omega)) :=
      h.measurable_objectiveGradientExtension.comp (measurable_point attempt kfin)
    have herror : Measurable (fun omega ↦
        ‖clippedEstimateAt h oracle Q B b k
            (attempt.state kfin omega, attempt.batch k omega) -
          h.objectiveGradientExtension (attempt.point kfin omega)‖ ^ 2) :=
      (hclipped.sub hgradient).norm.pow_const 2
    have hevent : MeasurableSet {omega | attempt.activeAt kfin omega} :=
      attempt.measurableSet_activeAt kfin
    have heq : activeGradientErrorIntegrand attempt k = fun omega ↦
        @ite ℝ (attempt.activeAt kfin omega) (Classical.propDecidable _) (
          ‖clippedEstimateAt h oracle Q B b k
              (attempt.state kfin omega, attempt.batch k omega) -
            h.objectiveGradientExtension (attempt.point kfin omega)‖ ^ 2) 0 := by
      funext omega
      simp only [activeGradientErrorIntegrand, dif_pos hk, kfin]
    rw [heq]
    apply Measurable.ite
    · exact hevent
    · exact herror
    · exact measurable_const
  · have heq : activeGradientErrorIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      rw [activeGradientErrorIntegrand, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Theorem 3.7: every stopped base-step-square integrand is
measurable. -/
theorem measurable_activeBaseStepIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : Measurable (activeBaseStepIntegrand attempt k) := by
  by_cases hk : k < K
  · have heq : activeBaseStepIntegrand attempt k = fun omega ↦
        ‖attempt.baseStep ⟨k, hk⟩ omega‖ ^ 2 := by
      funext omega
      rw [activeBaseStepIntegrand, dif_pos hk]
    rw [heq]
    exact (measurable_baseStep attempt ⟨k, hk⟩).norm.pow_const 2
  · have heq : activeBaseStepIntegrand attempt k = fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      rw [activeBaseStepIntegrand, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Theorem 3.7: every stopped displacement-square integrand is
measurable. -/
theorem measurable_activeDisplacementIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : Measurable (activeDisplacementIntegrand attempt k) := by
  by_cases hk : k < K
  · have heq : activeDisplacementIntegrand attempt k = fun omega ↦
        ‖attempt.point (⟨k, hk⟩ : Fin K).succ omega -
          attempt.point (⟨k, hk⟩ : Fin K).castSucc omega‖ ^ 2 := by
      funext omega
      rw [activeDisplacementIntegrand, dif_pos hk]
    rw [heq]
    exact ((measurable_point attempt (⟨k, hk⟩ : Fin K).succ).sub
      (measurable_point attempt (⟨k, hk⟩ : Fin K).castSucc)).norm.pow_const 2
  · have heq : activeDisplacementIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      rw [activeDisplacementIntegrand, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Theorem 3.7: an active finite state stores a point in the
localization set. -/
theorem point_mem_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) (omega : Ω) (hactive : attempt.activeAt k omega) :
    attempt.point k omega ∈ X := by
  have hkBound : k.1 ≤ K := Nat.le_of_lt_succ k.isLt
  by_cases hkzero : k.1 = 0
  · have hidx : k = ⟨0, Nat.zero_lt_succ K⟩ := by
      apply Fin.ext
      exact hkzero
    rw [hidx]
    unfold StoppedAttempt.point
    rw [attempt.state_zero]
    exact attempt.initial_mem
  · let j : Fin K := ⟨k.1 - 1, by omega⟩
    have hsucc : j.succ = k := by
      apply Fin.ext
      dsimp [j]
      omega
    have hprev : attempt.activeAt j.castSucc omega := by
      have hprev' := attempt.activeAt_of_le omega (k.1 - 1) k.1
        (by omega) hkBound hactive
      convert hprev' using 1
      · apply Fin.ext
        rfl
    have hmem := ((attempt.activeAt_succ_iff j omega).mp (by
      rw [hsucc]
      exact hactive)).2
    rw [← attempt.point_succ_of_active j omega hprev] at hmem
    rwa [hsucc] at hmem

/-- Helper for Theorem 3.7: an active finite state lies in the regularity
region supplied by the localization buffer. -/
theorem point_mem_region_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) (omega : Ω) (hactive : attempt.activeAt k omega) :
    attempt.point k omega ∈ h.region :=
  attempt.region_condition.thickening_subset
    (Metric.self_subset_cthickening X
      (point_mem_of_active attempt k omega hactive))

/-- Helper for Theorem 3.7: clipping contracts the active finite estimator
error pointwise. -/
theorem activeGradientErrorIntegrand_le_activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    activeGradientErrorIntegrand attempt k omega ≤
      activeRawGradientErrorIntegrand attempt k omega := by
  by_cases hk : k < K
  · let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
    by_cases hactive : attempt.activeAt kfin omega
    · have hx := point_mem_region_of_active attempt kfin omega hactive
      have hgradient :
          ‖gradient f (attempt.point kfin omega)‖ ≤ h.gradientBound :=
        h.norm_gradient_le _ hx
      simp only [activeGradientErrorIntegrand, activeRawGradientErrorIntegrand,
        dif_pos hk, kfin, if_pos hactive]
      rw [h.objectiveGradientExtension_eq hx]
      rw [clippedEstimateAt_def]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (SPIDER.norm_clip_sub_le h.gradientBound _ _ hgradient) 2
    · simp only [activeGradientErrorIntegrand, activeRawGradientErrorIntegrand,
        dif_pos hk, kfin, if_neg hactive]
      exact le_rfl
  · simp only [activeGradientErrorIntegrand, activeRawGradientErrorIntegrand,
      dif_neg hk]
    exact le_rfl

/-- Theorem 3.7: the active clipped-error square is automatically
integrable; this uses only clipping and active-point localization. -/
theorem integrable_activeGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : Integrable (activeGradientErrorIntegrand attempt k) P := by
  have hbound (omega : Ω) :
      ‖activeGradientErrorIntegrand attempt k omega‖ ≤
        (2 * (h.gradientBound : ℝ)) ^ 2 := by
    by_cases hk : k < K
    · let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
      by_cases hactive : attempt.activeAt kfin omega
      · have hx := point_mem_region_of_active attempt kfin omega hactive
        have hclip := SPIDER.norm_clip_le h.gradientBound
          (rawEstimateAt oracle Q B b k
            (attempt.state kfin omega).2.1
            (attempt.state kfin omega).2.2.1
            (attempt.state kfin omega).2.2.2.2
            (attempt.batch k omega))
        have hgradient : ‖gradient f (attempt.point kfin omega)‖ ≤
            h.gradientBound := h.norm_gradient_le _ hx
        have herror :
            ‖clippedEstimateAt h oracle Q B b k
                (attempt.state kfin omega, attempt.batch k omega) -
              h.objectiveGradientExtension (attempt.point kfin omega)‖ ≤
                2 * (h.gradientBound : ℝ) := by
          rw [h.objectiveGradientExtension_eq hx]
          rw [clippedEstimateAt_def]
          calc
            _ ≤ ‖SPIDER.clip h.gradientBound _‖ +
                ‖gradient f (attempt.point kfin omega)‖ := norm_sub_le _ _
            _ ≤ 2 * (h.gradientBound : ℝ) := by linarith
        have hright : 0 ≤ 2 * (h.gradientBound : ℝ) := by positivity
        have hsquare := (sq_le_sq₀ (norm_nonneg _) hright).2 herror
        simp only [activeGradientErrorIntegrand, dif_pos hk, kfin,
          if_pos hactive, Real.norm_of_nonneg (sq_nonneg _)]
        exact hsquare
      · simp only [activeGradientErrorIntegrand, dif_pos hk, kfin,
          if_neg hactive, norm_zero]
        exact sq_nonneg _
    · simp only [activeGradientErrorIntegrand, dif_neg hk, norm_zero]
      exact sq_nonneg _
  exact Integrable.mono' (integrable_const _)
    (measurable_activeGradientErrorIntegrand attempt k).aestronglyMeasurable
    (ae_of_all P hbound)

/-- Helper for Theorem 3.7: raw-error integrability transfers to the active
zero-padded observable.  The raw moment itself remains an explicit input to
the later independence/conditional-expectation argument. -/
theorem integrable_activeRawGradientErrorIntegrand_of_integrable
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ)
    (hraw : ∀ hk : k < K, Integrable (fun omega ↦
      ‖rawEstimateAt oracle Q B b k
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega).2.1
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega).2.2.1
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega).2.2.2.2
          (attempt.batch k omega) -
        h.objectiveGradientExtension
          (attempt.point ⟨k, Nat.lt_succ_of_lt hk⟩ omega)‖ ^ 2) P) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P := by
  by_cases hk : k < K
  · have hmajorant := hraw hk
    refine Integrable.mono' hmajorant
      (measurable_activeRawGradientErrorIntegrand attempt k).aestronglyMeasurable
      (ae_of_all P fun omega ↦ ?_)
    by_cases hactive :
        attempt.activeAt ⟨k, Nat.lt_succ_of_lt hk⟩ omega
    · simp only [activeRawGradientErrorIntegrand, dif_pos hk, if_pos hactive,
        Real.norm_of_nonneg (sq_nonneg _)]
      exact le_rfl
    · simp only [activeRawGradientErrorIntegrand, dif_pos hk, if_neg hactive,
        norm_zero]
      exact sq_nonneg _
  · have heq : activeRawGradientErrorIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      rw [activeRawGradientErrorIntegrand, dif_neg hk]
    rw [heq]
    exact integrable_const _

/-- Helper for Theorem 3.7: the base stopped displacement is exactly its
stored base step, so its square has no correction factor. -/
theorem activeDisplacementIntegrand_eq_activeBaseStepIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    activeDisplacementIntegrand attempt k omega =
      activeBaseStepIntegrand attempt k omega := by
  by_cases hk : k < K
  · rw [activeDisplacementIntegrand, dif_pos hk,
      activeBaseStepIntegrand, dif_pos hk]
    rfl
  · rw [activeDisplacementIntegrand, dif_neg hk,
      activeBaseStepIntegrand, dif_neg hk]

/-- Helper for Theorem 3.7: a uniform finite base-step bound yields
integrability of the stopped step square.  Unlike the corrected state package,
the base `StoppedAttempt` does not contain this bound, so it is explicit. -/
theorem integrable_activeBaseStepIntegrand_of_bound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ)
    (hbound : ∀ (hk : k < K) (omega : Ω),
      ‖attempt.baseStep ⟨k, hk⟩ omega‖ ≤ params.delta) :
    Integrable (activeBaseStepIntegrand attempt k) P := by
  have hmajorant (omega : Ω) :
      ‖activeBaseStepIntegrand attempt k omega‖ ≤ (params.delta : ℝ) ^ 2 := by
    by_cases hk : k < K
    · have hsquare := (sq_le_sq₀ (norm_nonneg _)
          (NNReal.coe_nonneg params.delta)).2 (hbound hk omega)
      simpa only [activeBaseStepIntegrand, dif_pos hk,
        Real.norm_of_nonneg (sq_nonneg _)] using hsquare
    · simp only [activeBaseStepIntegrand, dif_neg hk, norm_zero]
      exact sq_nonneg _
  exact Integrable.mono' (integrable_const _)
    (measurable_activeBaseStepIntegrand attempt k).aestronglyMeasurable
    (ae_of_all P hmajorant)

/-- Helper for Theorem 3.7: the same explicit step bound gives
integrability of the identical stopped displacement square. -/
theorem integrable_activeDisplacementIntegrand_of_bound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ)
    (hbound : ∀ (hk : k < K) (omega : Ω),
      ‖attempt.baseStep ⟨k, hk⟩ omega‖ ≤ params.delta) :
    Integrable (activeDisplacementIntegrand attempt k) P := by
  have hstep := integrable_activeBaseStepIntegrand_of_bound attempt k hbound
  rw [funext fun omega ↦
    activeDisplacementIntegrand_eq_activeBaseStepIntegrand attempt k omega]
  exact hstep

/-- Helper for Theorem 3.7: an active successor stores its predecessor's
current point as the previous-point component. -/
theorem successor_previousPoint_eq_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) (hactive : attempt.activeAt k.castSucc omega) :
    (attempt.state k.succ omega).2.2.1 =
      (attempt.state k.castSucc omega).2.1 := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  have hz : z.1.1 = 1 := by
    simpa only [StoppedAttempt.activeAt, z] using hactive
  have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
      attempt.batch k.1 omega := by
    rfl
  rw [hbatch] at hstate
  rw [hstate, transition_of_active X k.1 z hz]
  simpa only [z] using
    (activeTransition_previousPoint h oracle params Q B b X k.1 z)

/-- Helper for Theorem 3.7: an active successor stores exactly the raw
estimate computed from its predecessor state and fresh batch. -/
theorem successor_rawEstimate_eq_of_active
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin K) (omega : Ω) (hactive : attempt.activeAt k.castSucc omega) :
    (attempt.state k.succ omega).2.2.2.2 =
      rawEstimateAt oracle Q B b k.1
        (attempt.state k.castSucc omega).2.1
        (attempt.state k.castSucc omega).2.2.1
        (attempt.state k.castSucc omega).2.2.2.2
        (attempt.batch k.1 omega) := by
  have hstate := attempt.state_succ k omega
  let z : PreBatchState n m × (ℕ → Ξ) :=
    (attempt.state k.castSucc omega, attempt.batch k.1 omega)
  have hz : z.1.1 = 1 := by
    simpa only [StoppedAttempt.activeAt, z] using hactive
  have hbatch : (fun i ↦ attempt.sample k.1 i omega) =
      attempt.batch k.1 omega := by
    rfl
  rw [hbatch] at hstate
  rw [hstate, transition_of_active X k.1 z hz]
  simpa only [z] using
    (activeTransition_rawEstimate h oracle params Q B b X k.1 z)

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
