/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Remark 15.38: the pushed-forward law of `X n` viewed as a measure on `ℝ`. -/
noncomputable def centeredUnitVarianceLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_aemeasurable : ∀ n, AEMeasurable (X n) P) :
    ℕ → Measure ℝ :=
  fun n ↦
    ((ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX_aemeasurable n) : ProbabilityMeasure ℝ) :
      Measure ℝ)

/-- Helper for Remark 15.38: a norm-tail event for the law of `X n` is the corresponding preimage
event under `X n`. -/
lemma centeredUnitVarianceLaw_normTail_eq_preimage
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_aemeasurable : ∀ n, AEMeasurable (X n) P) (n : ℕ) (K : ℝ) :
    centeredUnitVarianceLaw P X hX_aemeasurable n {x | K < ‖x‖} =
      P {ω | K < ‖X n ω‖} := by
  -- Rewrite the pushed-forward law on the measurable norm tail.
  rw [centeredUnitVarianceLaw, ProbabilityMeasure.map_apply']
  · rfl
  · exact measurableSet_lt measurable_const measurable_norm

/-- Helper for Remark 15.38: each centered unit-variance law has the uniform quadratic norm-tail
bound coming from Chebyshev's inequality. -/
lemma centeredUnitVarianceLaw_normTail_le_invSq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_aemeasurable : ∀ n, AEMeasurable (X n) P)
    (hX_mean : ∀ n, P[X n] = 0)
    (hX_var : ∀ n, Var[X n; P] = 1)
    (n : ℕ) {K : ℝ} (hK : 0 < K) :
    centeredUnitVarianceLaw P X hX_aemeasurable n {x | K < ‖x‖} ≤
      ENNReal.ofReal (1 / K ^ 2) := by
  -- First rewrite the tail event for the law as an event on the original space.
  rw [centeredUnitVarianceLaw_normTail_eq_preimage P X hX_aemeasurable n K]
  -- Chebyshev applies because nonzero variance forces `X n` to lie in `L²`.
  have h_memLp : MemLp (X n) 2 P := by
    refine memLp_two_of_variance_ne_zero (μ := P) (X := X n)
      (hX_aemeasurable n).aestronglyMeasurable ?_
    simp [hX_var n]
  -- The strict tail is contained in the closed Chebyshev event after centering by the mean.
  have h_event :
      P {ω | K < ‖X n ω‖} ≤ P {ω | K ≤ |X n ω - P[X n]|} := by
    refine measure_mono ?_
    intro ω hω
    simpa [Real.norm_eq_abs, hX_mean n] using le_of_lt hω
  exact h_event.trans <| by
    simpa [hX_var n] using
      (meas_ge_le_variance_div_sq (μ := P) (X := X n) h_memLp hK)

/-- Helper for Remark 15.38: the quadratic tail bound is uniform over the whole range of laws. -/
lemma centeredUnitVarianceLaw_uniformNormTail_le_invSq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_aemeasurable : ∀ n, AEMeasurable (X n) P)
    (hX_mean : ∀ n, P[X n] = 0)
    (hX_var : ∀ n, Var[X n; P] = 1)
    {K : ℝ} (hK : 0 < K) :
    (⨆ μ ∈ Set.range (centeredUnitVarianceLaw P X hX_aemeasurable), μ {x | K < ‖x‖}) ≤
      ENNReal.ofReal (1 / K ^ 2) := by
  -- Evaluate the supremum on a representative law from the range.
  refine iSup₂_le fun μ hμ ↦ ?_
  rcases hμ with ⟨n, rfl⟩
  exact centeredUnitVarianceLaw_normTail_le_invSq P X hX_aemeasurable hX_mean hX_var n hK

-- Proof sketch: apply Chebyshev's inequality to each law `ProbabilityMeasure.map ⟨P, inferInstance⟩
-- (hX_aemeasurable n)` at level `K`, use `hX_mean` and `hX_var` to rewrite the second-moment
-- bound as `1 / K^2`, and conclude with the canonical norm-tail tightness criterion
-- `isTightMeasureSet_of_tendsto_measure_norm_gt` on `ℝ`.
/-- Remark 15.38: a sequence of centered real random variables with variance `1` has a tight
family of laws. -/
theorem laws_of_centered_unit_variance_sequence_are_tight
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_aemeasurable : ∀ n, AEMeasurable (X n) P)
    (hX_mean : ∀ n, P[X n] = 0)
    (hX_var : ∀ n, Var[X n; P] = 1) :
    IsTightMeasureSet
      (Set.range fun n : ℕ ↦
        ((ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX_aemeasurable n) : ProbabilityMeasure ℝ) :
          Measure ℝ)) := by
  -- The quadratic comparison function tends to `0` along `atTop`.
  have h_invSq_tendsto :
      Filter.Tendsto (fun K : ℝ ↦ ENNReal.ofReal (1 / K ^ 2)) Filter.atTop (nhds 0) := by
    -- Reduce the ENNReal limit to the real-variable fact `1 / K^2 → 0`.
    have h_invSq_real : Filter.Tendsto (fun K : ℝ ↦ 1 / K ^ 2) Filter.atTop (nhds (0 : ℝ)) := by
      simpa [one_div] using
        (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (p := 0) (q := 2) (by norm_num : 0 < 2))
    simpa using ENNReal.tendsto_ofReal h_invSq_real
  -- Eventually every tail supremum is controlled by the same quadratic bound.
  have h_eventually_bound :
      ∀ᶠ K : ℝ in Filter.atTop,
        (⨆ μ ∈ Set.range (centeredUnitVarianceLaw P X hX_aemeasurable), μ {x | K < ‖x‖}) ≤
          ENNReal.ofReal (1 / K ^ 2) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with K hK
    exact centeredUnitVarianceLaw_uniformNormTail_le_invSq
      P X hX_aemeasurable hX_mean hX_var hK
  -- Squeeze the tail supremum to `0` and invoke the norm-tail tightness criterion.
  have h_tail_tendsto :
      Filter.Tendsto
        (fun K : ℝ ↦
          ⨆ μ ∈ Set.range (centeredUnitVarianceLaw P X hX_aemeasurable), μ {x | K < ‖x‖})
        Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h_invSq_tendsto
        (Filter.Eventually.of_forall fun K ↦ zero_le _)
        h_eventually_bound
  simpa [centeredUnitVarianceLaw] using
    (MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt
      (S := Set.range (centeredUnitVarianceLaw P X hX_aemeasurable)) h_tail_tendsto)
