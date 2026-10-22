/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_32

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

section LawLevel

variable {E : Type*} [MeasurableSpace E]

/- Exercise 15.4.5 uses the Chapter 13 law-level tail criterion for one fixed observable tested
against a sequence of probability laws. The original helper module is currently unavailable in this
workspace, so we localize just the small owner-facing API needed by this file. -/
/-- A real-valued function is uniformly integrable with respect to a sequence of probability
measures when the supremum of its strict-tail first moments tends to `0`. -/
private def uniformlyIntegrableWithRespectToProbabilitySequence
    (f : E → ℝ) (μs : ℕ → ProbabilityMeasure E) : Prop :=
  (⨅ a : {a : ℝ // 0 < a},
      ⨆ n : ℕ,
        ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0

/-- Helper for Exercise 15.4.5: the tail `iInf/iSup` criterion is equivalent to the usual
`ε`-tail formulation. -/
private theorem uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} :
    uniformlyIntegrableWithRespectToProbabilitySequence f μs ↔
      ∀ ε : ℝ, 0 < ε → ∃ a : {a : ℝ // 0 < a},
        ∀ n, ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)
          ≤ ENNReal.ofReal ε := by
  constructor
  · intro hUI ε hε
    rw [uniformlyIntegrableWithRespectToProbabilitySequence] at hUI
    change sInf (Set.range fun a : {a : ℝ // 0 < a} ↦
      ⨆ n : ℕ, ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0 at hUI
    rw [sInfRange_eq_zero_iff_forall_epsilon] at hUI
    obtain ⟨a, ha⟩ := hUI ε hε
    refine ⟨a, fun n ↦ ?_⟩
    exact le_of_lt <|
      lt_of_le_of_lt
        (le_iSup (fun n ↦ ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x|
          ∂(μs n : Measure E)) n)
        ha
  · intro hε
    rw [uniformlyIntegrableWithRespectToProbabilitySequence]
    change sInf (Set.range fun a : {a : ℝ // 0 < a} ↦
      ⨆ n : ℕ, ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0
    rw [sInfRange_eq_zero_iff_forall_epsilon]
    intro ε hε_pos
    obtain ⟨a, ha⟩ := hε (ε / 2) (half_pos hε_pos)
    refine ⟨a, lt_of_le_of_lt (iSup_le fun n ↦ ha n) ?_⟩
    simpa using (ENNReal.ofReal_lt_ofReal_iff hε_pos).2 (by linarith : ε / 2 < ε)

/-- Helper for Exercise 15.4.5: a restricted strict-tail integral can be rewritten as the
lintegral of the codomain strict-tail indicator. -/
private lemma lintegral_strictTailAbsIndicator_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : AEMeasurable g μ) (a : ℝ) :
    ∫⁻ x in {x | a < |g x|}, ENNReal.ofReal |g x| ∂μ =
      ∫⁻ x, Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) (g x) ∂μ := by
  have hs : NullMeasurableSet {x | a < |g x|} μ := by
    simpa [Real.norm_eq_abs] using hg.norm.nullMeasurableSet_preimage measurableSet_Ioi
  rw [← lintegral_indicator₀ hs]
  refine lintegral_congr_ae ?_
  filter_upwards with x
  simp [Set.indicator]

/-- Helper for Exercise 15.4.5: the pointwise absolute value is controlled by a cutoff plus its
strict tail. -/
private lemma abs_le_cutoff_add_strictTailAbsIndicator {A y : ℝ} (hA : 0 ≤ A) :
    |y| ≤ A + Set.indicator {t : ℝ | A < |t|} (fun t ↦ |t|) y := by
  by_cases hy : A < |y|
  · have : |y| ≤ |y| + A := by linarith
    simpa [hy, add_comm] using this
  · simpa [hy] using le_of_not_gt hy

/-- Helper for Exercise 15.4.5: larger strict-tail cutoffs produce smaller indicator integrands. -/
private lemma strictTailAbsIndicator_mono {a b y : ℝ} (hab : a ≤ b) :
    Set.indicator {t : ℝ | b < |t|} (fun t ↦ ENNReal.ofReal |t|) y ≤
      Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) y := by
  by_cases hy : b < |y|
  · have hy' : a < |y| := lt_of_le_of_lt hab hy
    simp [hy, hy']
  · simp [hy]

end LawLevel

section LawLevelMetric

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Exercise 15.4.5: the real-valued strict-tail absolute-value observable is
measurable. -/
private lemma measurableRealStrictTailAbsIndicator (a : ℝ) :
    Measurable (fun y : ℝ ↦ Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) y) := by
  exact Measurable.indicator measurable_abs <| measurableSet_lt measurable_const measurable_abs

/-- Helper for Exercise 15.4.5: the bounded continuous cutoff `x ↦ min |f x| N`. -/
private def absCutoffContinuous {f : E → ℝ} (hf_cont : Continuous f) (N : ℕ) :
    BoundedContinuousFunction E ℝ where
  toFun := fun x ↦ min |f x| (N : ℝ)
  continuous_toFun := hf_cont.abs.min continuous_const
  map_bounded' := by
    refine ⟨2 * (N : ℝ), ?_⟩
    intro x y
    have hx : |min |f x| (N : ℝ)| ≤ (N : ℝ) := by
      have hnonneg : 0 ≤ min |f x| (N : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg _)
      rw [abs_of_nonneg hnonneg]
      exact min_le_right _ _
    have hy : |min |f y| (N : ℝ)| ≤ (N : ℝ) := by
      have hnonneg : 0 ≤ min |f y| (N : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg _)
      rw [abs_of_nonneg hnonneg]
      exact min_le_right _ _
    calc
      dist (min |f x| (N : ℝ)) (min |f y| (N : ℝ))
          = |min |f x| (N : ℝ) - min |f y| (N : ℝ)| := by simp [Real.dist_eq]
      _ ≤ |min |f x| (N : ℝ)| + |min |f y| (N : ℝ)| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (min |f x| (N : ℝ)) (-(min |f y| (N : ℝ)))
      _ ≤ 2 * (N : ℝ) := by linarith

/-- Helper for Exercise 15.4.5: the continuous clamp `x ↦ max (-N) (min (f x) N)` is uniformly
bounded by `N`. -/
private lemma abs_clampNat_le (N : ℕ) (y : ℝ) :
    |max (-(N : ℝ)) (min y (N : ℝ))| ≤ (N : ℝ) := by
  have hupper : max (-(N : ℝ)) (min y (N : ℝ)) ≤ (N : ℝ) := by
    exact max_le (by linarith) (min_le_right _ _)
  have hlower : -(N : ℝ) ≤ max (-(N : ℝ)) (min y (N : ℝ)) := le_max_left _ _
  exact abs_le.2 ⟨by linarith, hupper⟩

/-- Helper for Exercise 15.4.5: the bounded continuous symmetric clamp of `f` at level `N`. -/
private def clampContinuous {f : E → ℝ} (hf_cont : Continuous f) (N : ℕ) :
    BoundedContinuousFunction E ℝ where
  toFun := fun x ↦ max (-(N : ℝ)) (min (f x) (N : ℝ))
  continuous_toFun := Continuous.max continuous_const (hf_cont.min continuous_const)
  map_bounded' := by
    refine ⟨2 * (N : ℝ), ?_⟩
    intro x y
    have hx : |max (-(N : ℝ)) (min (f x) (N : ℝ))| ≤ (N : ℝ) := abs_clampNat_le N (f x)
    have hy : |max (-(N : ℝ)) (min (f y) (N : ℝ))| ≤ (N : ℝ) := abs_clampNat_le N (f y)
    calc
      dist (max (-(N : ℝ)) (min (f x) (N : ℝ))) (max (-(N : ℝ)) (min (f y) (N : ℝ)))
          = |max (-(N : ℝ)) (min (f x) (N : ℝ)) -
              max (-(N : ℝ)) (min (f y) (N : ℝ))| := by
                simp [Real.dist_eq]
      _ ≤ |max (-(N : ℝ)) (min (f x) (N : ℝ))| +
            |max (-(N : ℝ)) (min (f y) (N : ℝ))| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (max (-(N : ℝ)) (min (f x) (N : ℝ)))
                  (-(max (-(N : ℝ)) (min (f y) (N : ℝ))))
      _ ≤ 2 * (N : ℝ) := by linarith

/-- Helper for Exercise 15.4.5: the clamp error is supported on the strict tail and is bounded by
`|y|` there. -/
private lemma abs_sub_clampNat_le_strictTailAbsIndicator (N : ℕ) (y : ℝ) :
    |y - max (-(N : ℝ)) (min y (N : ℝ))| ≤
      Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) y := by
  by_cases hy : (N : ℝ) < |y|
  · by_cases hy_nonneg : 0 ≤ y
    · have hNy : (N : ℝ) < y := by simpa [abs_of_nonneg hy_nonneg] using hy
      have hclamp : max (-(N : ℝ)) (min y (N : ℝ)) = (N : ℝ) := by
        rw [min_eq_right (le_of_lt hNy), max_eq_right]
        linarith
      have hsub : 0 ≤ y - (N : ℝ) := by linarith
      rw [hclamp, abs_of_nonneg hsub]
      rw [show Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) y = |y| by simp [hy]]
      rw [abs_of_nonneg hy_nonneg]
      linarith
    · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
      have hyN : y < -(N : ℝ) := by
        have : (N : ℝ) < -y := by simpa [abs_of_neg hy_neg] using hy
        linarith
      have hclamp : max (-(N : ℝ)) (min y (N : ℝ)) = -(N : ℝ) := by
        have hy_le : y ≤ (N : ℝ) := by linarith
        rw [min_eq_left hy_le, max_eq_left (le_of_lt hyN)]
      have hsub : y + (N : ℝ) < 0 := by linarith
      rw [hclamp, show y - (-(N : ℝ)) = y + (N : ℝ) by ring, abs_of_neg hsub]
      rw [show Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) y = |y| by simp [hy]]
      rw [abs_of_neg hy_neg]
      linarith
  · have hy_le : |y| ≤ (N : ℝ) := le_of_not_gt hy
    have hy_bounds : -(N : ℝ) ≤ y ∧ y ≤ (N : ℝ) := abs_le.mp hy_le
    have hclamp : max (-(N : ℝ)) (min y (N : ℝ)) = y := by
      rw [min_eq_left hy_bounds.2, max_eq_right hy_bounds.1]
    rw [hclamp]
    simp [hy]

/-- Helper for Exercise 15.4.5: the real strict-tail indicator integral is the corresponding
tail `lintegral` written back in `ℝ`. -/
private lemma integral_strictTailAbsIndicator_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : AEStronglyMeasurable g μ) (_hgi : Integrable g μ) (a : ℝ) :
    ∫ x, Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) (g x) ∂μ =
      (∫⁻ x in {x | a < |g x|}, ENNReal.ofReal |g x| ∂μ).toReal := by
  have htail_sm :
      AEStronglyMeasurable (fun x ↦ Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) (g x)) μ :=
    (measurableRealStrictTailAbsIndicator a).aestronglyMeasurable.comp_aemeasurable hg.aemeasurable
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦ by
      by_cases hx : a < |g x| <;> simp [hx, Set.indicator])
    htail_sm]
  have hpoint :
      (∫⁻ x, ENNReal.ofReal (Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) (g x)) ∂μ) =
        ∫⁻ x, Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) (g x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    by_cases hx : a < |g x| <;> simp [hx, Set.indicator]
  rw [hpoint]
  simpa using congrArg ENNReal.toReal (lintegral_strictTailAbsIndicator_eq hg.aemeasurable a).symm

/-- Helper for Exercise 15.4.5: if `f` is continuous, uniformly integrable with respect to
probability laws `μₙ`, and `μₙ` converges weakly to `μ`, then `f` is integrable under `μ` and the
integrals converge. -/
private theorem integrable_and_tendsto_integral_of_continuous_of_uniformlyIntegrableProbabilitySequence
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hf_cont : Continuous f)
    (hf_ui : uniformlyIntegrableWithRespectToProbabilitySequence f μs)
    (hμs : Tendsto μs atTop (𝓝 μ)) :
    Integrable f (μ : Measure E) ∧
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  have hε_form :=
    (uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon).1 hf_ui
  obtain ⟨aOne, haOne⟩ := hε_form 1 zero_lt_one
  let B : ℝ := aOne.1 + 1
  have hμs_abs_lintegral_bound :
      ∀ n, ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E) ≤ ENNReal.ofReal B := by
    intro n
    have hpoint :
        ∀ x, ENNReal.ofReal |f x| ≤
          ENNReal.ofReal aOne.1 +
            Set.indicator {t : ℝ | aOne.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x) := by
      intro x
      by_cases hx : aOne.1 < |f x|
      · simp [Set.indicator, hx]
      · exact by
          simp [Set.indicator, hx]
          exact ENNReal.ofReal_le_ofReal (le_of_not_gt hx)
    have hnonneg_aOne : 0 ≤ aOne.1 := le_of_lt aOne.2
    calc
      ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E)
          ≤ ∫⁻ x,
              ENNReal.ofReal aOne.1 +
                Set.indicator {t : ℝ | aOne.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
                ∂(μs n : Measure E) := by
                  exact lintegral_mono hpoint
      _ = ENNReal.ofReal aOne.1 +
            ∫⁻ x, Set.indicator {t : ℝ | aOne.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
              ∂(μs n : Measure E) := by
                rw [lintegral_add_left measurable_const]
                simp
      _ = ENNReal.ofReal aOne.1 +
            ∫⁻ x in {x | aOne.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
                rw [← lintegral_strictTailAbsIndicator_eq hf_cont.measurable.aemeasurable]
      _ ≤ ENNReal.ofReal aOne.1 + ENNReal.ofReal 1 := by
            gcongr
            exact haOne n
      _ = ENNReal.ofReal B := by
            simpa [B] using (ENNReal.ofReal_add hnonneg_aOne zero_le_one).symm
  have hf_integrable_seq : ∀ n, Integrable f (μs n : Measure E) := by
    intro n
    have hlt :
        ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E) < ∞ := by
      exact lt_of_le_of_lt (hμs_abs_lintegral_bound n) (by simpa using ENNReal.ofReal_lt_top)
    have hAbsInt :
        Integrable (fun x : E ↦ |f x|) (μs n : Measure E) :=
      (lintegral_ofReal_ne_top_iff_integrable (hf_cont.abs.measurable.aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ abs_nonneg (f x))).1 (ne_of_lt hlt)
    exact (integrable_norm_iff hf_cont.measurable.aestronglyMeasurable).1 <| by
      simpa [Real.norm_eq_abs] using hAbsInt
  have hcutoff_bound : ∀ N : ℕ, ∫ x, absCutoffContinuous hf_cont N x ∂(μ : Measure E) ≤ B := by
    intro N
    have hcutoff_tendsto :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hμs (absCutoffContinuous hf_cont N)
    have hcutoff_seq_bound :
        ∀ n, ∫ x, absCutoffContinuous hf_cont N x ∂(μs n : Measure E) ≤ B := by
      intro n
      have hcutoff_int :
          Integrable (absCutoffContinuous hf_cont N : E → ℝ) (μs n : Measure E) :=
        (absCutoffContinuous hf_cont N).integrable (μs n : Measure E)
      have hlintegral_bound :
          ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μs n : Measure E) ≤
            ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
        refine lintegral_mono fun x ↦ ?_
        exact ENNReal.ofReal_le_ofReal <| min_le_left _ _
      have hnonneg :
          0 ≤ᵐ[(μs n : Measure E)] fun x ↦ absCutoffContinuous hf_cont N x :=
        Eventually.of_forall fun x ↦ le_min (abs_nonneg _) (Nat.cast_nonneg _)
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hcutoff_int.aestronglyMeasurable]
      refine ENNReal.toReal_le_of_le_ofReal (by
        dsimp [B]
        linarith [aOne.2]) ?_
      exact le_trans hlintegral_bound (hμs_abs_lintegral_bound n)
    exact le_of_tendsto hcutoff_tendsto (Eventually.of_forall hcutoff_seq_bound)
  have hμ_abs_lintegral_bound :
      ∫⁻ x, ENNReal.ofReal |f x| ∂(μ : Measure E) ≤ ENNReal.ofReal B := by
    have hcutoff_lintegral_tendsto :
        Tendsto
          (fun N : ℕ ↦
            ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E))
          atTop
          (𝓝 (∫⁻ x, ENNReal.ofReal |f x| ∂(μ : Measure E))) := by
      refine lintegral_tendsto_of_tendsto_of_monotone
        (fun N ↦ (hf_cont.abs.min continuous_const).measurable.aemeasurable.ennreal_ofReal) ?_ ?_
      · filter_upwards with x N M hNM
        exact ENNReal.ofReal_le_ofReal <| min_le_min_left _ (Nat.cast_le.mpr hNM)
      · filter_upwards with x
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_atTop (Nat.ceil |f x|)] with N hN
        have hN' : |f x| < (N : ℝ) := by
          exact lt_of_le_of_lt (Nat.le_ceil |f x|) (by exact_mod_cast hN)
        have hmin : min |f x| (N : ℝ) = |f x| := min_eq_left (le_of_lt hN')
        -- Proof comment: normalize the cutoff application to its `min` normal form before
        -- applying the eventual equality `min |f x| N = |f x|`.
        simpa [absCutoffContinuous, hmin]
    have hcutoff_lintegral_bound :
        ∀ N : ℕ,
          ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E) ≤
            ENNReal.ofReal B := by
      intro N
      have hcutoff_int :
          Integrable (absCutoffContinuous hf_cont N : E → ℝ) (μ : Measure E) :=
        (absCutoffContinuous hf_cont N).integrable (μ : Measure E)
      have hnonneg :
          0 ≤ᵐ[(μ : Measure E)] fun x ↦ absCutoffContinuous hf_cont N x :=
        Eventually.of_forall fun x ↦ le_min (abs_nonneg _) (Nat.cast_nonneg _)
      have hreal_bound := hcutoff_bound N
      have h_eq :
          ∫ x, absCutoffContinuous hf_cont N x ∂(μ : Measure E) =
            (∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E)).toReal := by
        exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hcutoff_int.aestronglyMeasurable
      have : (∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E)).toReal ≤ B := by
        simpa [h_eq] using hreal_bound
      have hlt :
          ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E) < ∞ := by
        exact lt_of_le_of_lt
          (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal <| min_le_right _ _)
          (by simpa using ENNReal.ofReal_lt_top)
      exact (ENNReal.le_ofReal_iff_toReal_le (ne_of_lt hlt) (by
        dsimp [B]
        linarith [aOne.2])).2 this
    exact le_of_tendsto hcutoff_lintegral_tendsto (Eventually.of_forall hcutoff_lintegral_bound)
  have hf_integrable : Integrable f (μ : Measure E) := by
    have hAbsInt :
        Integrable (fun x : E ↦ |f x|) (μ : Measure E) :=
      (lintegral_ofReal_ne_top_iff_integrable (hf_cont.abs.measurable.aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ abs_nonneg (f x))).1 <|
        ne_of_lt (lt_of_le_of_lt hμ_abs_lintegral_bound (by simpa using ENNReal.ofReal_lt_top))
    exact (integrable_norm_iff hf_cont.measurable.aestronglyMeasurable).1 <| by
      simpa [Real.norm_eq_abs] using hAbsInt
  have hμ_tail_tendsto :
      Tendsto
        (fun N : ℕ ↦
          ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E))
        atTop (𝓝 0) := by
    have htail_tendsto :
        Tendsto
          (fun N : ℕ ↦
            ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E))
          atTop
          (𝓝 (∫ x, (0 : ℝ) ∂(μ : Measure E))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (μ := (μ : Measure E))
        (F := fun N : ℕ ↦ fun x ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
        (f := fun _ ↦ (0 : ℝ))
        (fun x ↦ |f x|) ?_ ?_ hf_integrable.norm ?_
      · exact Eventually.of_forall fun N ↦
          (measurableRealStrictTailAbsIndicator (N : ℝ)).aestronglyMeasurable.comp_aemeasurable
            hf_cont.measurable.aemeasurable
      · refine Eventually.of_forall fun N ↦ ?_
        filter_upwards with x
        by_cases hx : (N : ℝ) < |f x| <;> simp [hx, Set.indicator]
      · filter_upwards with x
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_atTop (Nat.ceil |f x|)] with N hN
        have hN' : |f x| < (N : ℝ) := by
          exact lt_of_le_of_lt (Nat.le_ceil |f x|) (by exact_mod_cast hN)
        have hx : ¬ (N : ℝ) < |f x| := not_lt_of_ge (le_of_lt hN')
        simp [hx, Set.indicator]
    simpa using htail_tendsto
  constructor
  · exact hf_integrable
  ·
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨aε, haε⟩ := hε_form (ε / 3) (by positivity)
    have hμ_tail_eventually :
        ∀ᶠ N : ℕ in atTop,
          ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) <
            ε / 3 := by
      exact hμ_tail_tendsto.eventually (Iio_mem_nhds (by positivity))
    obtain ⟨Nμ, hNμ⟩ := Filter.eventually_atTop.1 hμ_tail_eventually
    let N : ℕ := max Nμ (Nat.ceil aε.1)
    have haε_le_N : aε.1 ≤ (N : ℝ) := by
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right Nμ (Nat.ceil aε.1))
    have htail_seq_small :
        ∀ n,
          ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μs n : Measure E) ≤
            ε / 3 := by
      intro n
      have htail_lintegral_le :
          ∫⁻ x in {x | (N : ℝ) < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) ≤
            ENNReal.ofReal (ε / 3) := by
        calc
          ∫⁻ x in {x | (N : ℝ) < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)
              = ∫⁻ x,
                  Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
                  ∂(μs n : Measure E) := by
                    exact lintegral_strictTailAbsIndicator_eq hf_cont.measurable.aemeasurable (N : ℝ)
          _ ≤ ∫⁻ x,
                Set.indicator {t : ℝ | aε.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
                ∂(μs n : Measure E) := by
                  refine lintegral_mono fun x ↦ ?_
                  exact strictTailAbsIndicator_mono haε_le_N
          _ = ∫⁻ x in {x | aε.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
                symm
                exact lintegral_strictTailAbsIndicator_eq hf_cont.measurable.aemeasurable aε.1
          _ ≤ ENNReal.ofReal (ε / 3) := haε n
      have htail_real_eq :=
        integral_strictTailAbsIndicator_eq hf_cont.measurable.aestronglyMeasurable
          (hf_integrable_seq n) (N : ℝ)
      rw [htail_real_eq]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) htail_lintegral_le
    have htail_μ_small :
        ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) < ε / 3 := by
      exact hNμ N (le_max_left _ _)
    have hclamp_tendsto :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hμs (clampContinuous hf_cont N)
    have hclamp_eventually :
        ∀ᶠ n in atTop,
          |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
              ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)| < ε / 3 := by
      have hdiff_tendsto :
          Tendsto
            (fun n ↦
              ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))
            atTop (𝓝 0) := by
        have hconst :
            Tendsto
              (fun _ : ℕ ↦ ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))
              atTop
              (𝓝 (∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))) :=
          tendsto_const_nhds
        have hdiff_tendsto' :
            Tendsto
              (fun n ↦
                ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                  ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))
              atTop
              (𝓝
                ((∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)) -
                  (∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)))) :=
          hclamp_tendsto.sub hconst
        simpa using hdiff_tendsto'
      have hnorm_tendsto :
          Tendsto
            (fun n ↦
              |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                  ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)|)
            atTop (𝓝 0) := by
        simpa [Real.norm_eq_abs] using hdiff_tendsto.norm
      exact hnorm_tendsto.eventually (Iio_mem_nhds (by positivity))
    obtain ⟨Nclamp, hNclamp⟩ := Filter.eventually_atTop.1 hclamp_eventually
    refine ⟨max N Nclamp, fun n hn ↦ ?_⟩
    have htail_seq_n : ∫ x,
        Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μs n : Measure E) ≤ ε / 3 :=
      htail_seq_small n
    have hclamp_n :
        |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
            ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)| < ε / 3 :=
      hNclamp n (le_trans (le_max_right _ _) hn)
    have herror_seq :
        |∫ x, f x ∂(μs n : Measure E) - ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E)| ≤
          ε / 3 := by
      have hsub_int :
          Integrable (fun x ↦ f x - clampContinuous hf_cont N x) (μs n : Measure E) :=
        (hf_integrable_seq n).sub ((clampContinuous hf_cont N).integrable (μs n : Measure E))
      have htail_int :
          Integrable (fun x ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
            (μs n : Measure E) := by
        have hs : MeasurableSet {x | (N : ℝ) < |f x|} :=
          measurableSet_lt measurable_const hf_cont.measurable.norm
        simpa [Set.indicator] using (hf_integrable_seq n).norm.indicator hs
      have hsub_abs_int :
          Integrable (fun x ↦ |f x - clampContinuous hf_cont N x|) (μs n : Measure E) := by
        simpa [Real.norm_eq_abs] using hsub_int.norm
      calc
        |∫ x, f x ∂(μs n : Measure E) - ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E)|
            = |∫ x, (f x - clampContinuous hf_cont N x) ∂(μs n : Measure E)| := by
                rw [integral_sub (hf_integrable_seq n) ((clampContinuous hf_cont N).integrable _)]
        _ ≤ ∫ x, |f x - clampContinuous hf_cont N x| ∂(μs n : Measure E) :=
              abs_integral_le_integral_abs
        _ ≤ ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μs n : Measure E) := by
              refine integral_mono_ae hsub_abs_int htail_int ?_
              filter_upwards with x
              exact abs_sub_clampNat_le_strictTailAbsIndicator N (f x)
        _ ≤ ε / 3 := htail_seq_n
    have herror_μ :
        |∫ x, clampContinuous hf_cont N x ∂(μ : Measure E) - ∫ x, f x ∂(μ : Measure E)| ≤ ε / 3 := by
      have hsub_int :
          Integrable (fun x ↦ clampContinuous hf_cont N x - f x) (μ : Measure E) :=
        ((clampContinuous hf_cont N).integrable (μ : Measure E)).sub hf_integrable
      have htail_int :
          Integrable (fun x ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
            (μ : Measure E) := by
        have hs : MeasurableSet {x | (N : ℝ) < |f x|} :=
          measurableSet_lt measurable_const hf_cont.measurable.norm
        simpa [Set.indicator] using hf_integrable.norm.indicator hs
      have hsub_abs_int :
          Integrable (fun x ↦ |clampContinuous hf_cont N x - f x|) (μ : Measure E) := by
        simpa [Real.norm_eq_abs] using hsub_int.norm
      have hsub_abs_int' :
          Integrable (fun x ↦ |f x - clampContinuous hf_cont N x|) (μ : Measure E) := by
        simpa [abs_sub_comm] using hsub_abs_int
      have htail_μ_le : ∫ x,
          Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) ≤ ε / 3 :=
        le_of_lt htail_μ_small
      calc
        |∫ x, clampContinuous hf_cont N x ∂(μ : Measure E) - ∫ x, f x ∂(μ : Measure E)|
            = |∫ x, (clampContinuous hf_cont N x - f x) ∂(μ : Measure E)| := by
                rw [integral_sub ((clampContinuous hf_cont N).integrable _) hf_integrable]
        _ ≤ ∫ x, |clampContinuous hf_cont N x - f x| ∂(μ : Measure E) :=
              abs_integral_le_integral_abs
        _ = ∫ x, |f x - clampContinuous hf_cont N x| ∂(μ : Measure E) := by
              congr 1
              ext x
              rw [abs_sub_comm]
        _ ≤ ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) := by
              refine integral_mono_ae hsub_abs_int' htail_int ?_
              filter_upwards with x
              simpa [abs_sub_comm] using abs_sub_clampNat_le_strictTailAbsIndicator N (f x)
        _ ≤ ε / 3 := htail_μ_le
    have hmain :
        |∫ x, f x ∂(μs n : Measure E) - ∫ x, f x ∂(μ : Measure E)| < ε := by
      calc
      |∫ x, f x ∂(μs n : Measure E) - ∫ x, f x ∂(μ : Measure E)|
          ≤ |∫ x, f x ∂(μs n : Measure E) -
                ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E)| +
              |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)| +
              |∫ x, clampContinuous hf_cont N x ∂(μ : Measure E) -
                ∫ x, f x ∂(μ : Measure E)| := by
              have h₁ := abs_sub_le
                (∫ x, f x ∂(μs n : Measure E))
                (∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E))
                (∫ x, f x ∂(μ : Measure E))
              have h₂ := abs_sub_le
                (∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E))
                (∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))
                (∫ x, f x ∂(μ : Measure E))
              linarith
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith
      _ = ε := by ring
    simpa [Real.dist_eq] using hmain

end LawLevelMetric

/- Exercise 15.4.5 is `source-facing`: it states the Fréchet--Shohat subsequence and moment
criteria directly for weakly convergent laws on `ℝ`. Its `core/canonical` owner abstractions are
`ProbabilityMeasure ℝ` for weak convergence and `Measure.IsMomentDeterminate (μ : Measure ℝ)` for
the moment-determinate limit law; the moment equalities are derived from those owners rather than
additional primitive data. -/

section SubseqMoments

variable {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {r : ℝ} (φ : ℕ ↪o ℕ)

/-- Helper for Exercise 15.4.5: lower absolute powers are pointwise dominated by
`1 + |x| ^ r` when `0 ≤ s ≤ r`. -/
private lemma absRpow_le_one_add_absRpow {s r x : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    |x| ^ s ≤ 1 + |x| ^ r := by
  rcases le_or_gt |x| 1 with hx | hx
  · calc
      |x| ^ s ≤ 1 := Real.rpow_le_one (abs_nonneg x) hx hs
      _ ≤ 1 + |x| ^ r := by
        exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg x) r)
  · calc
      |x| ^ s ≤ |x| ^ r := Real.rpow_le_rpow_of_exponent_le hx.le hsr
      _ ≤ 1 + |x| ^ r := by
        simpa [add_comm] using
          (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by positivity) : |x| ^ r ≤ |x| ^ r + 1)

/-- Helper for Exercise 15.4.5: integrating the lower-order absolute power is controlled by
`1 +` the higher-order absolute moment. -/
private lemma lintegral_absRpow_le_one_add_absRpow
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (η : ProbabilityMeasure ℝ) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(η : Measure ℝ) ≤
      1 + ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(η : Measure ℝ) := by
  -- Proof comment: dominate pointwise by `1 + |x| ^ r` and then integrate that explicit sum.
  refine le_trans (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal <|
    absRpow_le_one_add_absRpow hs hsr) ?_
  have hsplit :
      (fun x : ℝ ↦ ENNReal.ofReal (1 + |x| ^ r)) =
        fun x ↦ (1 : ℝ≥0∞) + ENNReal.ofReal (|x| ^ r) := by
    funext x
    have hnonneg : 0 ≤ |x| ^ r := Real.rpow_nonneg (abs_nonneg x) r
    calc
      ENNReal.ofReal (1 + |x| ^ r) = ENNReal.ofReal (|x| ^ r + 1) := by ring_nf
      _ = ENNReal.ofReal (|x| ^ r) + 1 := by
            simpa using ENNReal.ofReal_add hnonneg zero_le_one
      _ = 1 + ENNReal.ofReal (|x| ^ r) := by rw [add_comm]
  have hmeas :
      Measurable (fun x : ℝ ↦ ENNReal.ofReal (|x| ^ r)) :=
    (continuous_abs.rpow_const fun _ ↦ Or.inr (hs.trans hsr)).measurable.ennreal_ofReal
  simpa [hsplit] using
    (lintegral_add_right (μ := (η : Measure ℝ)) (fun x ↦ (1 : ℝ≥0∞)) hmeas).le

/-- Helper for Exercise 15.4.5: a finite `r`th absolute moment forces finiteness of every lower
absolute moment. -/
private lemma lintegral_absRpow_lt_top_of_absMoment_lt_top
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) {η : ProbabilityMeasure ℝ}
    (hη : ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(η : Measure ℝ) < ⊤) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(η : Measure ℝ) < ⊤ := by
  exact lt_of_le_of_lt (lintegral_absRpow_le_one_add_absRpow hs hsr η) <|
    ENNReal.add_lt_top.2 ⟨by simp, hη⟩

/-- Helper for Exercise 15.4.5: above a cutoff `A`, the lower power `t ^ s` is absorbed by the
tail factor `A ^ (s - r)` times the higher power `t ^ r`. -/
private lemma absRpow_le_cutoffMul_of_le {A s r t : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hsr : s < r) (ht : A ≤ t) :
    t ^ s ≤ A ^ (s - r) * t ^ r := by
  have ht_pos : 0 < t := lt_of_lt_of_le hA ht
  have hbase : t ^ (s - r) ≤ A ^ (s - r) :=
    Real.rpow_le_rpow_of_nonpos hA ht (sub_nonpos.mpr hsr.le)
  -- Proof comment: compare the negative exponent `s - r` on the larger base `t`, then multiply
  -- back by the nonnegative `r`th power.
  calc
    t ^ s = t ^ (s - r) * t ^ r := by
      symm
      rw [← Real.rpow_add ht_pos, sub_add_cancel]
    _ ≤ A ^ (s - r) * t ^ r := by
      exact mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (le_of_lt ht_pos) r)

/-- Helper for Exercise 15.4.5: a uniform `r`th absolute-moment bound implies law-level uniform
integrability of the lower absolute power `x ↦ |x| ^ s`. -/
private lemma uniformlyIntegrableWithRespectToProbabilitySequence_absRpow_of_bounded_absMoment
    {s r : ℝ} {μs : ℕ → ProbabilityMeasure ℝ} (hs : 0 < s) (hsr : s < r)
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(μs n : Measure ℝ)) < ⊤) :
    uniformlyIntegrableWithRespectToProbabilitySequence (fun x : ℝ ↦ |x| ^ s) μs := by
  let B : ℝ≥0∞ :=
    sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(μs n : Measure ℝ))
  refine (uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon).2 ?_
  intro ε hε
  let A : ℝ := ((B.toReal + 1) / ε) ^ (1 / (r - s))
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  let a : {a : ℝ // 0 < a} := ⟨A ^ s, by positivity⟩
  refine ⟨a, ?_⟩
  have hmeas_r (n : ℕ) :
      AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (|x| ^ r)) (μs n : Measure ℝ) :=
    by
      fun_prop
  have hA_pow :
      A ^ (s - r) = ε / (B.toReal + 1) := by
    dsimp [A]
    have hbase : 0 < (B.toReal + 1) / ε := by positivity
    have hsub_eq_neg : s - r = -(r - s) := by ring
    have hexp : (1 / (r - s)) * (s - r) = (-1 : ℝ) := by
      rw [hsub_eq_neg]
      field_simp [show r - s ≠ 0 by linarith]
    calc
      (((B.toReal + 1) / ε) ^ (1 / (r - s))) ^ (s - r)
          = ((B.toReal + 1) / ε) ^ ((1 / (r - s)) * (s - r)) := by
              rw [Real.rpow_mul hbase.le]
      _ = ((B.toReal + 1) / ε) ^ (-1 : ℝ) := by
            rw [hexp]
      _ = ε / (B.toReal + 1) := by
            rw [Real.rpow_neg hbase.le, Real.rpow_one]
            field_simp [show (B.toReal + 1) ≠ 0 by positivity, hε.ne']
  have hA_tail :
      A ^ (s - r) * (B.toReal + 1) ≤ ε := by
    calc
      A ^ (s - r) * (B.toReal + 1) = (ε / (B.toReal + 1)) * (B.toReal + 1) := by
        rw [hA_pow]
      _ = ε := by
        field_simp [show (B.toReal + 1) ≠ 0 by positivity]
      _ ≤ ε := le_rfl
  intro n
  have hBmem :
      ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(μs n : Measure ℝ) ≤ B := by
    exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ (Set.mem_range_self n)
  have htail_pointwise :
      ∀ x : ℝ,
        ENNReal.ofReal |(|x| ^ s)| ≤
          ENNReal.ofReal (A ^ (s - r)) * ENNReal.ofReal (|x| ^ r)
            ∨ |x| ^ s ≤ A ^ s := by
    intro x
    by_cases hxA : A ≤ |x|
    · left
      have hle : |x| ^ s ≤ A ^ (s - r) * |x| ^ r :=
        absRpow_le_cutoffMul_of_le hA_pos hs hsr hxA
      have hnonneg : 0 ≤ |x| ^ s := Real.rpow_nonneg (abs_nonneg x) s
      rw [abs_of_nonneg hnonneg]
      calc
        ENNReal.ofReal (|x| ^ s) ≤ ENNReal.ofReal (A ^ (s - r) * |x| ^ r) :=
          ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (A ^ (s - r)) * ENNReal.ofReal (|x| ^ r) := by
          rw [ENNReal.ofReal_mul (by positivity)]
    · right
      exact Real.rpow_le_rpow (abs_nonneg x) (le_of_not_ge hxA) hs.le
  have htail_meas :
      MeasurableSet {x : ℝ | a.1 < |(|x| ^ s)|} := by
    exact
      measurableSet_lt measurable_const
        (continuous_abs.rpow_const fun _ ↦ Or.inr hs.le).measurable.norm
  calc
    ∫⁻ x in {x | a.1 < |(|x| ^ s)|}, ENNReal.ofReal |(|x| ^ s)| ∂(μs n : Measure ℝ)
      ≤ ∫⁻ x in {x | a.1 < |(|x| ^ s)|},
          ENNReal.ofReal (A ^ (s - r)) * ENNReal.ofReal (|x| ^ r) ∂(μs n : Measure ℝ) := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' htail_meas]
            refine Filter.Eventually.of_forall ?_
            intro x hx
            rcases htail_pointwise x with hdom | hsmall
            · exact hdom
            ·
              have hnonneg : 0 ≤ |x| ^ s := Real.rpow_nonneg (abs_nonneg x) s
              have hx' : A ^ s < |x| ^ s := by
                simpa [a, abs_of_nonneg hnonneg] using hx
              exact (not_lt_of_ge hsmall hx').elim
    _ ≤ ∫⁻ x,
          ENNReal.ofReal (A ^ (s - r)) * ENNReal.ofReal (|x| ^ r) ∂(μs n : Measure ℝ) := by
            exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (A ^ (s - r)) *
          ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(μs n : Measure ℝ) := by
            rw [lintegral_const_mul'' _ (hmeas_r n)]
    _ ≤ ENNReal.ofReal (A ^ (s - r)) * B := by
          gcongr
    _ ≤ ENNReal.ofReal (A ^ (s - r)) * ENNReal.ofReal (B.toReal + 1) := by
          gcongr
          calc
            B = ENNReal.ofReal B.toReal := by
              symm
              exact ENNReal.ofReal_toReal hbound.ne
            _ ≤ ENNReal.ofReal (B.toReal + 1) := by
              exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (A ^ (s - r) * (B.toReal + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hA_tail

/-- Helper for Exercise 15.4.5: under a genuine even absolute moment, the corresponding even
moment agrees with that absolute moment. -/
private lemma lintegral_abs_even_eq_moment (η : ProbabilityMeasure ℝ) (m : ℕ)
    (hInt : Integrable (fun x : ℝ ↦ |x| ^ (2 * m : ℝ)) (η : Measure ℝ)) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * m : ℝ)) ∂(η : Measure ℝ) =
      ENNReal.ofReal (moment id (2 * m) (η : Measure ℝ)) := by
  have hexp_cast : (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) := by
    exact_mod_cast rfl
  have hpowInt :
      Integrable (fun x : ℝ ↦ x ^ (2 * m)) (η : Measure ℝ) := by
    have hnormInt : Integrable (fun x : ℝ ↦ |x ^ (2 * m)|) (η : Measure ℝ) := by
      -- Proof comment: switch from real exponents to the natural even power before invoking the
      -- ordinary moment API.
      have hpow_eq :
          (fun x : ℝ ↦ |x| ^ (2 * m : ℝ)) = fun x : ℝ ↦ |x ^ (2 * m)| := by
        funext x
        rw [hexp_cast, Real.rpow_natCast]
        exact (abs_pow x (2 * m)).symm
      simpa [hpow_eq] using hInt
    exact
      (integrable_norm_iff
        ((continuous_pow (2 * m)).aestronglyMeasurable)).1 <| by
          simpa [Real.norm_eq_abs] using hnormInt
  have hpowNonneg : 0 ≤ᵐ[(η : Measure ℝ)] fun x : ℝ ↦ x ^ (2 * m) := by
    filter_upwards with x
    simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using sq_nonneg (x ^ m)
  have hMoment :
      ENNReal.ofReal (moment id (2 * m) (η : Measure ℝ)) =
        ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂(η : Measure ℝ) := by
    simpa [ProbabilityTheory.moment_def] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpowInt hpowNonneg)
  -- Proof comment: rewrite the even moment as a nonnegative integral and then identify the
  -- integrands pointwise through `abs_pow`.
  calc
    ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * m : ℝ)) ∂(η : Measure ℝ)
        = ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂(η : Measure ℝ) := by
            refine lintegral_congr_ae ?_
            filter_upwards with x
            have hxnonneg : 0 ≤ x ^ (2 * m) := by
              simpa [pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                sq_nonneg (x ^ m)
            rw [hexp_cast, Real.rpow_natCast]
            simpa [abs_of_nonneg hxnonneg] using
              congrArg ENNReal.ofReal (abs_pow x (2 * m)).symm
    _ = ENNReal.ofReal (moment id (2 * m) (η : Measure ℝ)) := hMoment.symm

-- Proof sketch: combine weak convergence of the subsequence with the uniform `r`th absolute-moment
-- bound to obtain uniform integrability of `x ↦ |x| ^ s` for `0 < s < r`, then apply the
-- portmanteau/Vitali argument to the limit law.
/-- Item (i) of Exercise 15.4.5: if a subsequence of laws converges weakly and the whole
sequence has uniformly bounded `r`th absolute moments, then the weak limit has finite `s`th
absolute moment for every `0 < s < r`. -/
theorem integrable_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    Integrable (fun x : ℝ ↦ |x| ^ s) (μ : Measure ℝ) := by
  -- Proof comment: portmanteau gives the lower-semicontinuity inequality for the continuous
  -- nonnegative test function `x ↦ |x| ^ s`; the higher moment bound then forces the liminf to be
  -- finite.
  let B : ℝ≥0∞ :=
    sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ))
  have hopen :
      ∀ G : Set ℝ, IsOpen G →
        (μ : Measure ℝ) G ≤ atTop.liminf (fun l ↦ (ν (φ l) : Measure ℝ) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_tendsto hG
  have hlin_le :
      ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(μ : Measure ℝ) ≤
        atTop.liminf (fun l ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(ν (φ l) : Measure ℝ)) := by
    exact lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (continuous_abs.rpow_const fun _ ↦ Or.inr hs.le)
      (fun x ↦ Real.rpow_nonneg (abs_nonneg x) _) hopen
  have hpointwise :
      ∀ l : ℕ,
        ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(ν (φ l) : Measure ℝ) ≤ 1 + B := by
    intro l
    calc
      ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(ν (φ l) : Measure ℝ)
        ≤ 1 + ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν (φ l) : Measure ℝ) :=
          lintegral_absRpow_le_one_add_absRpow hs.le hsr.le _
      _ ≤ 1 + B := by
        gcongr
        exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ (Set.mem_range_self (φ l))
  have hliminf_le :
      atTop.liminf (fun l ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(ν (φ l) : Measure ℝ)) ≤ 1 + B := by
    refine liminf_le_of_le
      (u := fun l ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(ν (φ l) : Measure ℝ))
      (a := (1 + B : ℝ≥0∞)) (by isBoundedDefault) ?_
    intro (b : ℝ≥0∞)
      (hb :
        ∀ᶠ l in atTop,
          b ≤ ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(ν (φ l) : Measure ℝ))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hb
    exact (hN N le_rfl).trans (hpointwise N)
  have hlin_ne_top :
      ∫⁻ x, ENNReal.ofReal (|x| ^ s) ∂(μ : Measure ℝ) ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt (hlin_le.trans hliminf_le) <|
      ENNReal.add_lt_top.2 ⟨by simp, hbound⟩
  have hsm : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ s) (μ : Measure ℝ) :=
    (continuous_abs.rpow_const fun _ ↦ Or.inr hs.le).aestronglyMeasurable
  exact (lintegral_ofReal_ne_top_iff_integrable hsm (Eventually.of_forall fun _ ↦
    Real.rpow_nonneg (abs_nonneg _) _)).1 hlin_ne_top

-- Proof sketch: apply the previous uniform-integrability input to the test functions
-- `x ↦ |x| ^ s`; weak convergence of the laws then upgrades to convergence of the corresponding
-- absolute moments along the subsequence.
/-- Item (i) of Exercise 15.4.5: under the same hypotheses, the `s`th absolute moments converge
along the weakly convergent subsequence for every `0 < s < r`. -/
theorem tendsto_integral_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    Tendsto (fun l ↦ ∫ x, |x| ^ s ∂(ν (φ l) : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ s ∂(μ : Measure ℝ))) := by
  let νs : ℕ → ProbabilityMeasure ℝ := fun l ↦ ν (φ l)
  have hbound_sub :
      sSup (Set.range fun l : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(νs l : Measure ℝ)) < ⊤ := by
    refine lt_of_le_of_lt (csSup_le (Set.range_nonempty _) ?_) hbound
    intro b hb
    rcases hb with ⟨l, rfl⟩
    exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ (Set.mem_range_self (φ l))
  have hUI :
      uniformlyIntegrableWithRespectToProbabilitySequence (fun x : ℝ ↦ |x| ^ s) νs :=
    uniformlyIntegrableWithRespectToProbabilitySequence_absRpow_of_bounded_absMoment hs hsr
      hbound_sub
  -- Proof comment: the lower-order power is continuous, and the higher-moment bound gives exactly
  -- the law-level uniform integrability needed by the Chapter 13 convergence theorem.
  simpa [νs] using
    (integrable_and_tendsto_integral_of_continuous_of_uniformlyIntegrableProbabilitySequence
      (μs := νs) (μ := μ) (f := fun x : ℝ ↦ |x| ^ s)
      (continuous_abs.rpow_const fun _ ↦ Or.inr hs.le) hUI h_tendsto).2

-- Proof sketch: first use the bounded `r`th absolute moments to deduce uniform integrability of
-- `x ↦ x ^ k` for each natural `k` with `0 < k < r`, then apply item (i) to identify the limit of
-- the ordinary moments along the weakly convergent subsequence.
/-- Item (i) of Exercise 15.4.5: under the same hypotheses, every ordinary moment of order
`k ∈ ℕ ∩ (0, r)` converges along the weakly convergent subsequence. -/
theorem tendsto_moment_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {k : ℕ} (hk0 : 0 < k) (hkr : (k : ℝ) < r) :
    Tendsto (fun l ↦ moment id k (ν (φ l) : Measure ℝ)) atTop
      (𝓝 (moment id k (μ : Measure ℝ))) := by
  let νs : ℕ → ProbabilityMeasure ℝ := fun l ↦ ν (φ l)
  have hbound_sub :
      sSup (Set.range fun l : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(νs l : Measure ℝ)) < ⊤ := by
    refine lt_of_le_of_lt (csSup_le (Set.range_nonempty _) ?_) hbound
    intro b hb
    rcases hb with ⟨l, rfl⟩
    exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ (Set.mem_range_self (φ l))
  have hUIabs :
      uniformlyIntegrableWithRespectToProbabilitySequence
        (fun x : ℝ ↦ |x| ^ (k : ℝ)) νs :=
    uniformlyIntegrableWithRespectToProbabilitySequence_absRpow_of_bounded_absMoment
      (s := (k : ℝ)) (r := r) (μs := νs) (by exact_mod_cast hk0) hkr hbound_sub
  have hUIpow :
      uniformlyIntegrableWithRespectToProbabilitySequence (fun x : ℝ ↦ x ^ k) νs := by
    -- Proof comment: for natural powers, the law-level tail criterion only sees
    -- `|x ^ k| = |x| ^ k`, so the absolute-power uniform integrability transfers verbatim.
    simpa [uniformlyIntegrableWithRespectToProbabilitySequence, Real.rpow_natCast, abs_pow]
      using hUIabs
  -- Proof comment: once uniform integrability is available for `x ↦ x ^ k`, the ordinary moment
  -- convergence is just the Chapter 13 weak-convergence theorem for continuous test functions.
  simpa [νs, ProbabilityTheory.moment_def] using
    (integrable_and_tendsto_integral_of_continuous_of_uniformlyIntegrableProbabilitySequence
      (μs := νs) (μ := μ) (f := fun x : ℝ ↦ x ^ k) (continuous_pow k) hUIpow h_tendsto).2

end SubseqMoments

/-- Helper for Exercise 15.4.5: the complement of `[-R, R]` is the strict norm tail
`{x : ℝ | R < ‖x‖}`. -/
private lemma compl_Icc_neg_eq_norm_gt {R : ℝ} (hR : 0 ≤ R) :
    (Set.Icc (-R) R : Set ℝ)ᶜ = {x : ℝ | R < ‖x‖} := by
  ext x
  constructor
  · intro hx
    have hxIcc : x ∉ Set.Icc (-R) R := hx
    have hnot : ¬ |x| ≤ R := by
      intro hxabs
      exact hxIcc (abs_le.mp hxabs)
    simpa [Real.norm_eq_abs] using lt_of_not_ge hnot
  · intro hx
    have hxnorm : R < |x| := by
      simpa [Real.norm_eq_abs] using hx
    intro hxIcc
    exact not_lt_of_ge (abs_le.mpr hxIcc) hxnorm

/-- Helper for Exercise 15.4.5: a first absolute-moment bound controls the escape probability
outside a centered interval. -/
private lemma measure_centeredInterval_compl_lt_of_firstMomentBound
    (η : ProbabilityMeasure ℝ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∫⁻ x, ENNReal.ofReal |x| ∂(η : Measure ℝ) ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    (η : Measure ℝ) (Set.Icc (-((C.toReal + 1) / ε)) ((C.toReal + 1) / ε))ᶜ <
      ENNReal.ofReal ε := by
  let R : ℝ := (C.toReal + 1) / ε
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRnonzero : ENNReal.ofReal R ≠ 0 := by
    intro hzero
    have hRle : R ≤ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using hzero
    linarith
  have hmeas :
      AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal |x|) (η : Measure ℝ) := by
    fun_prop
  have hmarkov :
      (η : Measure ℝ) {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} ≤
        (∫⁻ x, ENNReal.ofReal |x| ∂(η : Measure ℝ)) / ENNReal.ofReal R :=
    MeasureTheory.meas_ge_le_lintegral_div hmeas hRnonzero ENNReal.ofReal_ne_top
  have hcompl_le :
      (η : Measure ℝ) (Set.Icc (-R) R)ᶜ ≤
        (η : Measure ℝ) {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} := by
    refine measure_mono ?_
    intro x hx
    have hxnorm : R < ‖x‖ := by
      rw [compl_Icc_neg_eq_norm_gt hRpos.le] at hx
      exact hx
    change ENNReal.ofReal R ≤ ENNReal.ofReal |x|
    have hxle : R ≤ |x| := by
      simpa [Real.norm_eq_abs] using hxnorm.le
    exact ENNReal.ofReal_le_ofReal hxle
  have hbound' :
      ∫⁻ x, ENNReal.ofReal |x| ∂(η : Measure ℝ) ≤ ENNReal.ofReal C.toReal := by
    simpa [ENNReal.ofReal_toReal hC.ne] using hbound
  have hdiv_lt :
      (∫⁻ x, ENNReal.ofReal |x| ∂(η : Measure ℝ)) / ENNReal.ofReal R <
        ENNReal.ofReal ε := by
    have hstep :
        (∫⁻ x, ENNReal.ofReal |x| ∂(η : Measure ℝ)) / ENNReal.ofReal R ≤
          ENNReal.ofReal C.toReal / ENNReal.ofReal R := by
      gcongr
    have hratio_lt : C.toReal / R < ε := by
      dsimp [R]
      have hεne : ε ≠ 0 := by linarith
      rw [div_lt_iff₀ hRpos]
      have hmul : ε * ((C.toReal + 1) / ε) = C.toReal + 1 := by
        field_simp [hεne]
      rw [hmul]
      linarith
    calc
      (∫⁻ x, ENNReal.ofReal |x| ∂(η : Measure ℝ)) / ENNReal.ofReal R
          ≤ ENNReal.ofReal C.toReal / ENNReal.ofReal R := hstep
      _ = ENNReal.ofReal (C.toReal / R) := by
        rw [ENNReal.ofReal_div_of_pos hRpos]
      _ < ENNReal.ofReal ε := by
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hratio_lt
  have hfinal := lt_of_le_of_lt (le_trans hcompl_le hmarkov) hdiv_lt
  simpa [R] using hfinal

/-- Helper for Exercise 15.4.5: a uniform first absolute-moment bound makes a sequence of laws on
`ℝ` tight. -/
private lemma tight_probabilityMeasureSequence_of_bounded_firstMoment
    (ηs : ℕ → ProbabilityMeasure ℝ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ n, ∫⁻ x, ENNReal.ofReal |x| ∂(ηs n : Measure ℝ) ≤ C) :
    IsTightMeasureSet (((↑) : ProbabilityMeasure ℝ → Measure ℝ) '' Set.range ηs) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨{0}, isCompact_singleton, ?_⟩
    intro ν hν
    simpa [hε_top] using (le_top : (ν : Measure ℝ) ({0}ᶜ) ≤ ⊤)
  ·
    refine ⟨Set.Icc (-((C.toReal + 1) / ε.toReal)) ((C.toReal + 1) / ε.toReal), isCompact_Icc, ?_⟩
    intro ν hν
    rcases hν with ⟨ρ, ⟨n, rfl⟩, rfl⟩
    exact le_of_lt <|
      (measure_centeredInterval_compl_lt_of_firstMomentBound (ηs n) hC (hbound n)
        (show 0 < ε.toReal by exact ENNReal.toReal_pos hε.ne' hε_top)).trans_le <|
          by
            have hεle : ENNReal.ofReal ε.toReal ≤ ε := by
              simpa using (ENNReal.ofReal_toReal_le : ENNReal.ofReal ε.toReal ≤ ε)
            exact hεle

-- Proof sketch: convergence of the first absolute moments implies tightness of the laws; apply
-- sequential compactness of tight probability measures on `ℝ` to extract a weakly convergent
-- subsequence, then use item (i) to identify all moments of the limit law with the prescribed
-- limits `m k` and to recover that this limit law has finite absolute moments of every order.
/-- Helper for Exercise 15.4.5: convergence of a real-valued moment sequence yields the eventual
bound `|moment id p (ν n)| ≤ |m p| + 1`. -/
private lemma eventually_absMoment_le_absLimit_add_one
    {ν : ℕ → ProbabilityMeasure ℝ} {m : ℕ → ℝ}
    (hm : ∀ k : ℕ, Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop (𝓝 (m k)))
    (p : ℕ) :
    ∀ᶠ n in atTop, |moment id p (ν n : Measure ℝ)| ≤ |m p| + 1 := by
  -- Proof comment: place the convergent moment sequence inside the closed ball of radius `1`
  -- around its limit, then unfold the resulting distance estimate into an absolute-value bound.
  filter_upwards [(hm p).eventually (Metric.closedBall_mem_nhds (x := m p) zero_lt_one)] with n hn
  have hdist : dist (moment id p (ν n : Measure ℝ)) (m p) ≤ 1 := by
    simpa using hn
  have hdist' : |moment id p (ν n : Measure ℝ) - m p| ≤ 1 := by
    simpa [Real.dist_eq] using hdist
  calc
    |moment id p (ν n : Measure ℝ)|
        = |(moment id p (ν n : Measure ℝ) - m p) + m p| := by ring_nf
    _ ≤ |moment id p (ν n : Measure ℝ) - m p| + |m p| := abs_add_le _ _
    _ ≤ 1 + |m p| := by gcongr
    _ = |m p| + 1 := by ring

/-- Helper for Exercise 15.4.5: once a shifted subsequence lies in the eventual integrability
region, each even absolute moment is bounded by the fixed moment envelope `|m (2 * j)| + 1`. -/
private lemma shiftedTailEvenAbsMomentBound
    {ν : ℕ → ProbabilityMeasure ℝ} {m : ℕ → ℝ} {φ : ℕ ↪o ℕ} {j N : ℕ}
    (hN :
      ∀ b ≥ N,
        Integrable (fun x : ℝ ↦ |x| ^ (2 * j : ℝ)) (ν (φ b) : Measure ℝ) ∧
          |moment id (2 * j) (ν (φ b) : Measure ℝ)| ≤ |m (2 * j)| + 1) :
    ∀ n,
      ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * j : ℝ)) ∂(ν (φ (N + n)) : Measure ℝ) ≤
        ENNReal.ofReal (|m (2 * j)| + 1) := by
  intro n
  have hn := hN (N + n) (Nat.le_add_right N n)
  have hlin_eq :
      ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * j : ℝ)) ∂(ν (φ (N + n)) : Measure ℝ) =
        ENNReal.ofReal (moment id (2 * j) (ν (φ (N + n)) : Measure ℝ)) := by
    simpa using lintegral_abs_even_eq_moment (ν (φ (N + n))) j hn.1
  -- Proof comment: rewrite the even absolute moment as the corresponding ordinary moment and then
  -- apply the eventual absolute-value bound.
  rw [hlin_eq]
  exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) hn.2)

/-- Helper for Exercise 15.4.5: after shifting far enough along an extracted subsequence, every
even absolute moment of order `2 * j` is globally integrable and uniformly bounded. -/
private lemma exists_shiftedTail_evenAbsMomentControl
    {ν : ℕ → ProbabilityMeasure ℝ} {m : ℕ → ℝ}
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ, Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop (𝓝 (m k)))
    (φ : ℕ ↪o ℕ) (j : ℕ) :
    ∃ N : ℕ,
      (∀ n, Integrable (fun x : ℝ ↦ |x| ^ (2 * j : ℝ)) (ν (φ (N + n)) : Measure ℝ)) ∧
      sSup (Set.range fun n : ℕ ↦
        ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * j : ℝ)) ∂(ν (φ (N + n)) : Measure ℝ)) < ⊤ := by
  obtain ⟨Nint, hNint⟩ := Filter.eventually_atTop.1 (hfinite (2 * j))
  obtain ⟨Nmom, hNmom⟩ := Filter.eventually_atTop.1
    (eventually_absMoment_le_absLimit_add_one hm (2 * j))
  let N : ℕ := max Nint Nmom
  have hN :
      ∀ b ≥ N,
        Integrable (fun x : ℝ ↦ |x| ^ (2 * j : ℝ)) (ν (φ b) : Measure ℝ) ∧
          |moment id (2 * j) (ν (φ b) : Measure ℝ)| ≤ |m (2 * j)| + 1 := by
    intro b hb
    have hφ_ge : b ≤ φ b := φ.strictMono.id_le b
    have hNint_le : Nint ≤ φ b := by
      exact le_trans (le_trans (le_max_left _ _) hb) hφ_ge
    have hNmom_le : Nmom ≤ φ b := by
      exact le_trans (le_trans (le_max_right _ _) hb) hφ_ge
    -- Proof comment: once the subsequence index is beyond `N`, the order embedding sits at an
    -- even later index of the original sequence, so both eventual properties apply there.
    refine ⟨?_, hNmom (φ b) hNmom_le⟩
    simpa [Nat.cast_mul] using hNint (φ b) hNint_le
  refine ⟨N, ?_, ?_⟩
  · -- Proof comment: the shifted tail stays inside the eventual integrability region by
    -- construction of the cutoff `N`.
    intro n
    exact (hN (N + n) (Nat.le_add_right N n)).1
  · -- Proof comment: each even absolute moment on the shifted tail equals the corresponding even
    -- ordinary moment and is bounded by the fixed finite radius `|m (2 * j)| + 1`.
    have hsup_le :
        sSup (Set.range fun n : ℕ ↦
          ∫⁻ x, ENNReal.ofReal (|x| ^ (2 * j : ℝ)) ∂(ν (φ (N + n)) : Measure ℝ)) ≤
          ENNReal.ofReal (|m (2 * j)| + 1) := by
      refine sSup_le ?_
      intro b hb
      rcases hb with ⟨n, rfl⟩
      exact shiftedTailEvenAbsMomentBound (ν := ν) (m := m) (φ := φ) (j := j) (N := N) hN n
    exact lt_of_le_of_lt hsup_le (by simp)

/-- Item (ii) of Exercise 15.4.5: if every moment sequence eventually exists and converges to a
finite limit, then there is a probability law on `ℝ` with exactly those moments and a weakly
convergent subsequence of the original laws converging to it; in particular, the limiting law has
finite absolute moments of every order. -/
theorem exists_subseq_tendsto_probabilityMeasure_of_eventually_defined_moments
    {ν : ℕ → ProbabilityMeasure ℝ} (m : ℕ → ℝ)
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ, Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop (𝓝 (m k))) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (μ : Measure ℝ)) ∧
        (∀ k : ℕ, moment id k (μ : Measure ℝ) = m k) ∧
        ∃ φ : ℕ ↪o ℕ, Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ) := by
  let C2 : ℝ := |m 2| + 1
  have hMoment2Bound :
      ∀ᶠ n in atTop, |moment id 2 (ν n : Measure ℝ)| ≤ C2 := by
    -- Proof comment: reuse the generic eventual bounded-neighborhood estimate at the specific
    -- even moment order `2` needed for the tightness step.
    simpa [C2] using eventually_absMoment_le_absLimit_add_one hm 2
  have htailEvent :
      ∀ᶠ n in atTop,
        Integrable (fun x : ℝ ↦ |x| ^ (2 : ℝ)) (ν n : Measure ℝ) ∧
          |moment id 2 (ν n : Measure ℝ)| ≤ C2 := (hfinite 2).and hMoment2Bound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htailEvent
  let νtail : ℕ → ProbabilityMeasure ℝ := fun n ↦ ν (N + n)
  have hfirstBound :
      ∀ n, ∫⁻ x, ENNReal.ofReal |x| ∂(νtail n : Measure ℝ) ≤ 1 + ENNReal.ofReal C2 := by
    intro n
    have htail := hN (N + n) (Nat.le_add_right N n)
    have hlin2le :
        ∫⁻ x, ENNReal.ofReal (|x| ^ (2 : ℝ)) ∂(νtail n : Measure ℝ) ≤ ENNReal.ofReal C2 := by
      have hlin2eq :
          ∫⁻ x, ENNReal.ofReal (|x| ^ (2 : ℝ)) ∂(νtail n : Measure ℝ) =
            ENNReal.ofReal (moment id 2 (νtail n : Measure ℝ)) := by
        simpa using lintegral_abs_even_eq_moment (νtail n) 1 (by simpa using htail.1)
      rw [hlin2eq]
      exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) htail.2)
    calc
      ∫⁻ x, ENNReal.ofReal |x| ∂(νtail n : Measure ℝ)
          ≤ 1 + ∫⁻ x, ENNReal.ofReal (|x| ^ (2 : ℝ)) ∂(νtail n : Measure ℝ) := by
              simpa using lintegral_absRpow_le_one_add_absRpow
                (s := 1) (r := 2) (by positivity) (by norm_num) (νtail n)
      _ ≤ 1 + ENNReal.ofReal C2 := by
            gcongr
  have htight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure ℝ → Measure ℝ) '' Set.range νtail) :=
    tight_probabilityMeasureSequence_of_bounded_firstMoment νtail (C := 1 + ENNReal.ofReal C2)
      (by simp) hfirstBound
  have hcomp : IsCompact (closure (Set.range νtail)) :=
    isCompact_closure_of_isTightMeasureSet (S := Set.range νtail) htight
  obtain ⟨μ, _hμmem, ψ, hψmono, hψtendsto⟩ :=
    hcomp.tendsto_subseq (fun n ↦ subset_closure ⟨n, rfl⟩)
  let φ : ℕ ↪o ℕ :=
    OrderEmbedding.ofStrictMono (fun n : ℕ ↦ N + ψ n)
      (fun a b hab ↦ Nat.add_lt_add_left (hψmono hab) N)
  have hφtendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ) := by
    simpa [φ, νtail, Function.comp] using hψtendsto
  refine ⟨μ, ?_, ?_, φ, hφtendsto⟩
  · intro k
    cases k with
    | zero =>
        -- Proof comment: the zeroth absolute moment is the constant function `1`, integrable
        -- under every probability measure.
        simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) (μ : Measure ℝ))
    | succ k =>
        let j : ℕ := k + 1
        obtain ⟨Nj, _hNjInt, hNjBound⟩ :=
          exists_shiftedTail_evenAbsMomentControl (ν := ν) (m := m) hfinite hm φ j
        let νj : ℕ → ProbabilityMeasure ℝ := fun n ↦ ν (φ (Nj + n))
        have hνjtendsto : Tendsto (fun n ↦ νj n) atTop (𝓝 μ) := by
          -- Proof comment: shifting the extracted subsequence does not change its weak limit.
          simpa [νj, Function.comp, add_comm, add_left_comm, add_assoc] using
            hφtendsto.comp (tendsto_add_atTop_nat Nj)
        have hjPosNat : 0 < j := by
          simpa [j] using Nat.succ_pos k
        have hjPos : 0 < (j : ℝ) := by
          exact_mod_cast hjPosNat
        have hjLt : (j : ℝ) < (2 * j : ℝ) := by
          nlinarith
        let idEmb : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono id (fun _ _ h ↦ h)
        -- Proof comment: item (i) now applies directly to the shifted tail with identity
        -- subsequence, because the even-order control is global over all `n`.
        simpa [j, νj, idEmb] using
          (integrable_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
            (ν := νj) (μ := μ) (r := (2 * j : ℝ)) (φ := idEmb)
            hνjtendsto hNjBound (s := (j : ℝ)) hjPos hjLt)
  · intro k
    cases k with
    | zero =>
        have hmoment_zero_seq :
            Tendsto (fun n ↦ moment id 0 (ν n : Measure ℝ)) atTop (𝓝 (1 : ℝ)) := by
          -- Proof comment: every zeroth moment of a probability law is its total mass, hence `1`.
          refine Tendsto.congr' ?_ tendsto_const_nhds
          exact Eventually.of_forall fun n ↦ by
            simp [ProbabilityTheory.moment_def]
        have hm0 : m 0 = 1 := tendsto_nhds_unique (hm 0) hmoment_zero_seq
        -- Proof comment: the extracted limit law is itself a probability measure, so its zeroth
        -- moment is also `1`, which identifies it with the prescribed limit `m 0`.
        calc
          moment id 0 (μ : Measure ℝ) = 1 := by simp [ProbabilityTheory.moment_def]
          _ = m 0 := hm0.symm
    | succ k =>
        let j : ℕ := k + 1
        obtain ⟨Nj, _hNjInt, hNjBound⟩ :=
          exists_shiftedTail_evenAbsMomentControl (ν := ν) (m := m) hfinite hm φ j
        let νj : ℕ → ProbabilityMeasure ℝ := fun n ↦ ν (φ (Nj + n))
        have hνjtendsto : Tendsto (fun n ↦ νj n) atTop (𝓝 μ) := by
          -- Proof comment: the shifted extracted tail still converges weakly to `μ`.
          simpa [νj, Function.comp, add_comm, add_left_comm, add_assoc] using
            hφtendsto.comp (tendsto_add_atTop_nat Nj)
        have hshiftAtTop : Tendsto (fun n : ℕ ↦ φ (Nj + n)) atTop atTop := by
          simpa [Function.comp, add_comm, add_left_comm, add_assoc] using
            φ.strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat Nj)
        have hjPosNat : 0 < j := by
          simpa [j] using Nat.succ_pos k
        have hjLt : (j : ℝ) < (2 * j : ℝ) := by
          nlinarith [show (0 : ℝ) < j by exact_mod_cast hjPosNat]
        let idEmb : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono id (fun _ _ h ↦ h)
        have hmoment_tail :
            Tendsto (fun n ↦ moment id j (νj n : Measure ℝ)) atTop
              (𝓝 (moment id j (μ : Measure ℝ))) := by
          -- Proof comment: item (i) turns weak convergence plus shifted even-moment control into
          -- convergence of the `j`th ordinary moments along the shifted tail.
          simpa [νj, idEmb] using
            (tendsto_moment_of_subseq_tendsto_of_bounded_rth_absoluteMoment
              (ν := νj) (μ := μ) (r := (2 * j : ℝ)) (φ := idEmb)
              hνjtendsto hNjBound (k := j) hjPosNat hjLt)
        have hmoment_from_hm :
            Tendsto (fun n ↦ moment id j (νj n : Measure ℝ)) atTop (𝓝 (m j)) := by
          -- Proof comment: the same shifted tail is still a tail of the original moment sequence,
          -- so the prescribed limit `m j` persists along it.
          simpa [νj, Function.comp] using (hm j).comp hshiftAtTop
        -- Proof comment: the two limits of the same shifted moment sequence must coincide.
        simpa [j] using tendsto_nhds_unique hmoment_tail hmoment_from_hm

/- The canonical chapter notion of a moment-determinate law is the owner predicate
`Measure.IsMomentDeterminate`; the corresponding owner-level theorem
`Measure.isMomentDeterminate_iff` exposes both the distinguished law's finite moments and its
uniqueness among comparison laws with the same finite moments. -/
recall Measure.isMomentDeterminate_iff

-- Proof sketch: by item (ii), every subsequence admits a further weakly convergent subsequence
-- whose limit law has moments `moment id k μ` and finite absolute moments of every order; the
-- eventual finite-moment hypothesis is needed here because `moment` is the totalized Bochner
-- integral in this project, so this genuine finite-moment content of the subsequential limit must
-- be recovered for the subsequential limits. Moment determinacy of `μ` already packages the
-- finite-moment content of the distinguished limit law together with uniqueness, so every such
-- subsequential limit equals `μ`, and the standard subsequence criterion yields convergence of
-- the whole sequence.
/-- Exercise 15.4.5 (5): Item (iii). This is the Fréchet--Shohat theorem in the source-faithful
form for the chapter's totalized moment convention: if the approximating laws eventually have all
absolute moments finite and the moments of `ν n` converge to those of a moment-determinate law
`μ`, then the laws `ν n` themselves converge weakly to `μ`. -/
theorem tendsto_probabilityMeasure_of_moments_tendsto_of_moment_determinate
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ,
      Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop
        (𝓝 (moment id k (μ : Measure ℝ))))
    (hdet : Measure.IsMomentDeterminate (μ : Measure ℝ)) :
    Tendsto ν atTop (𝓝 μ) := by
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨η, hηInt, hηMom, φ, hφtendsto⟩ :=
    exists_subseq_tendsto_probabilityMeasure_of_eventually_defined_moments
      (ν := fun n ↦ ν (ns n)) (m := fun k ↦ moment id k (μ : Measure ℝ))
      (fun k ↦ hns.eventually (hfinite k)) (fun k ↦ (hm k).comp hns)
  have hηeq_measure : (η : Measure ℝ) = (μ : Measure ℝ) := by
    exact (hdet.eq_of_forall_moment_eq
      (fun k ↦ by simpa [Real.rpow_natCast] using hηInt k) (fun k ↦ (hηMom k).symm)
      ).symm
  have hηeq : η = μ := ProbabilityMeasure.toMeasure_injective hηeq_measure
  refine ⟨φ, ?_⟩
  simpa [hηeq] using hφtendsto
