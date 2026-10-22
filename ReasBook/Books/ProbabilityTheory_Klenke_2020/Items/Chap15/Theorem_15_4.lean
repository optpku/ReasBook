/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_32

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']

noncomputable section

-- Proof sketch: a bounded range sits inside a compact interval `[a, b]`, hence `|X|` is bounded by
-- `max |a| |b|`. Therefore every exponential moment `E[exp (t |X|)]` with `t ≥ 0` is bounded by
-- the constant `exp (t * max |a| |b|)`, so `exp (t |X|)` is integrable under the probability
-- measure `μ`.
private theorem integrable_exp_mul_abs_of_isBounded_range
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX_bdd : Bornology.IsBounded (Set.range X)) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω ↦ Real.exp (t * |X ω|)) μ := by
  let a : ℝ := sInf (Set.range X)
  let b : ℝ := sSup (Set.range X)
  have hX_mem : ∀ ω, X ω ∈ Set.Icc a b := fun ω ↦
    hX_bdd.subset_Icc_sInf_sSup ⟨ω, rfl⟩
  refine Integrable.of_bound
    (((measurable_abs.comp hX).const_mul t).exp.aestronglyMeasurable)
    (Real.exp (t * max |a| |b|)) <|
    Filter.Eventually.of_forall fun ω ↦ ?_
  have h_abs : |X ω| ≤ max |a| |b| := abs_le_max_abs_abs (hX_mem ω).1 (hX_mem ω).2
  have h_mul : t * |X ω| ≤ t * max |a| |b| := mul_le_mul_of_nonneg_left h_abs ht
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using Real.exp_le_exp.mpr h_mul

/-- Theorem 15.4: a bounded real random variable is determined by its moments among measurable real
random variables. -/
theorem isMomentDeterminate_of_isBounded_range
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX_bdd : Bornology.IsBounded (Set.range X)) :
    IsMomentDeterminate μ X :=
  (method_of_moments_of_integrable_exp_abs_map μ X hX zero_lt_one
    (integrable_exp_mul_abs_of_isBounded_range μ hX hX_bdd zero_le_one)).2

/-- In particular, a bounded real random variable is identically distributed with any measurable
real random variable that has the same moments. -/
theorem identDistrib_of_forall_moment_eq_of_isBounded_range
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_bdd : Bornology.IsBounded (Set.range X))
    (hY_moments : ∀ n : ℕ, Integrable (fun ω ↦ |Y ω| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment X n μ = moment Y n ν) :
    IdentDistrib X Y μ ν := by
  let hX_det : IsMomentDeterminate μ X := isMomentDeterminate_of_isBounded_range μ hX hX_bdd
  exact
    { aemeasurable_fst := hX.aemeasurable
      aemeasurable_snd := hY.aemeasurable
      map_eq := hX_det.map_eq ν Y hY hY_moments h_moments }
