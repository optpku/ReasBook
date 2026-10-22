/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal NNReal

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

-- Bridge/view: the arbitrary-indexed family form used to prove the source-facing `Lp`-set
-- corollary below.
private theorem uniformIntegrable_of_bounded_memLp_family_of_one_lt (μ : Measure Ω)
    [IsFiniteMeasure μ]
    {ι : Type v} {p : ℝ} (hp : 1 < p) {f : ι → Ω → ℝ}
    (hf_memLp : ∀ i, MemLp (f i) (ENNReal.ofReal p) μ)
    (hf_bdd : ∃ C : NNReal, ∀ i, eLpNorm (f i) (ENNReal.ofReal p) μ ≤ C) :
    UniformIntegrable f 1 μ := by
  rcases hf_bdd with ⟨C, hC⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have h1_le_q : (1 : ℝ≥0∞) ≤ q := by
    simpa [q, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  let B : NNReal := max C 1
  have hB : ∀ i, eLpNorm (f i) q μ ≤ (B : ℝ≥0∞) := by
    intro i
    exact le_trans (hC i) (by exact_mod_cast le_max_left C (1 : NNReal))
  have hBpos : 0 < (B : ℝ) := by
    exact NNReal.coe_pos.2 (lt_of_lt_of_le zero_lt_one (le_max_right C 1))
  let r : ℝ := 1 - 1 / p
  have hr_pos : 0 < r := by
    dsimp [r]
    have hp_inv_lt : 1 / p < 1 / 1 := one_div_lt_one_div_of_lt zero_lt_one hp
    linarith
  have hbound1 : ∀ i, eLpNorm (f i) 1 μ ≤ (B : ℝ≥0∞) * μ Set.univ ^ r := by
    intro i
    -- Proof comment: compare the `L¹` and `L^p` seminorms on the whole finite measure space.
    calc
      eLpNorm (f i) 1 μ ≤ eLpNorm (f i) q μ * μ Set.univ ^ r := by
        simpa [q, r, hp0.ne', ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le, one_div] using
          (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_q
            ((hf_memLp i).aestronglyMeasurable))
      _ ≤ (B : ℝ≥0∞) * μ Set.univ ^ r := by
        gcongr
        exact hB i
  refine ⟨fun i ↦ (hf_memLp i).aestronglyMeasurable, ?_, ?_⟩
  · intro ε hε
    let δ : ℝ := (ε / B) ^ (1 / r)
    have hδpos : 0 < δ := by
      -- Proof comment: `δ` is positive because both `ε` and the uniform bound `B` are positive.
      dsimp [δ]
      exact Real.rpow_pos_of_pos (div_pos hε hBpos) _
    refine ⟨δ, hδpos, ?_⟩
    intro i s hs hμs
    have hmeas_restrict : AEStronglyMeasurable (f i) (μ.restrict s) :=
      ((hf_memLp i).aestronglyMeasurable).mono_measure Measure.restrict_le_self
    have hcomp :
        eLpNorm (s.indicator (f i)) 1 μ ≤
          eLpNorm (f i) q (μ.restrict s) * μ s ^ r := by
      -- Proof comment: move to the restricted measure on `s` and compare exponents there.
      simpa [q, eLpNorm_indicator_eq_eLpNorm_restrict hs, r, hp0.ne', ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le, one_div, Measure.restrict_apply' hs, Set.univ_inter] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_q hmeas_restrict)
    have hrestrict : eLpNorm (f i) q (μ.restrict s) ≤ (B : ℝ≥0∞) := by
      exact le_trans
        (eLpNorm_mono_measure (f i) Measure.restrict_le_self)
        (hB i)
    have hδr_real : δ ^ r = ε / B := by
      simpa [δ] using Real.rpow_inv_rpow (div_nonneg hε.le hBpos.le) hr_pos.ne'
    have hδr : ENNReal.ofReal δ ^ r = ENNReal.ofReal (ε / B) := by
      simpa [ENNReal.ofReal_rpow_of_nonneg hδpos.le hr_pos.le] using
        congrArg ENNReal.ofReal hδr_real
    have hμsr : μ s ^ r ≤ ENNReal.ofReal ε / (B : ℝ≥0∞) := by
      -- Proof comment: the choice of `δ` makes the measure factor `μ s ^ r` small enough.
      calc
        μ s ^ r ≤ ENNReal.ofReal δ ^ r := ENNReal.rpow_le_rpow hμs hr_pos.le
        _ = ENNReal.ofReal (ε / B) := hδr
        _ = ENNReal.ofReal ε / (B : ℝ≥0∞) := by
          simpa using (ENNReal.ofReal_div_of_pos hBpos)
    calc
      eLpNorm (s.indicator (f i)) 1 μ
          ≤ eLpNorm (f i) q (μ.restrict s) * μ s ^ r := hcomp
      _ ≤ (B : ℝ≥0∞) * μ s ^ r := by
        gcongr
      _ ≤ (B : ℝ≥0∞) * (ENNReal.ofReal ε / (B : ℝ≥0∞)) := by
        gcongr
      _ = ENNReal.ofReal ε := by
        rw [mul_comm, ENNReal.div_mul_cancel (by exact_mod_cast hBpos.ne') ENNReal.coe_ne_top]
  · refine ⟨(((B : ℝ≥0∞) * μ Set.univ ^ r).toNNReal), ?_⟩
    intro i
    -- Proof comment: the same exponent comparison gives a uniform `L¹` bound on the whole
    -- family, which is the boundedness component of `UniformIntegrable`.
    rw [ENNReal.coe_toNNReal]
    · exact hbound1 i
    · exact (ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)).ne

private lemma one_le_ofReal_of_one_lt {p : ℝ} (hp : 1 < p) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
  simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le

/-- Corollary 6.21: on a finite measure space, a bounded family in the canonical `Lp` owner space
`MeasureTheory.Lp ℝ (ENNReal.ofReal p) μ` is uniformly integrable for every exponent `p > 1`. The
boundedness hypothesis is the chapter's Definition 6.20 notion `Bornology.IsBounded`. -/
theorem uniformIntegrable_of_bounded_memLp_of_one_lt (μ : Measure Ω) [IsFiniteMeasure μ]
    {p : ℝ} (hp : 1 < p) {F : Set (Lp ℝ (ENNReal.ofReal p) μ)}
    (hF_bdd : by
      letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨one_le_ofReal_of_one_lt hp⟩
      exact Bornology.IsBounded F) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ := by
  letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨one_le_ofReal_of_one_lt hp⟩
  obtain ⟨C, hCpos, hC⟩ := hF_bdd.exists_pos_norm_le
  let B : NNReal := ⟨C, le_of_lt hCpos⟩
  refine uniformIntegrable_of_bounded_memLp_family_of_one_lt μ hp
    (fun f ↦ Lp.memLp (f : Lp ℝ (ENNReal.ofReal p) μ)) ?_
  refine ⟨B, fun f ↦ ?_⟩
  have hnorm : ‖(f : Lp ℝ (ENNReal.ofReal p) μ)‖ ≤ C := hC f f.2
  have hnnorm : ‖(f : Lp ℝ (ENNReal.ofReal p) μ)‖₊ ≤ B := by
    exact_mod_cast hnorm
  have henorm : ‖(f : Lp ℝ (ENNReal.ofReal p) μ)‖ₑ ≤ B := by
    simpa [enorm_eq_nnnorm] using hnnorm
  simpa [Lp.enorm_def] using henorm
