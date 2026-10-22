/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

-- Proof sketch: first view the identically distributed family `X` as uniformly integrable in
-- `L^p` using `MemLp.uniformIntegrable_of_identDistrib`, after translating the moment assumption
-- `E[|X₀|^p] < ∞` into the corresponding `L^p` membership. Then apply
-- `uniformIntegrable_average_real` to the Cesàro averages and use the standard criterion that a
-- uniformly `L^p`-integrable family yields uniform integrability of the powered absolute values.
/-- Lemma 20.15: if `p ≥ 1` and `X₀, X₁, ...` are identically distributed real random variables
with finite `p`-th absolute moment, then the sequence of powered Cesàro averages
`Yₙ(ω) = |(∑_{k < n} X_k(ω)) / n| ^ p` is uniformly integrable. In Lean's `0`-based indexing, the
`n = 0` term is the harmless convention `0 / 0 = 0`. -/
theorem uniformIntegrable_abs_rpow_cesaroAverage_of_identDistrib
    {p : ℝ} (hp : 1 ≤ p) (X : ℕ → Ω → ℝ)
    (hident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hXp : Integrable (fun ω ↦ |X 0 ω| ^ p) μ) :
    UniformIntegrable
      (fun n ω ↦ |((∑ k ∈ Finset.range n, X k ω) / (n : ℝ))| ^ p) 1 μ := by
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let A : ℕ → Ω → ℝ := fun n ↦ (∑ k ∈ Finset.range n, X k) / (n : Ω → ℝ)
  have hp_nonneg : 0 ≤ p := zero_le_one.trans hp
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hp_not_le_zero : ¬ p ≤ 0 := by
    linarith
  have hq_one : 1 ≤ q := by
    simpa [q] using (ENNReal.ofReal_le_ofReal hp)
  have hq_ne_zero : q ≠ 0 := by
    simpa [q, ENNReal.ofReal_eq_zero] using hp_not_le_zero
  have hq_ne_top : q ≠ ∞ := by
    simp [q]
  have hX0_aestronglyMeasurable : AEStronglyMeasurable (X 0) μ :=
    (hident 0).aestronglyMeasurable_fst
  have hX0_memLp : MemLp (X 0) q μ := by
    refine (integrable_norm_rpow_iff hX0_aestronglyMeasurable hq_ne_zero hq_ne_top).1 ?_
    simpa [q, Real.norm_eq_abs, ENNReal.toReal_ofReal hp_nonneg] using hXp
  have hA_ui : UniformIntegrable A q μ := by
    simpa [A] using uniformIntegrable_average_real hq_one
      (MemLp.uniformIntegrable_of_identDistrib hq_one hq_ne_top hX0_memLp hident)
  have hcont_abs_rpow : Continuous (fun x : ℝ ↦ |x| ^ p) :=
    continuous_abs.rpow_const fun _ ↦ Or.inr hp_nonneg
  suffices hUI : UniformIntegrable (fun n ω ↦ |A n ω| ^ p) 1 μ by
    simpa [A] using hUI
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact hcont_abs_rpow.comp_aestronglyMeasurable (hA_ui.aestronglyMeasurable n)
  · intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hA_ui.unifIntegrable (Real.rpow_pos_of_pos hε _)
    refine ⟨δ, hδ_pos, fun n s hs hμs ↦ ?_⟩
    calc
      eLpNorm (s.indicator (fun ω ↦ |A n ω| ^ p)) 1 μ
          = eLpNorm (fun ω ↦ ‖s.indicator (A n) ω‖ ^ p) 1 μ := by
              refine eLpNorm_congr_ae ?_
              filter_upwards with ω
              by_cases hω : ω ∈ s <;> simp [hω, hp_pos.ne.symm, Real.norm_eq_abs]
      _ = eLpNorm (s.indicator (A n)) q μ ^ p := by
            simpa [q, one_mul] using
              (@eLpNorm_norm_rpow Ω ℝ _ 1 p μ _ (s.indicator (A n)) hp_pos)
      _ ≤ (ENNReal.ofReal (ε ^ p⁻¹)) ^ p :=
            ENNReal.rpow_le_rpow (hδ n s hs hμs) hp_nonneg
      _ = ENNReal.ofReal ε := by
            rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε.le _) hp_nonneg]
            rw [← Real.rpow_mul hε.le, inv_mul_cancel₀ hp_pos.ne.symm, Real.rpow_one]
  · obtain ⟨C, hC⟩ := hA_ui.2.2
    refine ⟨C ^ p, fun n ↦ ?_⟩
    calc
      eLpNorm (fun ω ↦ |A n ω| ^ p) 1 μ = eLpNorm (A n) q μ ^ p := by
        simpa [q, one_mul, Real.norm_eq_abs] using
          (@eLpNorm_norm_rpow Ω ℝ _ 1 p μ _ (A n) hp_pos)
      _ ≤ (C : ℝ≥0∞) ^ p := ENNReal.rpow_le_rpow (hC n) hp_nonneg
      _ = ((C ^ p : NNReal) : ℝ≥0∞) := by
        symm
        exact ENNReal.coe_rpow_of_nonneg C hp_nonneg
