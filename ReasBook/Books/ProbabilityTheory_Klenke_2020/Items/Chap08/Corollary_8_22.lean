/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- Proof sketch: apply the de la Vallée-Poussin characterization of uniform integrability to the
-- original family `X`, then use conditional Jensen for the convex majorant of `|X i|` to obtain a
-- uniform bound for all conditional expectations `μ[X i | ℱ j]`.
/-- Corollary 8.22: if a real-valued family `X` is uniformly integrable, then the family of all
conditional expectations `μ[X i | ℱ j]`, indexed by `I × J`, is uniformly integrable. -/
theorem uniformIntegrable_condExp_of_uniformIntegrable
    {I : Type v} {J : Type w} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : I → Ω → ℝ} (hX : UniformIntegrable X 1 μ)
    {ℱ : J → MeasurableSpace Ω} (hℱ : ∀ j, ℱ j ≤ mΩ) :
    UniformIntegrable (fun ij : I × J ↦ μ[X ij.1 | ℱ ij.2]) 1 μ := by
  let Y : I × J → Ω → ℝ := fun ij ↦ μ[X ij.1 | ℱ ij.2]
  change UniformIntegrable Y 1 μ
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun ij ↦ (stronglyMeasurable_condExp.mono (hℱ ij.2)).aestronglyMeasurable) ?_
  intro ε hε
  -- Control the large-value tails uniformly by transferring the original tail estimate
  -- for `X` to the conditional expectations `Y (i, j) = μ[X i | ℱ j]`.
  obtain ⟨δ, hδ, hXδ⟩ := hX.unifIntegrable hε
  obtain ⟨M, hM⟩ := hX.2.2
  let δnn : ℝ≥0 := ⟨δ, hδ.le⟩
  let C : ℝ≥0 := δnn⁻¹ * max M 1
  refine ⟨C, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  let s : Set Ω := {x | C ≤ ‖Y (i, j) x‖₊}
  have hℱj : ℱ j ≤ mΩ := hℱ j
  have hsℱ : MeasurableSet[ℱ j] s := by
    have hCmeas : StronglyMeasurable[ℱ j] fun _ : Ω ↦ C := stronglyMeasurable_const
    simpa [Y, s] using
      hCmeas.measurableSet_le stronglyMeasurable_condExp.nnnorm
  have hs : MeasurableSet[mΩ] s := hℱj s hsℱ
  have hsμ : μ s ≤ ENNReal.ofReal δ := by
    have hδnn : 0 < δnn := by
      simpa [δnn] using hδ
    have hCpos : 0 < C := by
      exact mul_pos (inv_pos.2 hδnn) (lt_of_lt_of_le zero_lt_one (le_max_right M 1))
    have hcondMeas : AEStronglyMeasurable[mΩ] (Y (i, j)) μ :=
      (stronglyMeasurable_condExp.mono hℱj).aestronglyMeasurable
    have hsμ' : μ s ≤ (C : ℝ≥0∞)⁻¹ * eLpNorm (Y (i, j)) 1 μ := by
      simpa [Y, s, ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm] using
        meas_ge_le_mul_pow_eLpNorm_enorm μ one_ne_zero ENNReal.one_ne_top hcondMeas
          (ENNReal.coe_ne_zero.2 hCpos.ne') (by simp)
    refine hsμ'.trans ?_
    calc
      (C : ℝ≥0∞)⁻¹ * eLpNorm (Y (i, j)) 1 μ ≤ (C : ℝ≥0∞)⁻¹ * M := by
        gcongr
        simpa [Y] using
          le_trans (show eLpNorm (μ[X i | ℱ j]) 1 μ ≤ eLpNorm (X i) 1 μ from
            eLpNorm_one_condExp_le_eLpNorm (X i)) (hM i)
      _ ≤ ENNReal.ofReal δ := by
        have hnn : C⁻¹ * M ≤ δnn := by
          rw [inv_mul_le_iff₀ hCpos]
          convert le_max_left M (1 : ℝ≥0) using 1
          simp [C, δnn, mul_comm, hδnn.ne']
        have hδcoe : ENNReal.ofReal δ = (δnn : ℝ≥0∞) := by
          simpa [δnn] using ENNReal.ofReal_eq_coe_nnreal hδ.le
        rw [hδcoe, ← ENNReal.coe_inv hCpos.ne', ← ENNReal.coe_mul]
        exact_mod_cast hnn
  have hXi : Integrable (X i) μ := memLp_one_iff_integrable.1 (hX.memLp i)
  have hcond :
      eLpNorm (s.indicator (Y (i, j))) 1 μ ≤ eLpNorm (s.indicator (X i)) 1 μ := by
    -- On the same threshold set, the conditional expectation has no larger `L¹` mass than
    -- the original integrable function, by the absolute-value conditional expectation estimate.
    have hcondInt : Integrable (s.indicator (Y (i, j))) μ := by
      simpa [Y] using
        (show Integrable (μ[X i | ℱ j]) μ from integrable_condExp).indicator hs
    have hsInt : Integrable (s.indicator (X i)) μ := hXi.indicator hs
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hcondInt,
      ← ofReal_integral_norm_eq_lintegral_enorm hsInt]
    simp_rw [norm_indicator_eq_indicator_norm, Real.norm_eq_abs, integral_indicator hs]
    simpa [Y] using ENNReal.ofReal_le_ofReal (setIntegral_abs_condExp_le hsℱ (X i))
  exact hcond.trans (hXδ i s hs hsμ)

/- The single-function special case of this corollary is already the canonical theorem
`MeasureTheory.Integrable.uniformIntegrable_condExp`. -/
recall MeasureTheory.Integrable.uniformIntegrable_condExp
