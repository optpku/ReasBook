/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Filter MeasureTheory
open scoped Topology

section

variable {Ω : Type u} {Ω' : Type v} {E : Type w}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: use the canonical distance formulation of convergence in probability to show that
-- `Xₙ` and `Yₙ` are asymptotically indistinguishable against bounded Lipschitz test functions, then
-- combine this with the characterization of convergence in distribution by such test functions.
/-- Theorem 13.18: Slutzky's theorem states that if `Xₙ` converges in distribution to `X` and the
distance `dist (Xₙ, Yₙ)` tends to `0` in probability, then `Yₙ` converges in distribution to the
same limit `X`. -/
theorem tendstoInDistribution_of_tendstoInMeasure_dist
    {X Y : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ ↦ μ) μ')
    (hXY : TendstoInMeasure μ (fun n ω ↦ dist (X n ω) (Y n ω)) atTop (fun _ ↦ (0 : ℝ)))
    (hY : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution Y atTop Z (fun _ ↦ μ) μ' := by
  have hZ : AEMeasurable Z μ' := hX.aemeasurable_limit
  have hX_meas : ∀ n, AEMeasurable (X n) μ := hX.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  suffices
      ∀ (F : E → ℝ) (_ : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
        (_ : ∃ L, LipschitzWith L F),
        Tendsto (fun n ↦ ∫ ω, F ω ∂(μ.map (Y n))) atTop (𝓝 (∫ ω, F ω ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL : L = 0 ∨ 0 < L := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (Y n)) := Measure.isProbabilityMeasure_map (hY n)
    have : IsProbabilityMeasure (μ'.map Z) := Measure.isProbabilityMeasure_map hZ
    simp
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices
      ∀ ε > 0,
        ∀ᶠ n in atTop, |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n : |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ'.map Z)|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ.map (Y n))) (∫ ω, F ω ∂(μ.map (X n)))
      (∫ ω, F ω ∂(μ'.map Z))).trans ?_
    gcongr
    have hFY_meas : AEMeasurable (fun x ↦ F (Y n x)) μ :=
      hF_cont.measurable.comp_aemeasurable (hY n)
    have hFX_meas : AEMeasurable (fun x ↦ F (X n x)) μ :=
      hF_cont.measurable.comp_aemeasurable (hX_meas n)
    have hdist : AEMeasurable (fun x ↦ dist (Y n x) (X n x)) μ := (hY n).dist (hX_meas n)
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) μ := by
      refine Integrable.of_bound hFY_meas.aestronglyMeasurable (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) μ := by
      refine Integrable.of_bound hFX_meas.aestronglyMeasurable (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) μ := by
      rw [integrable_norm_iff (hFY_meas.sub hFX_meas).aestronglyMeasurable]
      exact h_int_Y.sub h_int_X
    rw [integral_map (hY n) hF_cont.aestronglyMeasurable,
      integral_map (hX_meas n) hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc
      ‖∫ a, F (Y n a) - F (X n a) ∂μ‖ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ
          + ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, ‖F (Y n a) - F (X n a)‖ ∂μ := by
            symm
            simp_rw [← not_lt]
            refine integral_add_compl₀ ?_ h_int_sub
            exact nullMeasurableSet_lt hdist (by fun_prop)
      _ ≤ ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, L * (ε / 2) ∂μ
          + ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, M ∂μ := by
            gcongr ?_ + ?_
            · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
              · exact nullMeasurableSet_lt hdist (by fun_prop)
              · intro x hx
                simpa [Real.dist_eq] using hF_lip.dist_le_mul_of_le hx.le
            · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
              simpa [Real.dist_eq] using hF_bounded (Y n a) (X n a)
      _ = L * (ε / 2) * μ.real {x | dist (Y n x) (X n x) < ε / 2}
          + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
            simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
              Set.univ_inter, smul_eq_mul]
            ring
      _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
            rw [mul_assoc]
            gcongr
            grw [measureReal_le_one, mul_one]
  have hXY' : Tendsto (fun n ↦ μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}) atTop (𝓝 0) := by
    have hXY_dist := (tendstoInMeasure_iff_measureReal_dist.1 hXY) (ε / 2) (by positivity)
    simpa [Real.dist_eq, abs_of_nonneg, dist_nonneg, dist_comm] using hXY_dist
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|) atTop (𝓝 (L * ε / 2)) := by
    suffices
        Tendsto
          (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
            + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ'.map Z)|)
          atTop (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ hXY')).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · replace hX := hX.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hX
      simpa [tendsto_iff_dist_tendsto_zero] using hX F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn
  exact (h_le n).trans_lt hn

end
