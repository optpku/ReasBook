/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped CompactlySupported Topology

universe u

noncomputable section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [LocallyCompactSpace E] [PolishSpace E]

/-- Helper for Lemma 13.15: every compact set already satisfies the liminf bound coming from vague
convergence. -/
lemma measureCompact_le_liminfTotalMass_ofVaguelyConverges
    {μ : Measure E} {μs : ℕ → Measure E}
    (h : radonMeasureVaguelyConvergesTo μs μ) {K : Set E} (hK : IsCompact K) :
    μ K ≤ liminf (fun n ↦ μs n Set.univ) atTop := by
  rcases h with ⟨hμ, -, htest⟩
  letI : SigmaCompactSpace E := inferInstance
  letI : IsLocallyFiniteMeasure μ := hμ.locallyFinite
  letI : Measure.Regular μ := inferInstance
  obtain ⟨f, hf_one, -, hf_compactSupport, hf_range⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty _)
  let g : C_c(E, ℝ) := ⟨f, hf_compactSupport⟩
  have hμK_le_integral : μ K ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
    -- Compare `μ K` with the integral of one admissible compactly supported cutoff.
    calc
      μ K =
          ⨅ (φ : E → ℝ) (_ : Continuous φ) (_ : HasCompactSupport φ) (_ : Set.EqOn φ 1 K)
            (_ : 0 ≤ φ), ENNReal.ofReal (∫ x, φ x ∂μ) := by
        simpa using hK.measure_eq_biInf_integral_hasCompactSupport (μ := μ)
      _ ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
        refine iInf_le_of_le g ?_
        refine iInf_le_of_le g.continuous ?_
        refine iInf_le_of_le g.hasCompactSupport ?_
        refine iInf_le_of_le hf_one ?_
        refine iInf_le_of_le (fun x ↦ (hf_range x).1) ?_
        rfl
  have hIntegral_le_measure (n : ℕ) :
      ENNReal.ofReal (∫ x, g x ∂μs n) ≤ μs n Set.univ := by
    -- The cutoff takes values in `[0, 1]`, so its integral is bounded by the total mass.
    refine integral_le_measure (μ := μs n) (s := Set.univ) (fun x _ ↦ (hf_range x).2) ?_
    intro x hx
    simp at hx
  have hg_tendsto :
      Tendsto (fun n ↦ ENNReal.ofReal (∫ x, g x ∂μs n)) atTop
        (𝓝 (ENNReal.ofReal (∫ x, g x ∂μ))) :=
    ENNReal.tendsto_ofReal (htest g)
  -- Identify the limit cutoff integral with the liminf and compare pointwise with total masses.
  calc
    μ K ≤ ENNReal.ofReal (∫ x, g x ∂μ) := hμK_le_integral
    _ = liminf (fun n ↦ ENNReal.ofReal (∫ x, g x ∂μs n)) atTop := by
      symm
      exact hg_tendsto.liminf_eq
    _ ≤ liminf (fun n ↦ μs n Set.univ) atTop := by
      exact Filter.liminf_le_liminf (Eventually.of_forall hIntegral_le_measure)

-- Proof sketch: first prove the liminf lower bound on each compact subset using one compactly
-- supported cutoff function, then recover the whole mass by inner regularity on `Set.univ`.
/-- Lemma 13.15: if Radon measures on a locally compact Polish space converge vaguely,
then their total masses are lower semicontinuous. -/
theorem measure_univ_le_liminf_of_vaguely_converges
    {μ : Measure E} {μs : ℕ → Measure E}
    (h : radonMeasureVaguelyConvergesTo μs μ) :
    μ Set.univ ≤ liminf (fun n ↦ μs n Set.univ) atTop := by
  have hμ := h.1
  letI : Measure.InnerRegular μ := hμ.innerRegular
  -- Replace the total mass by the supremum over compact subsets and use the compact estimate.
  calc
    μ Set.univ = ⨆ (K : Set E) (_ : K ⊆ Set.univ) (_ : IsCompact K), μ K := by
      simpa using (MeasurableSet.univ.measure_eq_iSup_isCompact (μ := μ))
    _ ≤ liminf (fun n ↦ μs n Set.univ) atTop := by
      refine iSup_le ?_
      intro K
      refine iSup_le ?_
      intro _
      refine iSup_le ?_
      intro hK
      simpa using measureCompact_le_liminfTotalMass_ofVaguelyConverges h hK

end
