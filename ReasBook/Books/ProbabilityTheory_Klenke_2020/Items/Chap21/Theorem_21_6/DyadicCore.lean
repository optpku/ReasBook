/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6.DyadicGeometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Theorem 21.6: almost-sure convergence of a dyadic extension identifies it with the
original process once the same approximants also converge in measure to the original path value. -/
lemma aeEq_original_of_dyadicExtension
    {X Y : NNReal → Ω → ℝ} {t : NNReal} {d : ℕ → NNReal}
    (hd_meas : ∀ n, AEStronglyMeasurable (fun ω ↦ X (d n) ω) μ)
    (hd_ae :
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ X (d n) ω) Filter.atTop (nhds (Y t ω)))
    (hd_measure :
      TendstoInMeasure μ (fun n ω ↦ X (d n) ω) Filter.atTop (fun ω ↦ X t ω)) :
    X t =ᵐ[μ] Y t := by
  -- Proof comment: the same dyadic approximation sequence converges in measure to both `X t` and
  -- `Y t`, so uniqueness of the limit in measure forces almost-sure equality.
  have hY_measure :
      TendstoInMeasure μ (fun n ω ↦ X (d n) ω) Filter.atTop (fun ω ↦ Y t ω) :=
    tendstoInMeasure_of_tendsto_ae hd_meas hd_ae
  simpa using tendstoInMeasure_ae_unique hd_measure hY_measure

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.6: for each fixed `t ≤ T`, the clipped dyadic approximants converge in
measure to the original process value `X t`. -/
lemma tendstoInMeasure_clippedDyadicApprox_of_isKolmogorovProcessOnIcc
    {X : NNReal → Ω → ℝ} {T α β C : ℝ≥0} {t : NNReal}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (htT : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ X (clippedDyadicApprox T t n) ω) Filter.atTop (fun ω ↦ X t ω) := by
  rw [MeasureTheory.tendstoInMeasure_iff_dist]
  intro ε hε
  have hαpos : 0 < (α : ℝ) := by
    exact_mod_cast h.alpha_pos
  have hβqpos : 0 < (1 + (β : ℝ)) := by
    have hβpos : 0 < (β : ℝ) := by
      exact_mod_cast h.beta_pos
    linarith
  let δ : ℝ≥0∞ := (ENNReal.ofReal ε) ^ (α : ℝ)
  have hδpos : 0 < δ := by
    -- Proof comment: the Markov threshold is a positive finite power of `ε`.
    have hεenn_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    exact ENNReal.rpow_pos hεenn_pos ENNReal.ofReal_ne_top
  have hδne0 : δ ≠ 0 := hδpos.ne'
  have hδnetop : δ ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg hαpos.le ENNReal.ofReal_ne_top
  have hpointwise :
      ∀ n : ℕ,
        μ {ω | ε ≤ dist (X (clippedDyadicApprox T t n) ω) (X t ω)}
          ≤ ((C : ℝ≥0∞) * edist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ))) / δ := by
    intro n
    let s := clippedDyadicApprox T t n
    have hs_mem : s ∈ Set.Icc (0 : NNReal) T := clippedDyadicApprox_mem_Icc T t n
    have ht_mem : t ∈ Set.Icc (0 : NNReal) T := by
      simpa using htT
    have hmeas :
        AEMeasurable (fun ω ↦ edist (X s ω) (X t ω) ^ (α : ℝ)) μ := by
      -- Proof comment: the owner Kolmogorov measurability API gives measurability of the fixed
      -- increment distance, and powers preserve that measurability.
      exact
        ((h.isKolmogorovProcess.measurable_edist
          (s := ⟨s, hs_mem⟩) (t := ⟨t, ht_mem⟩)).aemeasurable).pow_const (α : ℝ)
    have hsubset :
        {ω | ε ≤ dist (X s ω) (X t ω)} ⊆ {ω | δ ≤ edist (X s ω) (X t ω) ^ (α : ℝ)} := by
      intro ω hω
      -- Proof comment: raising the distance threshold to the positive exponent `α` gives the
      -- superlevel set used by Markov's inequality.
      have hωenn : ENNReal.ofReal ε ≤ edist (X s ω) (X t ω) := by
        simpa [edist_dist] using ENNReal.ofReal_le_ofReal hω
      have hωpow :
          (ENNReal.ofReal ε) ^ (α : ℝ) ≤ edist (X s ω) (X t ω) ^ (α : ℝ) :=
        ENNReal.rpow_le_rpow hωenn hαpos.le
      simpa [δ] using hωpow
    have hmarkov :
        μ {ω | δ ≤ edist (X s ω) (X t ω) ^ (α : ℝ)}
          ≤ (∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ) / δ :=
      MeasureTheory.meas_ge_le_lintegral_div hmeas hδne0 hδnetop
    have hlintegral :
        ∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ
          ≤ (C : ℝ≥0∞) * edist s t ^ (1 + (β : ℝ)) :=
      by
        -- Proof comment: the finite-horizon increment bound is symmetric in the two times after
        -- rewriting the distance by `edist_comm`.
        simpa [edist_comm] using h.increment_lintegral_le (s := s) (t := t) hs_mem.2 htT
    calc
      μ {ω | ε ≤ dist (X s ω) (X t ω)} ≤ μ {ω | δ ≤ edist (X s ω) (X t ω) ^ (α : ℝ)} :=
        measure_mono hsubset
      _ ≤ (∫⁻ ω, edist (X s ω) (X t ω) ^ (α : ℝ) ∂μ) / δ := hmarkov
      _ ≤ ((C : ℝ≥0∞) * edist s t ^ (1 + (β : ℝ))) / δ := by
        simpa using ENNReal.div_le_div_right hlintegral δ
  have hdist :
      Filter.Tendsto (fun n ↦ edist (clippedDyadicApprox T t n) t) Filter.atTop (nhds 0) := by
    -- Proof comment: the clipped approximants converge back to `t`, so their pairwise distance
    -- from `t` tends to zero.
    have htconst : Filter.Tendsto (fun _ : ℕ ↦ t) Filter.atTop (nhds t) := tendsto_const_nhds
    simpa using (tendsto_clippedDyadicApprox htT).edist htconst
  have hupper :
      Filter.Tendsto
        (fun n ↦ ((C : ℝ≥0∞) / δ) * edist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ)))
        Filter.atTop (nhds 0) := by
    -- Proof comment: the Kolmogorov moment bound converts convergence of the approximation times
    -- into a vanishing geometric upper bound on the error probabilities.
    exact
      (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
        (ENNReal.div_ne_top ENNReal.coe_ne_top hδne0) hβqpos).comp hdist
  have hupper' :
      Filter.Tendsto
        (fun n ↦ ((C : ℝ≥0∞) * edist (clippedDyadicApprox T t n) t ^ (1 + (β : ℝ))) / δ)
        Filter.atTop (nhds 0) := by
    simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper' ?_ ?_
  · exact Filter.Eventually.of_forall fun n ↦ zero_le _
  · exact Filter.Eventually.of_forall hpointwise
