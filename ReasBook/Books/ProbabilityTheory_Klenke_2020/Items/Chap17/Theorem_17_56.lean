/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_56.Index

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction

noncomputable section

universe u v

namespace ProbabilityTheory

/-- Helper for Theorem 17.56: if a random variable has law `ρ` and `ρ` gives full mass to a
measurable set `s`, then the random variable lies in `s` almost surely. -/
private theorem ae_mem_of_hasLaw_prob_eq_one
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : ProbabilityMeasure Ω) {Y : Ω → α} {ρ : ProbabilityMeasure α}
    (hY : HasLaw Y (ρ : Measure α) P) {s : Set α} (hs : MeasurableSet s)
    (hρs : ρ s = 1) :
    ∀ᵐ ω ∂(P : Measure Ω), Y ω ∈ s := by
  let Ym : Ω → α := AEMeasurable.mk Y hY.aemeasurable
  have hYmPreMeasure : (P : Measure Ω) (Ym ⁻¹' s) = 1 := by
    calc
      (P : Measure Ω) (Ym ⁻¹' s) = Measure.map Ym (P : Measure Ω) s := by
        symm
        exact Measure.map_apply_of_aemeasurable
          hY.aemeasurable.measurable_mk.aemeasurable hs
      _ = Measure.map Y (P : Measure Ω) s := by
        exact congrArg (fun μ : Measure α ↦ μ s)
          (Measure.map_congr hY.aemeasurable.ae_eq_mk).symm
      _ = (ρ : Measure α) s := by
        simpa using congrArg (fun μ : Measure α ↦ μ s) hY.map_eq
      _ = 1 := by
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν := ρ) s]
        exact_mod_cast hρs
  have hYmMem : ∀ᵐ ω ∂(P : Measure Ω), Ym ω ∈ s := by
    exact (MeasureTheory.mem_ae_iff_prob_eq_one
      (hY.aemeasurable.measurable_mk hs)).2 hYmPreMeasure
  -- Proof comment: replace the measurable representative by the original random variable on the
  -- almost-sure set where they coincide.
  filter_upwards [hY.aemeasurable.ae_eq_mk, hYmMem] with ω hωeq hωmem
  simpa [Ym, hωeq] using hωmem

/-- Helper for Theorem 17.56: dyadic eventual distance bounds imply metric convergence. -/
private theorem tendsto_of_forall_eventually_dist_le_pow_half
    {α : Type*} [MetricSpace α] {u : α} {un : ℕ → α}
    (h : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, dist (un n) u ≤ (1 / 2 : ℝ) ^ m) :
    Tendsto un atTop (𝓝 u) := by
  -- Proof comment: the dyadic radii tend to zero, so one eventually enters every `ε`-ball.
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rcases (Metric.tendsto_atTop.mp hpow) ε hε with ⟨m, hm⟩
  have hmε : (1 / 2 : ℝ) ^ m < ε := by
    have hm' := hm m le_rfl
    simpa [Real.dist_eq, abs_of_nonneg (pow_nonneg (by norm_num) m)] using hm'
  rcases Filter.eventually_atTop.mp (h m) with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ lt_of_le_of_lt (hN n hn) hmε⟩

-- Route correction: the stale compiled wrapper theorem is replaced by a source-visible proof in
-- this wrapper file, using the Hilbert-cube compact core and a pullback along the embedding.
/-- Theorem 17.56: if probability measures `μn` on a Polish space `E` converge weakly to `μ`,
then one can realize them on one probability space with almost-sure convergence. -/
theorem exists_skorohod_coupling
    {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [PolishSpace E]
    (μ : ProbabilityMeasure E) (μn : ℕ → ProbabilityMeasure E)
    (hμn : Tendsto μn atTop (𝓝 μ)) :
    ∃ (Ω : Type v) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (X : Ω → E) (Xn : ℕ → Ω → E),
      HasLaw X (μ : Measure E) (P : Measure Ω) ∧
        (∀ n : ℕ, HasLaw (Xn n) (μn n : Measure E) (P : Measure Ω)) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω))) := by
  letI : Nonempty E := MeasureTheory.nonempty_of_isProbabilityMeasure (μ := (μ : Measure E))
  letI : TopologicalSpace.MetrizableSpace E := inferInstance
  letI : MetricSpace E := TopologicalSpace.metrizableSpaceMetric E
  obtain ⟨F, hFemb⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := E)
  let hFcont : Continuous F := hFemb.continuous
  let hFinj : Function.Injective F := hFemb.injective
  let hFrange : MeasurableSet (Set.range F) :=
    MeasureTheory.measurableSet_range_of_continuous_injective hFcont hFinj
  let hFmeasEmb : MeasurableEmbedding F := hFemb.measurableEmbedding hFrange
  let ν : ProbabilityMeasure (ℕ → unitInterval) :=
    ProbabilityMeasure.map μ hFmeasEmb.measurable.aemeasurable
  let νn : ℕ → ProbabilityMeasure (ℕ → unitInterval) :=
    fun n ↦ ProbabilityMeasure.map (μn n) hFmeasEmb.measurable.aemeasurable
  have hνn : Tendsto νn atTop (𝓝 ν) := by
    -- Proof comment: weak convergence is preserved by the continuous embedding into the Hilbert
    -- cube, checked through bounded continuous test functions.
    rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hcomp :=
      (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμn)
        (f.compContinuous ⟨F, hFcont⟩)
    have hrewrite :
        Tendsto
          (fun n ↦
            ∫ x, f x ∂((νn n : ProbabilityMeasure (ℕ → unitInterval)) :
              Measure (ℕ → unitInterval)))
          atTop
          (𝓝 (∫ x, f (F x) ∂(μ : Measure E))) := by
      refine (tendsto_congr' ?_).2 hcomp
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa [νn] using
          (MeasureTheory.integral_map (μ := (μn n : Measure E))
            hFcont.measurable.aemeasurable f.continuous.aestronglyMeasurable)
    have hlimit :
        ∫ x, f x ∂((ν : ProbabilityMeasure (ℕ → unitInterval)) :
          Measure (ℕ → unitInterval)) =
          ∫ x, f (F x) ∂(μ : Measure E) := by
      simpa [ν] using
        (MeasureTheory.integral_map (μ := (μ : Measure E))
          hFcont.measurable.aemeasurable f.continuous.aestronglyMeasurable)
    exact hlimit.symm ▸ hrewrite
  rcases existsHilbertCubeDyadicTailRealization (ν := ν) (νn := νn) hνn with
    ⟨Ω, mΩ, P, Y, Yn, hY, hYn, hdyadic⟩
  let X : Ω → E := hFmeasEmb.invFun ∘ Y
  let Xn : ℕ → Ω → E := fun n ↦ hFmeasEmb.invFun ∘ Yn n
  have hDecodeLaw :
      HasLaw hFmeasEmb.invFun (μ : Measure E) (ν : Measure (ℕ → unitInterval)) := by
    -- Proof comment: the measurable inverse of the embedding recovers `μ` from the pushed-forward
    -- Hilbert-cube law.
    refine ⟨hFmeasEmb.measurable_invFun.aemeasurable, ?_⟩
    simpa [ν, hFmeasEmb.leftInverse_invFun.comp_eq_id] using
      (MeasureTheory.Measure.map_map hFmeasEmb.measurable_invFun hFmeasEmb.measurable)
  have hDecodeLawSeq :
      ∀ n : ℕ,
        HasLaw hFmeasEmb.invFun (μn n : Measure E) (νn n : Measure (ℕ → unitInterval)) := by
    intro n
    -- Proof comment: the same inverse recovers every approximating law from its embedded image.
    refine ⟨hFmeasEmb.measurable_invFun.aemeasurable, ?_⟩
    simpa [νn, hFmeasEmb.leftInverse_invFun.comp_eq_id] using
      (MeasureTheory.Measure.map_map hFmeasEmb.measurable_invFun hFmeasEmb.measurable)
  have hνRangeProb : ν (Set.range F) = 1 := by
    -- Proof comment: every embedded law is supported on the range of the embedding.
    simpa [ν] using
      (ProbabilityMeasure.map_apply_of_aemeasurable (ν := μ) (f := F)
        hFmeasEmb.measurable.aemeasurable (A := Set.range F) hFmeasEmb.measurableSet_range)
  have hνnRangeProb : ∀ n : ℕ, νn n (Set.range F) = 1 := by
    intro n
    simpa [νn] using
      (ProbabilityMeasure.map_apply_of_aemeasurable (ν := μn n) (f := F)
        hFmeasEmb.measurable.aemeasurable (A := Set.range F) hFmeasEmb.measurableSet_range)
  have hYRange : ∀ᵐ ω ∂(P : Measure Ω), Y ω ∈ Set.range F := by
    -- Proof comment: the pushed-forward limit law is supported on the embedding range, so the
    -- realized Hilbert-cube random variable also lies in that range almost surely.
    exact ae_mem_of_hasLaw_prob_eq_one P hY hFmeasEmb.measurableSet_range hνRangeProb
  have hYnRange : ∀ n : ℕ, ∀ᵐ ω ∂(P : Measure Ω), Yn n ω ∈ Set.range F := by
    intro n
    -- Proof comment: each approximating embedded law has the same support property.
    exact ae_mem_of_hasLaw_prob_eq_one P (hYn n) hFmeasEmb.measurableSet_range (hνnRangeProb n)
  have hDyadicAll :
      ∀ᵐ ω ∂(P : Measure Ω),
        ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, dist (Yn n ω) (Y ω) ≤ (1 / 2 : ℝ) ^ m := by
    -- Proof comment: package the scale-wise eventual bounds on one common almost-sure event.
    exact ae_all_iff.mpr hdyadic
  have hConv : ∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω)) := by
    filter_upwards [hYRange, ae_all_iff.mpr hYnRange, hDyadicAll] with ω hωY hωYn hωDyadic
    have hCube : Tendsto (fun n ↦ Yn n ω) atTop (𝓝 (Y ω)) := by
      -- Proof comment: invoke the extracted dyadic convergence helper on the realized path.
      exact tendsto_of_forall_eventually_dist_le_pow_half hωDyadic
    have hFX : F (X ω) = Y ω := by
      rcases hωY with ⟨x, hx⟩
      calc
        F (X ω) = F (hFmeasEmb.invFun (Y ω)) := rfl
        _ = Y ω := by
          rw [← hx]
          simpa using congrArg F (hFmeasEmb.leftInverse_invFun x)
    have hFXn : ∀ n : ℕ, F (Xn n ω) = Yn n ω := by
      intro n
      rcases hωYn n with ⟨x, hx⟩
      calc
        F (Xn n ω) = F (hFmeasEmb.invFun (Yn n ω)) := rfl
        _ = Yn n ω := by
          rw [← hx]
          simpa using congrArg F (hFmeasEmb.leftInverse_invFun x)
    have hImage' : Tendsto (fun n ↦ F (Xn n ω)) atTop (𝓝 (Y ω)) := by
      refine hCube.congr' ?_
      exact Filter.Eventually.of_forall fun n ↦ (hFXn n).symm
    have hImage : Tendsto (fun n ↦ F (Xn n ω)) atTop (𝓝 (F (X ω))) := by
      simpa [hFX] using hImage'
    -- Proof comment: once the embedded paths converge, the embedding criterion pulls the
    -- convergence back to the original Polish space.
    exact (hFemb.tendsto_nhds_iff).2 hImage
  refine ⟨Ω, mΩ, P, X, Xn, ?_, ?_, hConv⟩
  · -- Proof comment: decode the limit Hilbert-cube random variable through the embedding inverse.
    simpa [X] using HasLaw.comp hDecodeLaw hY
  · intro n
    -- Proof comment: decode each approximating Hilbert-cube random variable in the same way.
    simpa [Xn] using HasLaw.comp (hDecodeLawSeq n) (hYn n)

end ProbabilityTheory
