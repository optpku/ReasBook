/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.OptionalStopping
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

/- Theorem 10.21 is `source-facing`: its public content is the finite-stopping-time extension of
optional sampling for uniformly integrable martingales and supermartingales. Its
`core/canonical` owner remains the mathlib theorem
`Martingale.stoppedValue_ae_eq_condExp_of_le` on `ℕ∞`-valued stopping times. The only
`bridge/view` layer used here is the finite-time coercion `Ω → ℕ` to `Ω → ℕ∞`, so the public API
keeps the source-facing finite stopping times while reusing the owner-shaped stopped-value
expressions directly. -/
variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {σ τ : Ω → ℕ}

local notation "σ∞" => fun ω ↦ (σ ω : ℕ∞)
local notation "τ∞" => fun ω ↦ (τ ω : ℕ∞)

/-- Helper for Theorem 10.21: pointwise multiplication by a varying indicator preserves uniform
integrability at exponent `1`. -/
lemma uniformIntegrableIndicatorFamily
    {f : ℕ → Ω → ℝ} {s : ℕ → Set Ω}
    (hf : UniformIntegrable f 1 μ) (hs : ∀ n, MeasurableSet (s n)) :
    UniformIntegrable (fun n ↦ (s n).indicator (f n)) 1 μ := by
  refine ⟨fun n ↦ (hf.aestronglyMeasurable n).indicator (hs n), ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδ_bound⟩ := hf.unifIntegrable hε
    refine ⟨δ, hδ, fun n t ht hμt ↦ ?_⟩
    have hswap :
        t.indicator ((s n).indicator (f n)) = (s n).indicator (t.indicator (f n)) := by
      ext ω
      by_cases hωt : ω ∈ t <;> by_cases hωs : ω ∈ s n <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hωt, hωs]
    calc
      eLpNorm (t.indicator ((s n).indicator (f n))) 1 μ
          = eLpNorm ((s n).indicator (t.indicator (f n))) 1 μ := by rw [hswap]
      _ ≤ eLpNorm (t.indicator (f n)) 1 μ := eLpNorm_indicator_le _
      _ ≤ ENNReal.ofReal ε := hδ_bound n t ht hμt
  · rcases hf.2.2 with ⟨C, hC⟩
    refine ⟨C, fun n ↦ ?_⟩
    exact (eLpNorm_indicator_le _).trans (hC n)

/-- Helper for Theorem 10.21: restricted almost-everywhere equalities on the countable cover
`⋃ n, s n = univ` glue to a global almost-everywhere equality. -/
lemma aeEq_of_countableRestrictCover
    {α : Type*} {f g : Ω → α} {s : ℕ → Set Ω}
    (hs_univ : (⋃ n, s n) = Set.univ)
    (hfg : ∀ n, f =ᵐ[μ.restrict (s n)] g) :
    f =ᵐ[μ] g := by
  -- First assemble the restricted equalities on the union of the slices.
  have hUnion : f =ᵐ[μ.restrict (⋃ n, s n)] g := by
    rw [ae_eq_restrict_iUnion_iff]
    exact hfg
  -- Then rewrite the union back to `univ`, where `μ.restrict univ = μ`.
  simpa [hs_univ] using hUnion

/-- Helper for Theorem 10.21: on the slice `{ω | ρ ω = n}`, the finite stopped value agrees
almost everywhere with the deterministic-time sample `X n`. -/
lemma stoppedValue_eq_detTime_onFiniteSlice
    {ρ : Ω → ℕ} (hρ : IsStoppingTime ℱ (fun ω ↦ (ρ ω : ℕ∞))) (n : ℕ) :
    X n =ᵐ[μ.restrict {ω | (ρ ω : ℕ∞) = n}] stoppedValue X (fun ω ↦ (ρ ω : ℕ∞)) := by
  -- On the slice `{ρ = n}`, the definition of `stoppedValue` collapses to the deterministic index.
  filter_upwards [ae_restrict_mem (ℱ.le _ _ (hρ.measurableSet_eq n))] with ω hω
  simp [stoppedValue, hω]

/-- Helper for Theorem 10.21: the absolute-value process of a real martingale is a
submartingale. -/
lemma abs_submartingale_of_martingale
    (hX : Martingale X ℱ μ) :
    Submartingale (fun n ω ↦ |X n ω|) ℱ μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    -- Adaptedness is preserved by applying the convex map `x ↦ |x|` pointwise.
    simpa [Real.norm_eq_abs] using (hX.stronglyMeasurable n).norm
  · intro i j hij
    -- Conditional Jensen gives `|𝔼[X_j | ℱ_i]| ≤ 𝔼[|X_j| | ℱ_i]`, and the martingale identity
    -- rewrites the left-hand side to `|X_i|`.
    have hnorm :
        (fun ω ↦ |μ[X j | ℱ i] ω|) ≤ᵐ[μ] μ[(fun ω ↦ |X j ω|) | ℱ i] := by
      simpa [Real.norm_eq_abs] using
        (AEStronglyMeasurable.norm_condExp_le
          ((hX.integrable j).aestronglyMeasurable) : _)
    filter_upwards [hX.condExp_ae_eq hij, hnorm] with ω hω_eq hω_le
    simpa [hω_eq] using hω_le
  · intro n
    -- Integrability of `|X_n|` is just integrability of `X_n` through the norm.
    simpa [Real.norm_eq_abs] using (hX.integrable n).norm

/-- Helper for Theorem 10.21: a uniformly integrable martingale stopped at a finite stopping time
is integrable. -/
lemma integrableStoppedValueOfUiFinite
    {ρ : Ω → ℕ} (hX : Martingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hρ : IsStoppingTime ℱ (fun ω ↦ (ρ ω : ℕ∞))) :
    Integrable (stoppedValue X (fun ω ↦ (ρ ω : ℕ∞))) μ := by
  let ρbar : Ω → ℕ∞ := fun ω ↦ (ρ ω : ℕ∞)
  let ρtrunc : ℕ → Ω → ℕ∞ := fun n ω ↦ min ((ρ ω : ℕ∞)) n
  let Z : ℕ → Ω → ℝ := fun n ω ↦ |X n ω|
  have hZ : Submartingale Z ℱ μ := abs_submartingale_of_martingale hX
  obtain ⟨R, hR⟩ := hX_UI.2.2
  have hX_l1_bound : ∀ n, ∫ ω, |X n ω| ∂μ ≤ R := by
    intro n
    -- Convert the uniform `L¹` bound from uniform integrability into a real integral bound.
    have hRn := hR n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable n)] at hRn
    exact_mod_cast hRn
  have htrunc_int : ∀ n, Integrable (stoppedValue Z (ρtrunc n)) μ := by
    intro n
    -- Each truncation is a bounded stopped value of the nonnegative submartingale `|X|`.
    exact integrable_stoppedValue ℕ (hρ.min_const n) hZ.integrable fun ω ↦ min_le_right _ _
  have htrunc_nonneg : ∀ n, 0 ≤ᵐ[μ] stoppedValue Z (ρtrunc n) := by
    intro n
    -- The stopped value of the absolute-value process is pointwise nonnegative.
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp [Z, ρtrunc, stoppedValue]
  have htrunc_bound : ∀ n, ∫ ω, stoppedValue Z (ρtrunc n) ω ∂μ ≤ R := by
    intro n
    have hmono :
        μ[stoppedValue Z (ρtrunc n)] ≤ μ[stoppedValue Z (fun _ ↦ (n : ℕ∞))] :=
      hZ.expected_stoppedValue_mono (hρ.min_const n) (isStoppingTime_const ℱ n)
        (fun ω ↦ min_le_right _ _) (fun _ ↦ le_rfl)
    -- Compare the bounded stopped value with the deterministic-time sample `|X n|`.
    calc
      ∫ ω, stoppedValue Z (ρtrunc n) ω ∂μ = μ[stoppedValue Z (ρtrunc n)] := rfl
      _ ≤ μ[stoppedValue Z (fun _ ↦ (n : ℕ∞))] := hmono
      _ = ∫ ω, |X n ω| ∂μ := by
            simp [Z, stoppedValue]
      _ ≤ R := hX_l1_bound n
  have hρ_ae_ne_top : ∀ᵐ ω ∂μ, ρbar ω ≠ ⊤ :=
    Filter.Eventually.of_forall fun ω ↦ by
      change ((ρ ω : ℕ∞) ≠ ⊤)
      simp
  have htrunc_meas :
      ∀ n, AEMeasurable (fun ω ↦ ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω)) μ := by
    intro n
    exact (htrunc_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have htrunc_tendsto :
      ∀ᵐ ω ∂μ,
        Filter.Tendsto (fun n ↦ ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω)) Filter.atTop
          (nhds (ENNReal.ofReal (stoppedValue Z ρbar ω))) := by
    -- Along each path, the truncations eventually stop at the same index as `ρ`.
    filter_upwards [stoppedValue_truncation_ae_eventuallyEq (X := Z) (μ := μ) (τ := ρbar)
      hρ_ae_ne_top] with ω hω
    have hEq :
        (fun n ↦ ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω)) =ᶠ[Filter.atTop]
          fun _ ↦ ENNReal.ofReal (stoppedValue Z ρbar ω) := by
      filter_upwards [hω] with n hn
      simpa [ρtrunc] using congrArg ENNReal.ofReal hn
    refine Filter.Tendsto.congr' hEq.symm ?_
    exact
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ ↦ ENNReal.ofReal (stoppedValue Z ρbar ω)) Filter.atTop
          (nhds (ENNReal.ofReal (stoppedValue Z ρbar ω))))
  have hFatou :
      ∫⁻ ω, ENNReal.ofReal (stoppedValue Z ρbar ω) ∂μ ≤
        Filter.liminf
          (fun n ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω) ∂μ) Filter.atTop := by
    -- Fatou upgrades the eventual pointwise stabilization to a finite `L¹` bound for `X_ρ`.
    calc
      ∫⁻ ω, ENNReal.ofReal (stoppedValue Z ρbar ω) ∂μ
          = ∫⁻ ω,
              Filter.liminf
                (fun n ↦ ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω)) Filter.atTop ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards [htrunc_tendsto] with ω hω
              exact hω.liminf_eq.symm
      _ ≤ Filter.liminf
            (fun n ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω) ∂μ) Filter.atTop := by
            exact MeasureTheory.lintegral_liminf_le' htrunc_meas
  have htrunc_lintegral_bound :
      ∀ᶠ n in Filter.atTop,
        ∫⁻ ω, ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω) ∂μ ≤ ENNReal.ofReal R := by
    filter_upwards with n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (htrunc_int n) (htrunc_nonneg n)]
    exact ENNReal.ofReal_le_ofReal (htrunc_bound n)
  have hLiminfBound :
      Filter.liminf
          (fun n ↦ ∫⁻ ω, ENNReal.ofReal (stoppedValue Z (ρtrunc n) ω) ∂μ) Filter.atTop
        ≤ ENNReal.ofReal R := by
    exact Filter.liminf_le_of_frequently_le htrunc_lintegral_bound.frequently
  have hstopped_meas :
      AEStronglyMeasurable (stoppedValue X ρbar) μ := by
    have hmeas_rel :
        Measurable[hρ.measurableSpace] (stoppedValue X ρbar) :=
      measurable_stoppedValue hX.stronglyAdapted.progMeasurable_of_discrete hρ
    have hmeas : Measurable (stoppedValue X ρbar) :=
      hmeas_rel.mono hρ.measurableSpace_le le_rfl
    exact hmeas.aemeasurable.aestronglyMeasurable
  have habs_eq : (fun ω ↦ stoppedValue Z ρbar ω) = fun ω ↦ |stoppedValue X ρbar ω| := by
    ext ω
    simp [Z, stoppedValue, ρbar]
  have habs_nonneg : 0 ≤ᵐ[μ] fun ω ↦ |stoppedValue X ρbar ω| :=
    Filter.Eventually.of_forall fun ω ↦ abs_nonneg _
  have habs_lintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (|stoppedValue X ρbar ω|) ∂μ ≠ ⊤ := by
    apply lt_top_iff_ne_top.mp
    simpa [habs_eq] using lt_of_le_of_lt (hFatou.trans hLiminfBound) ENNReal.ofReal_lt_top
  have habs_int : Integrable (fun ω ↦ |stoppedValue X ρbar ω|) μ := by
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        (hstopped_meas.norm) habs_nonneg).1 habs_lintegral_ne_top
  -- Convert integrability of `|X_ρ|` back to integrability of `X_ρ`.
  have hnorm_int : Integrable (fun ω ↦ ‖stoppedValue X ρbar ω‖) μ := by
    simpa [Real.norm_eq_abs] using habs_int
  simpa [ρbar] using (integrable_norm_iff hstopped_meas).1 hnorm_int

/-- Helper for Theorem 10.21: bounded optional sampling on the truncated test set
`s ∩ {σ ≤ n}` gives the textbook identity for `τ ∧ n` and `σ`. -/
lemma setIntegralTruncatedStopsEqOfFiniteTestSet
    (hX : Martingale X ℱ μ) (hσ : IsStoppingTime ℱ σ∞) (hτ : IsStoppingTime ℱ τ∞)
    (hστ : σ ≤ τ) {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s) (n : ℕ) :
    ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ n}, stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) n) ω ∂μ
      = ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ n}, stoppedValue X σ∞ ω ∂μ := by
  let σn : Ω → ℕ∞ := fun ω ↦ min ((σ ω : ℕ∞)) n
  let τn : Ω → ℕ∞ := fun ω ↦ min ((τ ω : ℕ∞)) n
  let t : Set Ω := s ∩ {ω | (σ ω : ℕ∞) ≤ n}
  have hσn : IsStoppingTime ℱ σn := hσ.min_const n
  have hτn : IsStoppingTime ℱ τn := hτ.min_const n
  have hσn_le_τn : σn ≤ τn := by
    intro ω
    exact min_le_min (show ((σ ω : ℕ∞) ≤ (τ ω : ℕ∞)) by exact_mod_cast hστ ω) le_rfl
  have ht_hσ : MeasurableSet[hσ.measurableSpace] t := by
    change MeasurableSet[hσ.measurableSpace] (s ∩ {ω | (σ ω : ℕ∞) ≤ n})
    exact hs.inter (hσ.measurableSet_le' n)
  have ht_hσn : MeasurableSet[hσn.measurableSpace] t := by
    change MeasurableSet[hσn.measurableSpace] (s ∩ {ω | (σ ω : ℕ∞) ≤ n})
    exact (hσ.measurableSet_inter_le_const_iff s n).1 ht_hσ
  have ht_meas : MeasurableSet t := hσn.measurableSpace_le _ ht_hσn
  have hτn_int : Integrable (stoppedValue X τn) μ := by
    exact integrable_stoppedValue ℕ hτn hX.integrable fun ω ↦ min_le_right _ _
  have hbounded :
      μ[stoppedValue X τn | hσn.measurableSpace] =ᵐ[μ] stoppedValue X σn :=
    (hX.stoppedValue_ae_eq_condExp_of_le hτn hσn hσn_le_τn
      (fun ω ↦ min_le_right _ _)).symm
  calc
    ∫ ω in t, stoppedValue X τn ω ∂μ =
        ∫ ω in t, μ[stoppedValue X τn | hσn.measurableSpace] ω ∂μ := by
          symm
          exact MeasureTheory.setIntegral_condExp hσn.measurableSpace_le hτn_int ht_hσn
    _ = ∫ ω in t, stoppedValue X σn ω ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae ht_meas ?_
          filter_upwards [hbounded] with ω hω _
          exact hω
    _ = ∫ ω in t, stoppedValue X σ∞ ω ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun ht_meas ?_
          intro ω hω
          have hω_mem : ω ∈ {x | (σ x : ℕ∞) ≤ n} := by
            simpa [t] using hω.2
          simpa [σn] using (stoppedValue_min_const_eqOn_le_const n) hω_mem

/-- Helper for Theorem 10.21: a finite stopping index is eventually dominated by the deterministic
counter `n`. -/
lemma eventually_ge_natStoppingValue (ρ : Ω → ℕ) (ω : Ω) :
    ∀ᶠ n in Filter.atTop, ((ρ ω : ℕ∞) ≤ n) := by
  exact Filter.eventually_atTop.2 ⟨ρ ω, fun n hn ↦ by exact_mod_cast hn⟩

/-- Helper for Theorem 10.21: uniform integrability is stable under pointwise addition at
exponent `1`. -/
lemma uniformIntegrable_add
    {ι : Type*} {f g : ι → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (f + g) 1 μ := by
  refine ⟨fun i ↦ (hf.aestronglyMeasurable i).add (hg.aestronglyMeasurable i), ?_, ?_⟩
  · -- Pass the quantitative uniform-integrability estimate through the addition theorem.
    exact hf.unifIntegrable.add hg.unifIntegrable le_rfl
      (fun i ↦ hf.aestronglyMeasurable i) (fun i ↦ hg.aestronglyMeasurable i)
  · rcases hf.2.2 with ⟨Cf, hCf⟩
    rcases hg.2.2 with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun i ↦ ?_⟩
    -- The uniform `L¹` bounds add exactly as in the triangle inequality.
    exact (eLpNorm_add_le (hf.aestronglyMeasurable i) (hg.aestronglyMeasurable i) le_rfl).trans
      (add_le_add (hCf i) (hCg i))

/-- Helper for Theorem 10.21: the bounded truncation `τ ∧ n` splits the stopped value into the
already-stopped part on `{τ ≤ n}` and the deterministic-time sample on `{n < τ}`. -/
lemma truncatedStoppedValue_split (n : ℕ) :
    stoppedValue X (fun ω ↦ min ((τ ω : ℕ∞)) (n : ℕ∞))
      =
    {ω | (τ ω : ℕ∞) ≤ (n : ℕ∞)}.indicator (stoppedValue X τ∞)
      + {ω | (n : ℕ∞) < (τ ω : ℕ∞)}.indicator (X n) := by
  ext ω
  by_cases hτn : τ ω ≤ n
  · -- Once `τ ω ≤ n`, the truncation has already reached the terminal stopped value.
    have hτn' : (τ ω : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hτn
    have hmin : min ((τ ω : ℕ∞)) (n : ℕ∞) = (τ ω : ℕ∞) := min_eq_left hτn'
    have hidx : (min ((τ ω : ℕ∞)) (n : ℕ∞)).untopA = τ ω := by
      rw [hmin]
      simp
    simp [hτn]
    change X (min ((τ ω : ℕ∞)) (n : ℕ∞)).untopA ω = X ((τ ω : ℕ∞).untopA) ω
    simpa using congrArg (fun k ↦ X k ω) hidx
  · -- Before the stopping time, the truncation is exactly the deterministic index `n`.
    have hnτ : n < τ ω := lt_of_not_ge hτn
    have hnτ' : (n : ℕ∞) < (τ ω : ℕ∞) := by exact_mod_cast hnτ
    have hmin : min ((τ ω : ℕ∞)) (n : ℕ∞) = (n : ℕ∞) := min_eq_right (le_of_lt hnτ')
    have hidx : (min ((τ ω : ℕ∞)) (n : ℕ∞)).untopA = n := by
      rw [hmin]
      simp
    simp [hτn, hnτ]
    change X (min ((τ ω : ℕ∞)) (n : ℕ∞)).untopA ω = X n ω
    simpa using congrArg (fun k ↦ X k ω) hidx

/-- Helper for Theorem 10.21: the bounded truncation family `n ↦ X_{τ ∧ n}` is uniformly
integrable whenever `X` is a uniformly integrable martingale and `τ` is finite. -/
lemma uniformIntegrableTruncatedStoppedValueFamily
    (hX : Martingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hτ : IsStoppingTime ℱ τ∞) :
    UniformIntegrable (fun n : ℕ ↦ stoppedValue X (fun ω ↦ min ((τ ω : ℕ∞)) (n : ℕ∞))) 1 μ := by
  have hτ_int : Integrable (stoppedValue X τ∞) μ :=
    integrableStoppedValueOfUiFinite hX hX_UI hτ
  have hτ_meas :
      ∀ n : ℕ, MeasurableSet {ω | (τ ω : ℕ∞) ≤ (n : ℕ∞)} := by
    intro n
    exact hτ.measurableSpace_le _ (hτ.measurableSet_le' n)
  have hconst_UI : UniformIntegrable (fun _ : ℕ ↦ stoppedValue X τ∞) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.2 hτ_int)
  have hleft_UI :
      UniformIntegrable
        (fun n : ℕ ↦ {ω | (τ ω : ℕ∞) ≤ (n : ℕ∞)}.indicator (stoppedValue X τ∞)) 1 μ :=
    uniformIntegrableIndicatorFamily hconst_UI hτ_meas
  have hright_UI :
      UniformIntegrable (fun n : ℕ ↦ {ω | (n : ℕ∞) < (τ ω : ℕ∞)}.indicator (X n)) 1 μ :=
    uniformIntegrableIndicatorFamily hX_UI fun n ↦ by
      simpa [Set.compl_setOf, not_le] using (hτ_meas n).compl
  -- Rewrite the truncation into the indicator split and combine the two UI pieces.
  convert uniformIntegrable_add hleft_UI hright_UI using 1
  ext n ω
  exact congrFun (truncatedStoppedValue_split (X := X) (τ := τ) n) ω

/-- Helper for Theorem 10.21: on a finite restricted measure, uniform integrability plus almost
everywhere convergence yields convergence of the restricted integrals. -/
lemma restrictedIntegralConvergenceOfUi
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {s : Set Ω}
    (hμs : μ s < ⊤) (hf_UI : UniformIntegrable f 1 μ) (hfi : ∀ n, Integrable (f n) μ)
    (hg : Integrable g μ)
    (hfg :
      ∀ᵐ ω ∂(μ.restrict s), Filter.Tendsto (fun n ↦ f n ω) Filter.atTop (nhds (g ω))) :
    Filter.Tendsto (fun n ↦ ∫ ω, f n ω ∂(μ.restrict s)) Filter.atTop
      (nhds (∫ ω, g ω ∂(μ.restrict s))) := by
  letI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
  have hf_UI_restrict : UniformIntegrable f 1 (μ.restrict s) := by
    refine ⟨fun n ↦ (hf_UI.aestronglyMeasurable n).mono_measure Measure.restrict_le_self,
      hf_UI.unifIntegrable.restrict s, ?_⟩
    rcases hf_UI.2.2 with ⟨C, hC⟩
    refine ⟨C, fun n ↦ ?_⟩
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC n)
  have hg_mem : MemLp g 1 (μ.restrict s) :=
    memLp_one_iff_integrable.2 hg.restrict
  have hLp :
      Filter.Tendsto (fun n ↦ eLpNorm (f n - g) 1 (μ.restrict s)) Filter.atTop (nhds 0) :=
    MeasureTheory.tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp)
      (fun n ↦ (hfi n).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      hg_mem hf_UI_restrict.unifIntegrable hfg
  -- Once the restricted family converges in `L¹`, the restricted integrals converge as well.
  exact MeasureTheory.tendsto_integral_of_L1' g hg.restrict
    (Filter.Eventually.of_forall fun n ↦ (hfi n).restrict) hLp

lemma setIntegralStoppedValueEqOfUiFinite
    (hX : Martingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hσ : IsStoppingTime ℱ σ∞) (hτ : IsStoppingTime ℱ τ∞) (hστ : σ ≤ τ)
    {s : Set Ω} (hs : MeasurableSet[hσ.measurableSpace] s) (_hμs : μ s < ⊤) :
    ∫ ω in s, stoppedValue X τ∞ ω ∂μ = ∫ ω in s, stoppedValue X σ∞ ω ∂μ := by
  -- Route correction: avoid the stronger `limitProcess` bridge and work directly with the
  -- truncated bounded optional-sampling identity on finite `𝓕_σ`-test sets.
  let L : ℕ → Ω → ℝ :=
    fun n ↦ {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}.indicator
      (stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞)))
  let R : ℕ → Ω → ℝ :=
    fun n ↦ {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}.indicator (stoppedValue X σ∞)
  have hτ_int : Integrable (stoppedValue X τ∞) μ :=
    integrableStoppedValueOfUiFinite hX hX_UI hτ
  have hσ_int : Integrable (stoppedValue X σ∞) μ :=
    integrableStoppedValueOfUiFinite hX hX_UI hσ
  have hσ_meas :
      ∀ n : ℕ, MeasurableSet {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)} := by
    intro n
    exact hσ.measurableSpace_le _ (hσ.measurableSet_le' n)
  have htrunc_UI :
      UniformIntegrable (fun n : ℕ ↦ stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞))) 1 μ :=
    uniformIntegrableTruncatedStoppedValueFamily hX hX_UI hτ
  have hL_UI : UniformIntegrable L 1 μ :=
    uniformIntegrableIndicatorFamily htrunc_UI hσ_meas
  have hσ_const_UI : UniformIntegrable (fun _ : ℕ ↦ stoppedValue X σ∞) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.2 hσ_int)
  have hR_UI : UniformIntegrable R 1 μ :=
    uniformIntegrableIndicatorFamily hσ_const_UI hσ_meas
  have htrunc_int :
      ∀ n : ℕ, Integrable (stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞))) μ := by
    intro n
    -- Each truncated stopped value is bounded by the deterministic time `n`.
    exact integrable_stoppedValue ℕ (hτ.min_const n) hX.integrable fun ω ↦ min_le_right _ _
  have hL_int : ∀ n, Integrable (L n) μ := by
    intro n
    -- Restricting an integrable truncation to `{σ ≤ n}` preserves integrability.
    exact (htrunc_int n).indicator (hσ_meas n)
  have hR_int : ∀ n, Integrable (R n) μ := by
    intro n
    -- The right family is the same stopped value, cut down by the same finite-time test set.
    exact hσ_int.indicator (hσ_meas n)
  have htrunc_eq :
      ∀ n : ℕ,
        ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ n},
            stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) n) ω ∂μ
          =
        ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ n}, stoppedValue X σ∞ ω ∂μ := by
    intro n
    exact setIntegralTruncatedStopsEqOfFiniteTestSet hX hσ hτ hστ hs n
  have hσ_eventually_ae :
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in Filter.atTop, ((σ ω : ℕ∞) ≤ (n : ℕ∞)) :=
    Filter.Eventually.of_forall fun ω ↦ by
      exact Filter.eventually_atTop.2 ⟨σ ω, fun n hn ↦ by exact_mod_cast hn⟩
  have hτ_ae_ne_top : ∀ᵐ ω ∂μ, τ∞ ω ≠ ⊤ :=
    Filter.Eventually.of_forall fun ω ↦ by simp
  have hL_tendsto :
      ∀ᵐ ω ∂(μ.restrict s),
        Filter.Tendsto (fun n ↦ L n ω) Filter.atTop (nhds (stoppedValue X τ∞ ω)) := by
    have hτ_trunc :
        ∀ᵐ ω ∂μ,
          ∀ᶠ n : ℕ in Filter.atTop,
            stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞)) ω = stoppedValue X τ∞ ω :=
      stoppedValue_truncation_ae_eventuallyEq (X := X) (μ := μ) (τ := τ∞) hτ_ae_ne_top
    refine ae_restrict_of_ae ?_
    filter_upwards [hτ_trunc, hσ_eventually_ae] with ω hτω hσω
    have hEq : (fun n ↦ L n ω) =ᶠ[Filter.atTop] fun _ ↦ stoppedValue X τ∞ ω := by
      filter_upwards [hτω, hσω] with n hnτ hnσ
      have hmem : ω ∈ {x | (σ x : ℕ∞) ≤ (n : ℕ∞)} := by simpa using hnσ
      change
        {x | (σ x : ℕ∞) ≤ (n : ℕ∞)}.indicator
            (stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞))) ω
          =
        stoppedValue X τ∞ ω
      rw [Set.indicator_of_mem hmem]
      exact hnτ
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  have hR_tendsto :
      ∀ᵐ ω ∂(μ.restrict s),
        Filter.Tendsto (fun n ↦ R n ω) Filter.atTop (nhds (stoppedValue X σ∞ ω)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hσ_eventually_ae] with ω hσω
    have hEq : (fun n ↦ R n ω) =ᶠ[Filter.atTop] fun _ ↦ stoppedValue X σ∞ ω := by
      filter_upwards [hσω] with n hnσ
      have hmem : ω ∈ {x | (σ x : ℕ∞) ≤ (n : ℕ∞)} := by simpa using hnσ
      change {x | (σ x : ℕ∞) ≤ (n : ℕ∞)}.indicator (stoppedValue X σ∞) ω = stoppedValue X σ∞ ω
      rw [Set.indicator_of_mem hmem]
    exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds
  have hL_integral :
      ∀ n : ℕ,
        ∫ ω, L n ω ∂(μ.restrict s)
          =
        ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ n},
            stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) n) ω ∂μ := by
    intro n
    -- Rewrite the restricted integral of the indicator family back to the original set integral.
    change
      ∫ ω,
          {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}.indicator
            (stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞))) ω ∂(μ.restrict s)
        =
      ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)},
          stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞)) ω ∂μ
    rw [MeasureTheory.integral_indicator (μ := μ.restrict s)
      (f := stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞)))
      (s := {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}) (hσ_meas n)]
    change
      ∫ ω, stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞)) ω ∂
          ((μ.restrict s).restrict {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)})
        =
      ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)},
          stoppedValue X (fun x ↦ min ((τ x : ℕ∞)) (n : ℕ∞)) ω ∂μ
    rw [Measure.restrict_restrict (hσ_meas n), Set.inter_comm]
  have hR_integral :
      ∀ n : ℕ,
        ∫ ω, R n ω ∂(μ.restrict s)
          =
        ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ n}, stoppedValue X σ∞ ω ∂μ := by
    intro n
    -- The same transport identifies the right restricted integrals with the original test-set
    -- integrals of `X_σ`.
    change
      ∫ ω, {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}.indicator (stoppedValue X σ∞) ω ∂(μ.restrict s)
        =
      ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}, stoppedValue X σ∞ ω ∂μ
    rw [MeasureTheory.integral_indicator (μ := μ.restrict s)
      (f := stoppedValue X σ∞) (s := {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}) (hσ_meas n)]
    change
      ∫ ω, stoppedValue X σ∞ ω ∂((μ.restrict s).restrict {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)})
        =
      ∫ ω in s ∩ {ω | (σ ω : ℕ∞) ≤ (n : ℕ∞)}, stoppedValue X σ∞ ω ∂μ
    rw [Measure.restrict_restrict (hσ_meas n), Set.inter_comm]
  have hL_limit :
      Filter.Tendsto (fun n ↦ ∫ ω, L n ω ∂(μ.restrict s)) Filter.atTop
        (nhds (∫ ω, stoppedValue X τ∞ ω ∂(μ.restrict s))) :=
    restrictedIntegralConvergenceOfUi _hμs hL_UI hL_int hτ_int hL_tendsto
  have hR_limit :
      Filter.Tendsto (fun n ↦ ∫ ω, R n ω ∂(μ.restrict s)) Filter.atTop
        (nhds (∫ ω, stoppedValue X σ∞ ω ∂(μ.restrict s))) :=
    restrictedIntegralConvergenceOfUi _hμs hR_UI hR_int hσ_int hR_tendsto
  have hR_limit_on_L :
      Filter.Tendsto (fun n ↦ ∫ ω, L n ω ∂(μ.restrict s)) Filter.atTop
        (nhds (∫ ω, stoppedValue X σ∞ ω ∂(μ.restrict s))) := by
    -- Transport the truncated bounded identity to the restricted measure side before taking
    -- limits.
    refine hR_limit.congr' ?_
    filter_upwards with n
    rw [hL_integral n, hR_integral n, htrunc_eq n]
  have hrestrict_eq :
      ∫ ω, stoppedValue X τ∞ ω ∂(μ.restrict s)
        =
      ∫ ω, stoppedValue X σ∞ ω ∂(μ.restrict s) :=
    tendsto_nhds_unique hL_limit hR_limit_on_L
  -- Convert the restricted-integral identity back to the textbook set-integral identity.
  simpa using hrestrict_eq

/-- Helper for Theorem 10.21: the predictable part of a supermartingale is almost surely
nonpositive at every deterministic time. -/
lemma predictablePart_nonpos_ae_of_supermartingale
    (hX : Supermartingale X ℱ μ) :
    ∀ n, predictablePart X ℱ μ n ≤ᵐ[μ] 0 := by
  intro n
  -- Compare the predictable part at time `n` with its initial value `0`.
  filter_upwards [supermartingale_ae_antitone_predictablePart hX] with
    ω hω
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

/-- Helper for Theorem 10.21: an absolute domination for every deterministic time propagates to
every finite stopped value. -/
lemma stoppedValue_abs_ae_le_of_abs_ae_le_all
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {ρ : Ω → ℕ}
    (hdom : ∀ n, |f n| ≤ᵐ[μ] g) :
    |stoppedValue f (fun ω ↦ (ρ ω : ℕ∞))| ≤ᵐ[μ] g := by
  -- Evaluate the pointwise family domination at the selected stopping index.
  filter_upwards [ae_all_iff.2 hdom] with ω hω
  simpa [stoppedValue] using hω (ρ ω)

/-- Helper for Theorem 10.21: if `σ ≤ τ` are finite stopping times, then the predictable part of a
supermartingale sampled at `τ` is almost surely bounded above by the same predictable part sampled
at `σ`. -/
lemma predictablePart_stoppedValue_ae_le_of_le_of_finite
    (hX : Supermartingale X ℱ μ) (hστ : σ ≤ τ) :
    stoppedValue (predictablePart X ℱ μ) τ∞ ≤ᵐ[μ] stoppedValue (predictablePart X ℱ μ) σ∞ := by
  -- The finite-time coercion removes all `⊤` cases, so the deterministic-time antitonicity of
  -- the predictable part can be applied pathwise at the selected indices.
  filter_upwards [supermartingale_ae_antitone_predictablePart hX] with
    ω hω
  have hτ_top : τ∞ ω ≠ ⊤ := by simp
  have hσ_idx_le_τ_idx : (σ∞ ω).untopA ≤ (τ∞ ω).untopA :=
    WithTop.untopA_mono hτ_top (by
      change ((σ ω : ℕ∞) ≤ (τ ω : ℕ∞))
      exact_mod_cast hστ ω)
  simpa [stoppedValue] using hω hσ_idx_le_τ_idx

/-- Helper for Theorem 10.21: an almost-everywhere absolute domination by one integrable function
implies uniform integrability at exponent `1`. -/
lemma uniformIntegrable_of_abs_ae_le
    {ι : Type*} {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg : Integrable g μ)
    (hdom : ∀ i, ∀ᵐ ω ∂μ, |f i ω| ≤ g ω) :
    UniformIntegrable f 1 μ := by
  have hconst : UniformIntegrable (fun _ : ι ↦ g) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.2 hg)
  refine ⟨hf_meas, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδ_bound⟩ := hconst.2.1 hε
    refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
    refine (eLpNorm_mono_ae_real ?_).trans (hδ_bound i s hs hμs)
    filter_upwards [hdom i] with ω hω
    by_cases hmem : ω ∈ s
    · simpa [Set.indicator_of_mem, hmem] using hω
    · simp [Set.indicator_of_notMem, hmem]
  · rcases hconst.2.2 with ⟨C, hC⟩
    refine ⟨C, fun i ↦ ?_⟩
    exact (eLpNorm_mono_ae_real (hdom i)).trans (hC i)

/-- Helper for Theorem 10.21: uniform integrability is stable under pointwise subtraction at
exponent `1`. -/
lemma uniformIntegrable_sub
    {ι : Type*} {f g : ι → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (f - g) 1 μ := by
  refine ⟨fun i ↦ (hf.aestronglyMeasurable i).sub (hg.aestronglyMeasurable i), ?_, ?_⟩
  · exact hf.unifIntegrable.sub hg.unifIntegrable le_rfl
      (fun i ↦ hf.aestronglyMeasurable i) (fun i ↦ hg.aestronglyMeasurable i)
  · rcases hf.2.2 with ⟨Cf, hCf⟩
    rcases hg.2.2 with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun i ↦ ?_⟩
    simpa [sub_eq_add_neg] using
      (eLpNorm_add_le (hf.aestronglyMeasurable i) ((hg.aestronglyMeasurable i).neg) le_rfl).trans
        (by
          rw [eLpNorm_neg]
          exact add_le_add (hCf i) (hCg i))

/-- Helper for Theorem 10.21: uniform integrability is stable under restricting the ambient
measure. -/
lemma uniformIntegrable_restrict
    {ι : Type*} {f : ι → Ω → ℝ} (hf : UniformIntegrable f 1 μ) (s : Set Ω) :
    UniformIntegrable f 1 (μ.restrict s) := by
  refine ⟨fun i ↦ (hf.aestronglyMeasurable i).mono_measure Measure.restrict_le_self,
    hf.unifIntegrable.restrict s, ?_⟩
  rcases hf.2.2 with ⟨C, hC⟩
  refine ⟨C, fun i ↦ ?_⟩
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i)

/-- Helper for Theorem 10.21: the predictable part of a uniformly integrable supermartingale is
almost surely dominated in absolute value by one integrable random variable. -/
lemma predictablePart_abs_ae_le_integrableBound_of_ui_supermartingale
    (hX : Supermartingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ n, |predictablePart X ℱ μ n| ≤ᵐ[μ] g := by
  let A := predictablePart X ℱ μ
  let M := martingalePart X ℱ μ
  have hA_strong : StronglyAdapted ℱ A := by
    simpa [A] using (stronglyAdapted_predictablePart' : StronglyAdapted ℱ A)
  obtain ⟨R, hR⟩ := hX_UI.2.2
  have hA_meas : ∀ n, Measurable (A n) := by
    intro n
    exact ((hA_strong n).mono (ℱ.le n)).measurable
  have hA_nonpos : ∀ n, A n ≤ᵐ[μ] 0 :=
    predictablePart_nonpos_ae_of_supermartingale hX
  have hB_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω ↦ -A n ω := by
    intro n
    -- The predictable part is a.s. nonpositive, so its negative is a.s. nonnegative.
    filter_upwards [hA_nonpos n] with ω hω
    exact neg_nonneg.mpr hω
  have hB_mono : ∀ᵐ ω ∂μ, Monotone fun n ↦ ENNReal.ofReal (-A n ω) := by
    -- Negating the a.s. antitone predictable part produces an a.s. monotone increasing family.
    filter_upwards [supermartingale_ae_antitone_predictablePart hX] with ω hω
    intro i j hij
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (hω hij))
  have hM : Martingale M ℱ μ := martingale_martingalePart hX.stronglyAdapted hX.integrable
  have hM0 : M 0 = X 0 := by
    -- At time `0`, the predictable part vanishes.
    ext ω
    simp [M, martingalePart, predictablePart_zero]
  have hA_int : ∀ n, Integrable (A n) μ := by
    intro n
    -- Each deterministic predictable value is a finite sum of conditional expectations.
    dsimp [A, predictablePart]
    rw [show (∑ i ∈ Finset.range n, μ[X (i + 1) - X i | ℱ i]) =
        (fun ω ↦ ∑ i ∈ Finset.range n, μ[X (i + 1) - X i | ℱ i] ω) by
      ext ω
      simp [Finset.sum_apply]]
    exact integrable_finset_sum (Finset.range n) fun i _ ↦ (integrable_condExp : Integrable
      (μ[X (i + 1) - X i | ℱ i]) μ)
  have hB_int : ∀ n, Integrable (fun ω ↦ -A n ω) μ := by
    intro n
    exact (hA_int n).neg
  have hX_l1_bound : ∀ n, ∫ ω, |X n ω| ∂μ ≤ R := by
    intro n
    -- Convert the uniform `eLpNorm` bound from uniform integrability into a real `L¹` bound.
    have hRn := hR n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable n)] at hRn
    exact_mod_cast hRn
  have hM_integral_eq : ∀ n, ∫ ω, M n ω ∂μ = ∫ ω, X 0 ω ∂μ := by
    intro n
    -- A martingale has constant expectations at deterministic times.
    calc
      ∫ ω, M n ω ∂μ = ∫ ω, M 0 ω ∂μ := by
        symm
        simpa using hM.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
      _ = ∫ ω, X 0 ω ∂μ := by simp [hM0]
  have hB_integral_le : ∀ n, ∫ ω, -A n ω ∂μ ≤ (2 : ℝ) * R := by
    intro n
    -- Decompose `-A n` as `M n - X n` and bound the two expectations by the uniform `L¹` bound.
    have hsplit : (fun ω ↦ -A n ω) = M n - X n := by
      ext ω
      have hω : M n ω + A n ω = X n ω := by
        simpa [M, A] using congrFun (congrFun (martingalePart_add_predictablePart ℱ μ X) n) ω
      change -A n ω = M n ω - X n ω
      linarith
    calc
      ∫ ω, -A n ω ∂μ = ∫ ω, M n ω ∂μ - ∫ ω, X n ω ∂μ := by
        rw [hsplit]
        simpa [Pi.sub_apply] using integral_sub (hM.integrable n) (hX.integrable n)
      _ ≤ |∫ ω, M n ω ∂μ| + |∫ ω, X n ω ∂μ| := by
        have hleft : ∫ ω, M n ω ∂μ ≤ |∫ ω, M n ω ∂μ| := le_abs_self _
        have hright : -∫ ω, X n ω ∂μ ≤ |∫ ω, X n ω ∂μ| := by
          simpa using neg_le_abs (∫ ω, X n ω ∂μ)
        linarith
      _ = |∫ ω, X 0 ω ∂μ| + |∫ ω, X n ω ∂μ| := by rw [hM_integral_eq n]
      _ ≤ ∫ ω, |X 0 ω| ∂μ + ∫ ω, |X n ω| ∂μ := by
        gcongr
        · simpa [Real.norm_eq_abs] using (norm_integral_le_integral_norm (X 0))
        · simpa [Real.norm_eq_abs] using (norm_integral_le_integral_norm (X n))
      _ ≤ R + R := add_le_add (hX_l1_bound 0) (hX_l1_bound n)
      _ = (2 : ℝ) * R := by ring
  let G : Ω → ENNReal := fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal (-A n ω)
  have hG_meas : Measurable G := by
    -- The monotone envelope is measurable as a countable supremum of measurable functions.
    refine Measurable.iSup fun n ↦ ?_
    exact (hA_meas n).neg.ennreal_ofReal
  have hG_lintegral :
      ∫⁻ ω, G ω ∂μ = ⨆ n, ∫⁻ ω, ENNReal.ofReal (-A n ω) ∂μ := by
    simpa [G] using MeasureTheory.lintegral_iSup'
      (fun n ↦ ((hA_meas n).neg.aemeasurable).ennreal_ofReal) hB_mono
  have hG_lintegral_le : ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal ((2 : ℝ) * R) := by
    -- Monotone convergence reduces the envelope bound to the deterministic-time integral bounds.
    rw [hG_lintegral]
    refine iSup_le fun n ↦ ?_
    have hnorm_eq :
        ∫⁻ ω, ENNReal.ofReal (-A n ω) ∂μ =
          ENNReal.ofReal (∫ ω, -A n ω ∂μ) := by
      have hnorm_integral :
          ENNReal.ofReal (∫ ω, ‖-A n ω‖ ∂μ) = ∫⁻ ω, ENNReal.ofReal (-A n ω) ∂μ := by
        calc
          ENNReal.ofReal (∫ ω, ‖-A n ω‖ ∂μ) = ∫⁻ ω, ‖-A n ω‖ₑ ∂μ := by
            exact ofReal_integral_norm_eq_lintegral_enorm (hB_int n)
          _ = ∫⁻ ω, ENNReal.ofReal (-A n ω) ∂μ := by
            rw [lintegral_enorm_of_ae_nonneg (hB_nonneg n)]
      have habs :
          ∫ ω, ‖-A n ω‖ ∂μ = ∫ ω, -A n ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hB_nonneg n] with ω hω
        simpa using (Real.norm_of_nonneg hω)
      calc
        ∫⁻ ω, ENNReal.ofReal (-A n ω) ∂μ = ENNReal.ofReal (∫ ω, ‖-A n ω‖ ∂μ) := by
          exact hnorm_integral.symm
        _ = ENNReal.ofReal (∫ ω, -A n ω ∂μ) := by rw [habs]
    rw [hnorm_eq]
    exact ENNReal.ofReal_le_ofReal (hB_integral_le n)
  have hG_ne_top : ∫⁻ ω, G ω ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt hG_lintegral_le ENNReal.ofReal_lt_top).ne
  let g : Ω → ℝ := fun ω ↦ (G ω).toReal
  have hg_int : Integrable g μ := by
    -- Finite `ℝ≥0∞`-mass of the envelope turns into integrability of its real-valued `toReal`.
    exact integrable_toReal_of_lintegral_ne_top hG_meas.aemeasurable hG_ne_top
  have hG_lt_top : ∀ᵐ ω ∂μ, G ω < ⊤ := ae_lt_top hG_meas hG_ne_top
  refine ⟨g, hg_int, ?_⟩
  intro n
  -- Compare the deterministic predictable part with the `toReal` of the monotone envelope.
  filter_upwards [hA_nonpos n, hG_lt_top] with ω hω hGω
  have hle_enn : ENNReal.ofReal (-A n ω) ≤ G ω := by
    exact le_iSup (fun m ↦ ENNReal.ofReal (-A m ω)) n
  have hle : -A n ω ≤ g ω := by
    change -A n ω ≤ (G ω).toReal
    exact (ENNReal.ofReal_le_iff_le_toReal hGω.ne).1 hle_enn
  simpa [A, g, abs_of_nonpos hω] using hle

/-- Helper for Theorem 10.21: the martingale part of a uniformly integrable supermartingale is
again uniformly integrable. -/
lemma martingalePart_uniformIntegrable_of_ui_supermartingale
    (hX : Supermartingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ) :
    UniformIntegrable (martingalePart X ℱ μ) 1 μ := by
  obtain ⟨g, hg_int, hg_dom⟩ :=
    predictablePart_abs_ae_le_integrableBound_of_ui_supermartingale hX hX_UI
  have hA_strong : StronglyAdapted ℱ (predictablePart X ℱ μ) := by
    simpa using (stronglyAdapted_predictablePart' :
      StronglyAdapted ℱ (predictablePart X ℱ μ))
  have hA_UI : UniformIntegrable (predictablePart X ℱ μ) 1 μ := by
    -- Dominate the predictable part by one integrable envelope and apply the general UI transfer
    -- lemma for exponent `1`.
    refine uniformIntegrable_of_abs_ae_le
      (fun n ↦
        ((hA_strong n).mono (ℱ.le n)).aestronglyMeasurable)
      hg_int hg_dom
  -- The martingale part is definitionally `X - predictablePart X ℱ μ`, so UI is stable under
  -- subtraction once the predictable part has been dominated.
  simpa [martingalePart] using uniformIntegrable_sub hX_UI hA_UI

-- Proof sketch: apply the bounded optional sampling identity to the truncations `σ ∧ n` and
-- `τ ∧ n`, use uniform integrability to upgrade convergence in measure of the stopped values to
-- convergence in `L¹`, and then pass the conditional expectations to the limit.
/-- Theorem 10.21 (1): if `X` is a uniformly integrable martingale and `σ ≤ τ` are finite
stopping times, then `stoppedValue X τ` is integrable and its conditional expectation with respect
to `𝓕_σ` agrees almost surely with `stoppedValue X σ`. -/
theorem martingale_condExp_stoppedValue_ae_eq_of_uniformIntegrable_of_le_of_finite
    (hX : Martingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hσ : IsStoppingTime ℱ σ∞) (hτ : IsStoppingTime ℱ τ∞) (hστ : σ ≤ τ) :
    Integrable (stoppedValue X τ∞) μ ∧
      μ[stoppedValue X τ∞ | hσ.measurableSpace] =ᵐ[μ] stoppedValue X σ∞ := by
  have hτ_int : Integrable (stoppedValue X τ∞) μ :=
    integrableStoppedValueOfUiFinite hX hX_UI hτ
  have hσ_int : Integrable (stoppedValue X σ∞) μ :=
    integrableStoppedValueOfUiFinite hX hX_UI hσ
  have hσ_meas :
      AEStronglyMeasurable[hσ.measurableSpace] (stoppedValue X σ∞) μ := by
    have hmeas :
        Measurable[hσ.measurableSpace] (stoppedValue X σ∞) :=
      measurable_stoppedValue hX.stronglyAdapted.progMeasurable_of_discrete hσ
    exact hmeas.stronglyMeasurable.aestronglyMeasurable
  -- Route correction: identify the conditional expectation directly by the finite-test-set
  -- uniqueness theorem, using the textbook truncation identity packaged in
  -- `setIntegralStoppedValueEqOfUiFinite`.
  refine ⟨hτ_int, ?_⟩
  exact
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hσ.measurableSpace_le hτ_int
      (fun s hs hμs ↦ hσ_int.integrableOn)
      (fun s hs hμs ↦ (setIntegralStoppedValueEqOfUiFinite hX hX_UI hσ hτ hστ hs hμs).symm)
      hσ_meas).symm

-- Proof sketch: write the uniformly integrable supermartingale as the sum of its martingale part
-- and its decreasing predictable part, apply the martingale optional sampling identity to the
-- martingale part, and use monotonicity of the predictable part and of conditional expectation to
-- obtain the inequality.
/-- Theorem 10.21 (2): if `X` is a uniformly integrable supermartingale and `σ ≤ τ` are finite
stopping times, then `stoppedValue X τ` is integrable and its conditional expectation with respect
to `𝓕_σ` is almost surely bounded above by `stoppedValue X σ`. -/
theorem supermartingale_condExp_stoppedValue_ae_le_of_uniformIntegrable_of_le_of_finite
    (hX : Supermartingale X ℱ μ) (hX_UI : UniformIntegrable X 1 μ)
    (hσ : IsStoppingTime ℱ σ∞) (hτ : IsStoppingTime ℱ τ∞) (hστ : σ ≤ τ) :
    Integrable (stoppedValue X τ∞) μ ∧
      μ[stoppedValue X τ∞ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X σ∞ := by
  let M := martingalePart X ℱ μ
  let A := predictablePart X ℱ μ
  have hAadp : StronglyAdapted ℱ A := by
    simpa [A] using (stronglyAdapted_predictablePart' : StronglyAdapted ℱ A)
  have hM : Martingale M ℱ μ := martingale_martingalePart hX.stronglyAdapted hX.integrable
  have hM_UI : UniformIntegrable M 1 μ :=
    martingalePart_uniformIntegrable_of_ui_supermartingale hX hX_UI
  have hM_stop :
      Integrable (stoppedValue M τ∞) μ ∧
        μ[stoppedValue M τ∞ | hσ.measurableSpace] =ᵐ[μ] stoppedValue M σ∞ :=
    martingale_condExp_stoppedValue_ae_eq_of_uniformIntegrable_of_le_of_finite hM hM_UI hσ hτ hστ
  obtain ⟨g, hg_int, hg_dom⟩ :=
    predictablePart_abs_ae_le_integrableBound_of_ui_supermartingale hX hX_UI
  have hAτ_dom : |stoppedValue A τ∞| ≤ᵐ[μ] g :=
    stoppedValue_abs_ae_le_of_abs_ae_le_all hg_dom
  have hAσ_dom : |stoppedValue A σ∞| ≤ᵐ[μ] g :=
    stoppedValue_abs_ae_le_of_abs_ae_le_all hg_dom
  have hAτ_meas : AEStronglyMeasurable (stoppedValue A τ∞) μ := by
    have hAτ_measurable_rel : Measurable[hτ.measurableSpace] (stoppedValue A τ∞) :=
      measurable_stoppedValue hAadp.progMeasurable_of_discrete hτ
    have hAτ_measurable : Measurable (stoppedValue A τ∞) :=
      hAτ_measurable_rel.mono hτ.measurableSpace_le le_rfl
    exact hAτ_measurable.aemeasurable.aestronglyMeasurable
  have hAσ_meas : AEStronglyMeasurable (stoppedValue A σ∞) μ := by
    have hAσ_measurable_rel : Measurable[hσ.measurableSpace] (stoppedValue A σ∞) :=
      measurable_stoppedValue hAadp.progMeasurable_of_discrete hσ
    have hAσ_measurable : Measurable (stoppedValue A σ∞) :=
      hAσ_measurable_rel.mono hσ.measurableSpace_le le_rfl
    exact hAσ_measurable.aemeasurable.aestronglyMeasurable
  have hAτ_int : Integrable (stoppedValue A τ∞) μ := by
    -- The predictable stopped value inherits integrability from the same global envelope.
    refine hg_int.mono' hAτ_meas ?_
    simpa [Real.norm_eq_abs] using hAτ_dom
  have hAσ_int : Integrable (stoppedValue A σ∞) μ := by
    -- The earlier stopped predictable part is controlled by the same envelope.
    refine hg_int.mono' hAσ_meas ?_
    simpa [Real.norm_eq_abs] using hAσ_dom
  have hA_stop :
      μ[stoppedValue A τ∞ | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue A σ∞ := by
    have hmono :
        μ[stoppedValue A τ∞ | hσ.measurableSpace] ≤ᵐ[μ]
          μ[stoppedValue A σ∞ | hσ.measurableSpace] :=
      condExp_mono hAτ_int hAσ_int
        (predictablePart_stoppedValue_ae_le_of_le_of_finite hX hστ)
    have hmeas :
        μ[stoppedValue A σ∞ | hσ.measurableSpace] = stoppedValue A σ∞ := by
      refine condExp_of_stronglyMeasurable hσ.measurableSpace_le ?_ hAσ_int
      exact (measurable_stoppedValue hAadp.progMeasurable_of_discrete hσ).stronglyMeasurable
    filter_upwards [hmono] with ω hω
    simpa [hmeas] using hω
  have hMA : M + A = X := by
    simpa [M, A] using martingalePart_add_predictablePart ℱ μ X
  have hτ_split : stoppedValue X τ∞ = stoppedValue M τ∞ + stoppedValue A τ∞ := by
    -- Split the stopped value through the Doob decomposition pointwise at the selected index.
    ext ω
    simpa [stoppedValue, Pi.add_apply] using
      (congrFun (congrFun hMA ((τ∞ ω).untopA)) ω).symm
  have hσ_split : stoppedValue X σ∞ = stoppedValue M σ∞ + stoppedValue A σ∞ := by
    -- The same pointwise splitting applies at the earlier stopping time.
    ext ω
    simpa [stoppedValue, Pi.add_apply] using
      (congrFun (congrFun hMA ((σ∞ ω).untopA)) ω).symm
  have hτ_sum_int : Integrable (stoppedValue M τ∞ + stoppedValue A τ∞) μ := hM_stop.1.add hAτ_int
  -- Compare the martingale and predictable parts separately under conditional expectation.
  refine ⟨hτ_sum_int.congr (Filter.EventuallyEq.of_eq hτ_split).symm, ?_⟩
  calc
    μ[stoppedValue X τ∞ | hσ.measurableSpace]
        =ᵐ[μ] μ[stoppedValue M τ∞ | hσ.measurableSpace] +
            μ[stoppedValue A τ∞ | hσ.measurableSpace] := by
          exact (condExp_congr_ae (Filter.EventuallyEq.of_eq hτ_split)).trans
            (condExp_add hM_stop.1 hAτ_int hσ.measurableSpace)
    _ ≤ᵐ[μ] stoppedValue M σ∞ + stoppedValue A σ∞ := by
      filter_upwards [hM_stop.2, hA_stop] with ω hωM hωA
      exact add_le_add (by simp [hωM]) hωA
    _ =ᵐ[μ] stoppedValue X σ∞ := Filter.EventuallyEq.of_eq hσ_split.symm
