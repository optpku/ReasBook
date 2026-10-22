/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Remark_13_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Remark_13_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal Topology

universe u

namespace MeasureTheory
namespace FiniteMeasure

section

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
  [LocallyCompactSpace E] [PolishSpace E]

def vagueMassTendstoClause (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) : Prop :=
  radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
    Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)

theorem vagueMassTendstoClause_iff (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) :
    vagueMassTendstoClause μs μ ↔
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
        Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
  -- Proof comment: this theorem only unfolds the source-facing clause wrapper.
  rfl

def vagueMassLimsupClause (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) : Prop :=
  radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
    limsup (fun n ↦ (μs n : Measure E) Set.univ) atTop ≤ (μ : Measure E) Set.univ

theorem vagueMassLimsupClause_iff (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) :
    vagueMassLimsupClause μs μ ↔
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
        limsup (fun n ↦ (μs n : Measure E) Set.univ) atTop ≤ (μ : Measure E) Set.univ := by
  -- Proof comment: this theorem only unfolds the source-facing clause wrapper.
  rfl

def vagueTightClause (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) : Prop :=
  radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
    IsTightMeasureSet (FiniteMeasure.toMeasure '' Set.range μs)

theorem vagueTightClause_iff (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) :
    vagueTightClause μs μ ↔
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
        IsTightMeasureSet (FiniteMeasure.toMeasure '' Set.range μs) := by
  -- Proof comment: this theorem only unfolds the source-facing clause wrapper.
  rfl

/-- Helper for Theorem 13.35: an eventually bounded `NNReal` sequence admits one global bound on
all indices. -/
lemma exists_globalBound_of_eventually_le {u : ℕ → NNReal} {b : NNReal}
    (h : ∀ᶠ n in atTop, u n ≤ b) :
    ∃ C : NNReal, ∀ n, u n ≤ C := by
  -- Proof comment: patch the eventual tail bound with the finite supremum of the initial segment.
  rw [Filter.eventually_atTop] at h
  rcases h with ⟨N, hN⟩
  let C : NNReal := max b ((Finset.range N).sup u)
  refine ⟨C, fun n ↦ ?_⟩
  by_cases hn : n < N
  · exact le_trans (Finset.le_sup (Finset.mem_range.mpr hn)) (le_max_right _ _)
  · exact le_trans (hN n (Nat.le_of_not_gt hn)) (le_max_left _ _)

/-- Helper for Theorem 13.35: vague convergence together with the one-sided total-mass limsup
control already forces total-mass convergence. -/
lemma vagueMassTendstoClause_of_vagueMassLimsupClause
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h : vagueMassLimsupClause μs μ) :
    vagueMassTendstoClause μs μ := by
  rcases h with ⟨hvague, hUpper⟩
  have hEventuallyMass :
      ∀ᶠ n in atTop, (μs n : Measure E) Set.univ < (μ : Measure E) Set.univ + 1 := by
    -- Proof comment: the limsup bound gives an eventual finite upper control on the total masses.
    refine Filter.eventually_lt_of_limsup_lt ?_
    exact lt_of_le_of_lt hUpper <|
      ENNReal.lt_add_right (measure_ne_top (μ : Measure E) Set.univ) one_ne_zero
  have hEventuallyMassNN :
      ∀ᶠ n in atTop, (μs n).mass ≤ μ.mass + 1 := by
    -- Proof comment: rewrite the eventual `Measure`-level bound through the finite-measure mass
    -- API before extracting one global `NNReal` bound.
    filter_upwards [hEventuallyMass] with n hn
    exact ENNReal.coe_le_coe.mp (by simpa [FiniteMeasure.ennreal_mass] using hn.le)
  obtain ⟨C, hC⟩ :=
    exists_globalBound_of_eventually_le (u := fun n ↦ (μs n).mass) (b := μ.mass + 1)
      hEventuallyMassNN
  have hBound : atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ (μs n).mass) :=
    Filter.isBoundedUnder_of ⟨C, hC⟩
  have hLowerENNReal :
      (μ : Measure E) Set.univ ≤ liminf (fun n ↦ (μs n : Measure E) Set.univ) atTop :=
    measure_univ_le_liminf_of_vaguely_converges hvague
  have hLower :
      μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop := by
    have hAux :
        ENNReal.ofNNReal (liminf (fun n ↦ (μs n).mass) atTop) =
          liminf (ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass) atTop := by
      -- Proof comment: the global mass bound lets `ENNReal.ofNNReal` commute with the liminf.
      simpa [Function.comp_apply] using
        Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono
          (fun n ↦ (μs n).mass) ENNReal.continuous_coe.continuousAt
          (isCoboundedUnder_ge_of_le atTop hC) ⟨0, by simp⟩
    have hMassFun :
        (fun n ↦ (μs n : Measure E) Set.univ) =
          ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass := by
      funext n
      simp [FiniteMeasure.ennreal_mass, Function.comp_apply]
    have hLower' :
        ENNReal.ofNNReal μ.mass ≤
          liminf (ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass) atTop := by
      simpa [hMassFun, Function.comp_apply] using hLowerENNReal
    have hLower'' :
        ENNReal.ofNNReal μ.mass ≤
          ENNReal.ofNNReal (liminf (fun n ↦ (μs n).mass) atTop) := by
      simpa [hAux] using hLower'
    exact ENNReal.coe_le_coe.mp hLower''
  have hUpperNN :
      limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass := by
    have hAux :
        ENNReal.ofNNReal (limsup (fun n ↦ (μs n).mass) atTop) =
          limsup (ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass) atTop := by
      -- Proof comment: the same global bound transports the limsup comparison back to `NNReal`.
      simpa [Function.comp_apply] using
        Monotone.map_limsup_of_continuousAt (F := atTop) ENNReal.coe_mono
          (fun n ↦ (μs n).mass) ENNReal.continuous_coe.continuousAt hBound ⟨0, by simp⟩
    have hMassFun :
        (fun n ↦ (μs n : Measure E) Set.univ) =
          ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass := by
      funext n
      simp [FiniteMeasure.ennreal_mass, Function.comp_apply]
    have hUpper' :
        ENNReal.ofNNReal (limsup (fun n ↦ (μs n).mass) atTop) ≤ ENNReal.ofNNReal μ.mass := by
      have hUpper'' :
          limsup (ENNReal.ofNNReal ∘ fun n ↦ (μs n).mass) atTop ≤ ENNReal.ofNNReal μ.mass := by
        simpa [hMassFun, Function.comp_apply] using hUpper
      simpa [hAux] using hUpper''
    exact ENNReal.coe_le_coe.mp hUpper'
  -- Proof comment: squeeze the total masses between the liminf lower bound from vague
  -- convergence and the assumed limsup upper bound.
  exact ⟨hvague, massTendstoOfLiminfLimsup hBound hLower hUpperNN⟩

/-- Helper for Theorem 13.35: a compactly supported cutoff controls the real complement mass
between the large set where it vanishes and the smaller set where it is identically `1`. -/
lemma compactCutoffEscapeBounds
    {ν : FiniteMeasure E} {L K : Set E} {g : C_c(E, ℝ)}
    (hL_meas : MeasurableSet L) (hK_meas : MeasurableSet K)
    (hg_nonneg : ∀ x, 0 ≤ g x) (hg_le_one : ∀ x, g x ≤ 1)
    (hL_one : ∀ x ∈ L, g x = 1) (hK_zero : ∀ x ∉ K, g x = 0) :
    ((ν : Measure E).real Kᶜ) ≤ (ν.mass : ℝ) - ∫ x, g x ∂(ν : Measure E) ∧
      (ν.mass : ℝ) - ∫ x, g x ∂(ν : Measure E) ≤ ((ν : Measure E).real Lᶜ) := by
  have hg_int : Integrable g (ν : Measure E) :=
    g.1.continuous.integrable_of_hasCompactSupport g.2
  have hOneSub_int : Integrable (fun x : E ↦ 1 - g x) (ν : Measure E) :=
    (integrable_const (1 : ℝ)).sub hg_int
  have hDiff :
      (ν.mass : ℝ) - ∫ x, g x ∂(ν : Measure E) =
        ∫ x, (1 - g x) ∂(ν : Measure E) := by
    -- Proof comment: rewrite the lost mass against the cutoff as the integral of `1 - g`.
    calc
      (ν.mass : ℝ) - ∫ x, g x ∂(ν : Measure E)
          = ((ν : Measure E).real Set.univ) - ∫ x, g x ∂(ν : Measure E) := by
              simp [FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass]
      _ = ∫ x, (1 - g x) ∂(ν : Measure E) := by
            rw [integral_sub (integrable_const (1 : ℝ)) hg_int, integral_const]
            simp [smul_eq_mul]
  have hKc_int :
      Integrable (Kᶜ.indicator fun _ : E ↦ (1 : ℝ)) (ν : Measure E) := by
    exact (integrable_indicator_iff hK_meas.compl).2 (integrable_const (1 : ℝ)).integrableOn
  have hLc_int :
      Integrable (Lᶜ.indicator fun _ : E ↦ (1 : ℝ)) (ν : Measure E) := by
    exact (integrable_indicator_iff hL_meas.compl).2 (integrable_const (1 : ℝ)).integrableOn
  have hLower_int :
      ∫ x, Kᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x ∂(ν : Measure E) ≤
        ∫ x, (1 - g x) ∂(ν : Measure E) := by
    -- Proof comment: outside `K`, the cutoff vanishes, so `1 - g` dominates `1_{Kᶜ}`.
    refine integral_mono hKc_int hOneSub_int ?_
    intro x
    by_cases hx : x ∈ Kᶜ
    · have hg0 : g x = 0 := hK_zero x hx
      simp [hx, hg0]
    · have hnonneg : 0 ≤ 1 - g x := sub_nonneg.mpr (hg_le_one x)
      simp [hx, hnonneg]
  have hUpper_int :
      ∫ x, (1 - g x) ∂(ν : Measure E) ≤
        ∫ x, Lᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x ∂(ν : Measure E) := by
    -- Proof comment: on `L`, the cutoff is already `1`, so `1 - g` is supported inside `Lᶜ`.
    refine integral_mono hOneSub_int hLc_int ?_
    intro x
    by_cases hx : x ∈ L
    · have hg1 : g x = 1 := hL_one x hx
      simp [hx, hg1]
    · have hle : 1 - g x ≤ 1 := by
        linarith [hg_nonneg x]
      simp [hx, hle]
  constructor
  · -- Proof comment: identify the lower comparison with the real mass of `Kᶜ`.
    rw [hDiff]
    rw [(integral_indicator_one hK_meas.compl).symm]
    exact hLower_int
  · -- Proof comment: identify the upper comparison with the real mass of `Lᶜ`.
    rw [hDiff]
    rw [(integral_indicator_one hL_meas.compl).symm]
    exact hUpper_int

/-- Helper for Theorem 13.35: vague convergence is preserved by `NNReal` scaling of finite
measures. -/
lemma radonMeasureVaguelyConvergesTo_nnnreal_smul
    (c : NNReal) {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E)) :
    radonMeasureVaguelyConvergesTo
      (fun n ↦ ((c • μs n : FiniteMeasure E) : Measure E))
      ((c • μ : FiniteMeasure E) : Measure E) := by
  rw [radonMeasureVaguelyConvergesTo_iff] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · have hμRadon : IsRadonMeasure (μ : Measure E) := h.1
    rw [IsRadonMeasure] at hμRadon ⊢
    letI : (μ : Measure E).InnerRegular := hμRadon.2.1
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro n
    have hμnRadon : IsRadonMeasure (μs n : Measure E) := h.2.1 n
    rw [IsRadonMeasure] at hμnRadon ⊢
    letI : (μs n : Measure E).InnerRegular := hμnRadon.2.1
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  intro f
  -- Proof comment: every compactly supported test integral scales by the same fixed scalar.
  have hScaled :
      Tendsto (fun n ↦ (c : ℝ) * ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 ((c : ℝ) * ∫ x, f x ∂(μ : Measure E))) := by
    exact tendsto_const_nhds.mul (h.2.2 f)
  simpa [FiniteMeasure.toMeasure_smul, integral_smul_measure, mul_comm, mul_left_comm,
    mul_assoc] using hScaled

/-- Helper for Theorem 13.35: vague convergence together with convergence of the total masses
implies tightness of the sequence. -/
lemma vagueTightClause_of_vagueMassTendstoClause
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h : vagueMassTendstoClause μs μ) :
    vagueTightClause μs μ := by
  rcases h with ⟨hVague, hMass⟩
  refine ⟨hVague, ?_⟩
  rw [FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt]
  intro ε hε
  have hε_half : 0 < ε / 2 := by positivity
  have hμtight : IsTightMeasureSet ({(μ : Measure E)} : Set (Measure E)) :=
    isTightMeasureSet_singleton
  obtain ⟨L, hLcompact, hLsmall⟩ :=
    (MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμtight)
      (ENNReal.ofReal (ε / 2)) (by positivity)
  have hμLsmall :
      (μ : Measure E) Lᶜ ≤ ENNReal.ofReal (ε / 2) := hLsmall _ (by simp)
  obtain ⟨V, hVOpen, hLV, -, hVClosureCompact⟩ :=
    exists_open_between_and_isCompact_closure hLcompact isOpen_univ (subset_univ L)
  obtain ⟨δ, hδ, hThick⟩ := hLcompact.exists_thickening_subset_open hVOpen hLV
  obtain ⟨g, hg_eq⟩ :=
    compactlySupportedThickenedIndicator (K := L) (V := V) hδ hThick hVClosureCompact
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    rw [hg_eq]
    exact_mod_cast (show (0 : NNReal) ≤ thickenedIndicator hδ L x from bot_le)
  have hg_le_one : ∀ x, g x ≤ 1 := by
    intro x
    rw [hg_eq]
    exact_mod_cast (thickenedIndicator_le_one hδ L x)
  have hg_one : ∀ x ∈ L, g x = 1 := by
    intro x hx
    rw [hg_eq]
    exact congrArg (fun t : NNReal ↦ (t : ℝ)) (thickenedIndicator_one hδ L hx)
  have hg_zero : ∀ x ∉ closure V, g x = 0 := by
    intro x hx
    rw [hg_eq]
    have hx_not_V : x ∉ V := fun hxV ↦ hx (subset_closure hxV)
    have hx_not_thick : x ∉ Metric.thickening δ L := by
      intro hx_thick
      exact hx_not_V (hThick hx_thick)
    exact congrArg (fun t : NNReal ↦ (t : ℝ)) (thickenedIndicator_zero hδ L hx_not_thick)
  have hEscapeUpperμ :
      (μ.mass : ℝ) - ∫ x, g x ∂(μ : Measure E) ≤ ((μ : Measure E).real Lᶜ) :=
    (compactCutoffEscapeBounds (ν := μ) (L := L) (K := closure V)
      hLcompact.measurableSet hVClosureCompact.measurableSet
      hg_nonneg hg_le_one hg_one hg_zero).2
  have hμLsmall_real : ((μ : Measure E).real Lᶜ) ≤ ε / 2 := by
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hμLsmall
  have hLimit_lt :
      (μ.mass : ℝ) - ∫ x, g x ∂(μ : Measure E) < ε := by
    linarith
  have hIntTendsto :
      Tendsto (fun n ↦ ∫ x, g x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
    rw [radonMeasureVaguelyConvergesTo_iff] at hVague
    exact hVague.2.2 g
  have hDiffTendsto :
      Tendsto (fun n ↦ (μs n).mass - ∫ x, g x ∂(μs n : Measure E)) atTop
        (𝓝 ((μ.mass : ℝ) - ∫ x, g x ∂(μ : Measure E))) := by
    -- Proof comment: combine mass convergence and vague convergence of the single cutoff test.
    exact ((NNReal.tendsto_coe.2 hMass).sub hIntTendsto)
  have hTail :
      ∀ᶠ n in atTop, ((μs n : Measure E).real (closure V)ᶜ) < ε := by
    filter_upwards [hDiffTendsto (Iio_mem_nhds hLimit_lt)] with n hn
    exact lt_of_le_of_lt
      (compactCutoffEscapeBounds (ν := μs n) (L := L) (K := closure V)
        hLcompact.measurableSet hVClosureCompact.measurableSet
        hg_nonneg hg_le_one hg_one hg_zero).1
      hn
  rw [Filter.eventually_atTop] at hTail
  rcases hTail with ⟨N, hTail⟩
  let S : Set (FiniteMeasure E) := Set.range fun m : Fin N ↦ μs m
  have hSfinite : S.Finite := Set.finite_range _
  have hPrefixTight :
      IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' S) :=
    isTightMeasureSet_of_finite_finiteMeasureFamily hSfinite
  obtain ⟨K₀, hK₀compact, hK₀bound⟩ :=
    (FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt S).1
      hPrefixTight ε hε
  refine ⟨K₀ ∪ closure V, hK₀compact.union hVClosureCompact, ?_⟩
  intro ν hν
  rcases hν with ⟨n, rfl⟩
  by_cases hn : n < N
  · have hmemS : μs n ∈ S := ⟨⟨n, hn⟩, rfl⟩
    exact lt_of_le_of_lt
      (measure_mono (compl_subset_compl.mpr (subset_union_left : K₀ ⊆ K₀ ∪ closure V)))
      (hK₀bound _ hmemS)
  · have hTailENN : (μs n : Measure E) (closure V)ᶜ < ENNReal.ofReal ε := by
      let εnn : NNReal := ⟨ε, hε.le⟩
      have hTailReal : (((μs n) (closure V)ᶜ : NNReal) : ℝ) < ε := by
        simpa [FiniteMeasure.measureReal_eq_coe_coeFn] using hTail n (Nat.le_of_not_gt hn)
      have hTailNN : ((μs n) (closure V)ᶜ : NNReal) < εnn := by
        exact NNReal.coe_lt_coe.mp (by simpa [εnn] using hTailReal)
      have hTailENN' : (((μs n) (closure V)ᶜ : NNReal) : ℝ≥0∞) < (εnn : ℝ≥0∞) := by
        exact_mod_cast hTailNN
      simpa [εnn, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ENNReal.ofReal_eq_coe_nnreal hε.le] using hTailENN'
    exact lt_of_le_of_lt
      (measure_mono (compl_subset_compl.mpr (subset_union_right : closure V ⊆ K₀ ∪ closure V)))
      hTailENN

/-- Helper for Theorem 13.35: tightness together with vague convergence yields one common bound on
all total masses. -/
lemma exists_uniformMassBound_of_vagueTightClause
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h : vagueTightClause μs μ) :
    ∃ C : NNReal, 1 ≤ C ∧ μ.mass ≤ C ∧ ∀ n, (μs n).mass ≤ C := by
  rcases h with ⟨hVague, hTight⟩
  obtain ⟨K, hKcompact, hKsmall⟩ :=
    (FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt
      (Set.range μs)).1 hTight 1 zero_lt_one
  obtain ⟨V, hVOpen, hKV, -, hVClosureCompact⟩ :=
    exists_open_between_and_isCompact_closure hKcompact isOpen_univ (subset_univ K)
  obtain ⟨δ, hδ, hThick⟩ := hKcompact.exists_thickening_subset_open hVOpen hKV
  obtain ⟨g, hg_eq⟩ :=
    compactlySupportedThickenedIndicator (K := K) (V := V) hδ hThick hVClosureCompact
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    rw [hg_eq]
    exact_mod_cast (show (0 : NNReal) ≤ thickenedIndicator hδ K x from bot_le)
  have hg_le_one : ∀ x, g x ≤ 1 := by
    intro x
    rw [hg_eq]
    exact_mod_cast (thickenedIndicator_le_one hδ K x)
  have hg_one : ∀ x ∈ K, g x = 1 := by
    intro x hx
    rw [hg_eq]
    exact congrArg (fun t : NNReal ↦ (t : ℝ)) (thickenedIndicator_one hδ K hx)
  have hg_zero : ∀ x ∉ closure V, g x = 0 := by
    intro x hx
    rw [hg_eq]
    have hx_not_V : x ∉ V := fun hxV ↦ hx (subset_closure hxV)
    have hx_not_thick : x ∉ Metric.thickening δ K := by
      intro hx_thick
      exact hx_not_V (hThick hx_thick)
    exact congrArg (fun t : NNReal ↦ (t : ℝ)) (thickenedIndicator_zero hδ K hx_not_thick)
  have hIntTendsto :
      Tendsto (fun n ↦ ∫ x, g x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, g x ∂(μ : Measure E))) := by
    rw [radonMeasureVaguelyConvergesTo_iff] at hVague
    exact hVague.2.2 g
  have hIntegralNonneg :
      0 ≤ ∫ x, g x ∂(μ : Measure E) := by
    refine integral_nonneg ?_
    intro x
    exact hg_nonneg x
  have hMassEventually :
      ∀ᶠ n in atTop, (μs n).mass ≤ Real.toNNReal (∫ x, g x ∂(μ : Measure E) + 2) := by
    have hIntEventually :
        ∀ᶠ n in atTop, ∫ x, g x ∂(μs n : Measure E) <
          ∫ x, g x ∂(μ : Measure E) + 1 := by
      exact hIntTendsto (Iio_mem_nhds (by linarith))
    filter_upwards [hIntEventually] with n hn
    have hEscapeReal :
        ((μs n : Measure E).real Kᶜ) < 1 := by
      have hKsmall' : (μs n : Measure E) Kᶜ < ENNReal.ofReal 1 := by
        simpa using hKsmall (μs n) ⟨n, rfl⟩
      rw [FiniteMeasure.measureReal_eq_coe_coeFn]
      exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top (μs n : Measure E) Kᶜ)).1 hKsmall'
    have hMassReal :
        ((μs n).mass : ℝ) <
          ∫ x, g x ∂(μ : Measure E) + 2 := by
      have hEscapeUpper :
          ((μs n).mass : ℝ) - ∫ x, g x ∂(μs n : Measure E) ≤
            ((μs n : Measure E).real Kᶜ) :=
        (compactCutoffEscapeBounds (ν := μs n) (L := K) (K := closure V)
          hKcompact.measurableSet hVClosureCompact.measurableSet
          hg_nonneg hg_le_one hg_one hg_zero).2
      linarith
    have hBoundNonneg : 0 ≤ ∫ x, g x ∂(μ : Measure E) + 2 := by
      linarith
    have hBoundReal :
        ((μs n).mass : ℝ) ≤ (Real.toNNReal (∫ x, g x ∂(μ : Measure E) + 2) : ℝ) := by
      simpa [Real.toNNReal_of_nonneg hBoundNonneg] using hMassReal.le
    exact NNReal.coe_le_coe.mp hBoundReal
  obtain ⟨C₀, hC₀⟩ :=
    exists_globalBound_of_eventually_le
      (u := fun n ↦ (μs n).mass)
      (b := Real.toNNReal (∫ x, g x ∂(μ : Measure E) + 2))
      hMassEventually
  let C : NNReal := max 1 (max μ.mass C₀)
  refine ⟨C, le_max_left _ _, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro n
    exact le_trans (hC₀ n) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Helper for Theorem 13.35: vague convergence and tightness imply weak convergence once one
common mass bound is fixed. -/
lemma tendsto_of_vagueTight_of_uniformMassBound
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (hVague : radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E))
    (hTight : IsTightMeasureSet (FiniteMeasure.toMeasure '' Set.range μs))
    {C : NNReal} (hC_ge_one : 1 ≤ C) (hμ_le_C : μ.mass ≤ C) (hμs_le_C : ∀ n, (μs n).mass ≤ C) :
    Tendsto μs atTop (𝓝 μ) := by
  let νs : ℕ → FiniteMeasure E := fun n ↦ C⁻¹ • μs n
  let ν : FiniteMeasure E := C⁻¹ • μ
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_one
  have hC_ne_zero : C ≠ 0 := ne_of_gt hC_pos
  have hCinv_le_one : ((C⁻¹ : NNReal) : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (inv_le_one_of_one_le₀ hC_ge_one : C⁻¹ ≤ (1 : NNReal))
  have hScaledMass_le_one :
      ∀ {η : FiniteMeasure E}, η.mass ≤ C → (C⁻¹ • η).mass ≤ 1 := by
    intro η hη
    apply ENNReal.coe_le_coe.mp
    calc
      (((C⁻¹ • η).mass : NNReal) : ℝ≥0∞)
          = ((C⁻¹ : NNReal) : ℝ≥0∞) * (η.mass : ℝ≥0∞) := by
              simp [FiniteMeasure.ennreal_mass, Measure.smul_apply]
      _ ≤ ((C⁻¹ : NNReal) : ℝ≥0∞) * C := by
            exact_mod_cast mul_le_mul_left' hη (C⁻¹ : NNReal)
      _ = (((C : ℝ≥0∞))⁻¹ * (C : ℝ≥0∞)) := by
            rw [ENNReal.coe_inv hC_ne_zero]
      _ = 1 := by
            exact ENNReal.inv_mul_cancel
              (by simpa using hC_ne_zero)
              (by simp : ((C : ℝ≥0∞)) ≠ ∞)
  have hν_mass : ν.mass ≤ 1 := by
    simpa [ν] using hScaledMass_le_one hμ_le_C
  have hνs_mass : ∀ n, (νs n).mass ≤ 1 := by
    intro n
    simpa [νs] using hScaledMass_le_one (hμs_le_C n)
  have hνTight :
      IsTightMeasureSet (FiniteMeasure.toMeasure '' Set.range νs) := by
    rw [FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt]
    intro ε hε
    obtain ⟨K, hKcompact, hKbound⟩ :=
      (FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt
        (Set.range μs)).1 hTight ε hε
    refine ⟨K, hKcompact, ?_⟩
    intro η hη
    rcases hη with ⟨n, rfl⟩
    calc
      ((νs n : FiniteMeasure E) : Measure E) Kᶜ
          = ((C⁻¹ : NNReal) : ℝ≥0∞) * (μs n : Measure E) Kᶜ := by
              simp [νs, FiniteMeasure.toMeasure_smul, Measure.smul_apply]
      _ ≤ 1 * (μs n : Measure E) Kᶜ := by gcongr
      _ = (μs n : Measure E) Kᶜ := by simp
      _ < ENNReal.ofReal ε := hKbound _ ⟨n, rfl⟩
  have hνVague :
      radonMeasureVaguelyConvergesTo (fun n ↦ (νs n : Measure E)) (ν : Measure E) := by
    simpa [νs, ν] using
      radonMeasureVaguelyConvergesTo_nnnreal_smul C⁻¹ hVague
  have hνTendsto : Tendsto νs atTop (𝓝 ν) := by
    refine Filter.tendsto_of_subseq_tendsto ?_
    intro ns hns
    obtain ⟨νlim, φ, hφ, hWeakSubseq⟩ :=
      isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet
        (Set.range νs) (by
          intro η hη
          rcases hη with ⟨n, rfl⟩
          exact hνs_mass n)
        hνTight (νs ∘ ns) (by
          intro n
          exact ⟨ns n, rfl⟩)
    have hWeakVague :
        radonMeasureVaguelyConvergesTo
          (fun n ↦ ((νs (ns (φ n)) : FiniteMeasure E) : Measure E))
          (νlim : Measure E) :=
      (weakImpliesVagueAndMass (μs := νs ∘ ns ∘ φ) (μ := νlim) hWeakSubseq).1
    have hTargetVague :
        radonMeasureVaguelyConvergesTo
          (fun n ↦ ((νs (ns (φ n)) : FiniteMeasure E) : Measure E))
          (ν : Measure E) := by
      rw [radonMeasureVaguelyConvergesTo_iff] at hνVague ⊢
      refine ⟨hνVague.1, fun n ↦ hνVague.2.1 _, fun f ↦ ?_⟩
      exact (hνVague.2.2 f).comp (hns.comp hφ.tendsto_atTop)
    have hνlim_eq_ν_measure : (νlim : Measure E) = (ν : Measure E) :=
      vague_limit_unique_of_locallyCompact hWeakVague hTargetVague
    have hνlim_eq_ν : νlim = ν := FiniteMeasure.toMeasure_injective hνlim_eq_ν_measure
    refine ⟨φ, ?_⟩
    simpa [Function.comp, hνlim_eq_ν] using hWeakSubseq
  have hScaleCont : Continuous fun η : FiniteMeasure E ↦ C • η :=
    continuous_const.smul continuous_id
  have hRecover :
      Tendsto (fun n ↦ C • νs n) atTop (𝓝 (C • ν)) := by
    exact (hScaleCont.tendsto _).comp hνTendsto
  have hRecoverSeq : (fun n ↦ C • νs n) = μs := by
    funext n
    dsimp [νs]
    rw [smul_smul, mul_inv_cancel₀ hC_ne_zero, one_smul]
  have hRecoverLim : C • ν = μ := by
    dsimp [ν]
    rw [smul_smul, mul_inv_cancel₀ hC_ne_zero, one_smul]
  simpa [hRecoverSeq, hRecoverLim] using hRecover

-- Proof sketch: first identify the three mass clauses using the locally compact Portmanteau
-- machinery from Theorem 13.16. Then prove tightness from vague convergence plus mass convergence
-- by one compact cutoff argument, and recover weak convergence from vague convergence plus
-- tightness by scaling to a subprobability family and applying Theorem 13.29.
-- Semantic recall: `limsup` on `NNReal` or `ℝ` collapses unbounded sequences to `0`, so the
-- source-facing one-sided mass control clause is stated on total masses in `ℝ≥0∞`.
/-- Theorem 13.35: for finite measures on a locally compact Polish space, weak convergence is
equivalent to vague convergence together with either convergence of total masses, one-sided limsup
mass control of the total masses, or tightness of the sequence. -/
theorem weak_vague_mass_tight_tfae (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) :
    List.TFAE
      [ Tendsto μs atTop (𝓝 μ)
      , vagueMassTendstoClause μs μ
      , vagueMassLimsupClause μs μ
      , vagueTightClause μs μ
      ] := by
  -- Proof comment: the weak, vague-plus-mass, and vague-plus-limsup clauses form the standard
  -- Portmanteau cycle, while the tightness clause is handled by the two dedicated helpers above.
  tfae_have 1 → 2 := by
    exact weakImpliesVagueAndMass (μs := μs) (μ := μ)
  tfae_have 2 → 3 := by
    intro h
    exact ⟨h.1, by simpa [FiniteMeasure.ennreal_mass] using ((ENNReal.tendsto_coe).2 h.2).limsup_eq.le⟩
  tfae_have 3 → 2 := by
    exact vagueMassTendstoClause_of_vagueMassLimsupClause μs μ
  tfae_have 2 → 4 := by
    exact vagueTightClause_of_vagueMassTendstoClause μs μ
  tfae_have 4 → 1 := by
    intro h
    obtain ⟨C, hC_ge_one, hμ_le_C, hμs_le_C⟩ :=
      exists_uniformMassBound_of_vagueTightClause μs μ h
    exact tendsto_of_vagueTight_of_uniformMassBound μs μ h.1 h.2 hC_ge_one hμ_le_C hμs_le_C
  tfae_finish

end

end FiniteMeasure
end MeasureTheory
