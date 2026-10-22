/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Corollary_6_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Filter MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {p : ℝ}

/- Theorem 11.10 is `source-facing`: it concerns a discrete martingale and its canonical terminal
limit random variable `ℱ.limitProcess X μ`. Its `core/canonical` owner layers are the existing
martingale API around `Filtration.limitProcess`, `Submartingale.memLp_limitProcess`, and
`Submartingale.ae_tendsto_limitProcess`, together with the Chapter 7 convergence owner
`TendstoInLp`. Its local `bridge/view` statements are the passage from the textbook `L^p` bound
`∃ C, ∀ n, eLpNorm (X n) p μ ≤ C` to the owner `L¹` boundedness input, and the raw `eLpNorm`
convergence reformulation of `TendstoInLp`; the theorems below keep the source statement public
and derive the shorter owner-level companions from it. -/

section

variable [IsProbabilityMeasure μ]

private theorem submartingale_eLpNorm_one_bounded_of_lp_bounded
    (hf : Submartingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    ∃ R : ℝ≥0, ∀ n, eLpNorm (X n) 1 μ ≤ R := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨C, fun n ↦ ?_⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hcompare :
      eLpNorm (X n) 1 μ ≤ eLpNorm (X n) (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) := by
    simpa [hp0.ne', ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le, one_div] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_p
        (((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) :
          eLpNorm (X n) 1 μ ≤
            eLpNorm (X n) (ENNReal.ofReal p) μ *
              μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal))
  calc
    eLpNorm (X n) 1 μ
        ≤ eLpNorm (X n) (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) := hcompare
    _ = eLpNorm (X n) (ENNReal.ofReal p) μ := by simp
    _ ≤ C := hC n

private theorem fact_one_le_ofReal_of_one_lt (hp : 1 < p) :
    Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩

/-- Helper for Theorem 11.10: the function `x ↦ |x| ^ q` is convex on `ℝ` for every exponent
`q ≥ 1`. -/
private theorem absRpowConvexOnUniv {q : ℝ} (hq : 1 ≤ q) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ q) := by
  -- Proof comment: compose the convex absolute value with the convex power map on `[0, ∞)`.
  have hrange_abs : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact abs_nonneg y
    · intro hx
      exact ⟨x, Set.mem_univ x, abs_of_nonneg hx⟩
  have hrpow : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) (fun x : ℝ ↦ x ^ q) := by
    simpa [hrange_abs] using (convexOn_rpow hq)
  have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
    simpa [Real.norm_eq_abs] using
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
  simpa using hrpow.comp habs
    (by
      simpa [hrange_abs] using
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans zero_le_one hq)))

/-- Helper for Theorem 11.10: an `L^p`-bounded martingale family with `p > 1` is uniformly
integrable in `L¹`. -/
private theorem martingale_uniformIntegrable_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    UniformIntegrable X 1 μ := by
  letI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  rcases hbounded with ⟨C, hC⟩
  let F : Set (Lp ℝ (ENNReal.ofReal p) μ) :=
    Set.range fun n ↦ ((show MemLp (X n) (ENNReal.ofReal p) μ from
      ⟨((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable,
        lt_of_le_of_lt (hC n) ENNReal.coe_lt_top⟩).toLp (X n))
  have hX_memLp : ∀ n, MemLp (X n) (ENNReal.ofReal p) μ := by
    intro n
    exact ⟨((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable,
      lt_of_le_of_lt (hC n) ENNReal.coe_lt_top⟩
  have hF_bdd : Bornology.IsBounded F := by
    -- Proof comment: the `L^p` bounds turn into a uniform norm bound on the image set in `Lp`.
    refine isBounded_iff_forall_norm_le.2 ⟨(C : ℝ), ?_⟩
    intro f hfF
    rcases hfF with ⟨n, rfl⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top (hC n)
  have hUI_F : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ :=
    uniformIntegrable_of_bounded_memLp_of_one_lt (μ := μ) (p := p) hp hF_bdd
  let Xsub : ℕ → F := fun n ↦ ⟨(hX_memLp n).toLp (X n), ⟨n, rfl⟩⟩
  have hUI_X : UniformIntegrable (fun n ↦ ((Xsub n : F) : Ω → ℝ)) 1 μ := by
    refine ⟨fun n ↦ hUI_F.1 (Xsub n), ?_, ?_⟩
    · -- Proof comment: reindex the uniform-integrability estimate from the bounded `Lp` set.
      intro ε hε
      obtain ⟨δ, hδ, hδ_bound⟩ := hUI_F.2.1 hε
      exact ⟨δ, hδ, fun n s hs hμs ↦ hδ_bound (Xsub n) s hs hμs⟩
    · obtain ⟨B, hB⟩ := hUI_F.2.2
      exact ⟨B, fun n ↦ hB (Xsub n)⟩
  -- Proof comment: the `Lp` representatives coincide almost everywhere with the original process.
  refine hUI_X.ae_eq ?_
  intro n
  simpa [Xsub] using MemLp.coeFn_toLp (hX_memLp n)

/-- Helper for Theorem 11.10: scalar multiplication preserves uniform integrability at exponent
`1`. -/
private theorem uniformIntegrableSmul
    {ι : Type*} (c : ℝ) {f : ι → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) :
    UniformIntegrable (c • f) 1 μ := by
  refine ⟨fun i ↦ (hf.aestronglyMeasurable i).const_smul c, ?_, ?_⟩
  · by_cases hc : c = 0
    · -- Proof comment: the zero scalar collapses the family to the constant zero family.
      subst hc
      simpa using
        (uniformIntegrable_const (μ := μ) (ι := ι) (p := (1 : ℝ≥0∞)) le_rfl (by simp)
          (MemLp.zero : MemLp (0 : Ω → ℝ) 1 μ)).unifIntegrable
    · -- Proof comment: otherwise rescale the quantitative uniform-integrability estimate by `‖c‖`.
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ :=
        hf.unifIntegrable (ε := ε / ‖c‖) (div_pos hε (norm_pos_iff.2 hc))
      refine ⟨δ, hδpos, fun i s hs hμs ↦ ?_⟩
      have hsIndicator :
          s.indicator ((c • f) i) = c • s.indicator (f i) := by
        funext x
        by_cases hx : x ∈ s
        · simp [hx, Pi.smul_apply]
        · simp [hx, Pi.smul_apply]
      have hmul : ‖c‖ * (ε / ‖c‖) = ε := by
        field_simp [hc]
      calc
        eLpNorm (s.indicator ((c • f) i)) 1 μ
            = eLpNorm (c • s.indicator (f i)) 1 μ := by
                rw [hsIndicator]
        _ = ‖c‖ₑ * eLpNorm (s.indicator (f i)) 1 μ := by
              rw [eLpNorm_const_smul]
        _ ≤ ‖c‖ₑ * ENNReal.ofReal (ε / ‖c‖) := by
              simpa [mul_comm] using mul_le_mul_left (hδ i s hs hμs) ‖c‖ₑ
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul]
              · rw [hmul]
              · exact norm_nonneg _
  · -- Proof comment: the uniform `L¹` bound also rescales linearly.
    rcases hf.2.2 with ⟨C, hC⟩
    refine ⟨‖c‖₊ * C, fun i ↦ ?_⟩
    calc
      eLpNorm ((c • f) i) 1 μ = ‖c‖ₑ * eLpNorm (f i) 1 μ := by
        rw [Pi.smul_apply, eLpNorm_const_smul]
      _ ≤ ‖c‖ₑ * C := by
        simpa [mul_comm] using mul_le_mul_left (hC i) ‖c‖ₑ
      _ = ↑(‖c‖₊ * C) := by
        rw [enorm_eq_nnnorm]
        rfl

/-- Helper for Theorem 11.10: a family dominated almost everywhere by a uniformly integrable
family is uniformly integrable. -/
private theorem uniformIntegrable_of_abs_ae_le_of_uniformIntegrable
    {ι : Type*} {f g : ι → Ω → ℝ}
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hg : UniformIntegrable g 1 μ)
    (hdom : ∀ i, ∀ᵐ ω ∂μ, |f i ω| ≤ g i ω) :
    UniformIntegrable f 1 μ := by
  refine ⟨hf_meas, ?_, ?_⟩
  · -- Proof comment: each truncation of `f` is controlled by the matching truncation of `g`.
    intro ε hε
    obtain ⟨δ, hδ, hδ_bound⟩ := hg.2.1 hε
    refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
    refine (eLpNorm_mono_ae_real ?_).trans (hδ_bound i s hs hμs)
    filter_upwards [hdom i] with ω hω
    by_cases hmem : ω ∈ s
    · simpa [Set.indicator_of_mem, hmem] using hω
    · simp [Set.indicator_of_notMem, hmem]
  · obtain ⟨C, hC⟩ := hg.2.2
    refine ⟨C, fun i ↦ ?_⟩
    exact (eLpNorm_mono_ae_real (hdom i)).trans (hC i)

/-- Helper for Theorem 11.10: conditional Jensen bounds `|𝔼[Y | m]| ^ p` by the conditional
expectation of `|Y| ^ p` when `p ≥ 1`. -/
private theorem absRpow_condExp_le_ae
    {Y : Ω → ℝ} {m : MeasurableSpace Ω}
    (hY : MemLp Y (ENNReal.ofReal p) μ) (hm : m ≤ m0) (hp_one : 1 ≤ p) :
    ∀ᵐ ω ∂μ, |μ[Y | m] ω| ^ p ≤ μ[fun ω ↦ |Y ω| ^ p | m] ω := by
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp_one
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    exact by
      have hp0 : 0 < p := by linarith
      simp [ENNReal.ofReal_eq_zero, not_le_of_gt hp0]
  have hY_int : Integrable Y μ :=
    memLp_one_iff_integrable.1 <| hY.mono_exponent h1_le_p
  have hY_rpow_int : Integrable (fun ω ↦ |Y ω| ^ p) μ := by
    have hp0 : 0 < p := by linarith
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      hY.integrable_norm_rpow hp_zero ENNReal.ofReal_ne_top
  -- Proof comment: apply conditional Jensen to the convex function `x ↦ |x| ^ p`.
  simpa [Function.comp_apply, Real.norm_eq_abs] using
    (absRpowConvexOnUniv hp_one).map_condExp_le_of_finiteDimensional hm hY_int hY_rpow_int

/-- Helper for Theorem 11.10: the powered error family `|X n - ℱ.limitProcess X μ| ^ p` is
uniformly integrable at exponent `1` under the textbook `L^p` boundedness hypothesis. -/
private theorem uniformIntegrableAbsSubLimitProcessRpowOfLpBounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    UniformIntegrable (fun n ω ↦ |X n ω - ℱ.limitProcess X μ ω| ^ p) 1 μ := by
  let L : Ω → ℝ := ℱ.limitProcess X μ
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hUI_l1 : UniformIntegrable X 1 μ :=
    martingale_uniformIntegrable_of_lp_bounded hf hp hbounded
  rcases hbounded with ⟨C, hC⟩
  have hmem_limit : MemLp L (ENNReal.ofReal p) μ :=
    hf.submartingale.memLp_limitProcess hC
  have hcondEq : ∀ n, X n =ᵐ[μ] μ[L | ℱ n] := by
    intro n
    simpa [L] using hf.ae_eq_condExp_limitProcess hUI_l1 n
  have hpowIntegrable : Integrable (fun ω ↦ |L ω| ^ p) μ := by
    simpa [L, Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      hmem_limit.integrable_norm_rpow
        (by simp [ENNReal.ofReal_eq_zero, not_le_of_gt hp0]) ENNReal.ofReal_ne_top
  let condPow : ℕ → Ω → ℝ := fun n ω ↦ μ[fun ω ↦ |L ω| ^ p | ℱ n] ω
  have hcondPowUI : UniformIntegrable condPow 1 μ := by
    simpa [condPow] using hpowIntegrable.uniformIntegrable_condExp_filtration (f := ℱ)
  have hconstPowUI : UniformIntegrable (fun _ : ℕ ↦ fun ω ↦ |L ω| ^ p) 1 μ := by
    -- Proof comment: the limit power is a single integrable function, so its constant family is UI.
    exact uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.2 hpowIntegrable)
  have hsumUI :
      UniformIntegrable (fun n ω ↦ condPow n ω + |L ω| ^ p) 1 μ := by
    -- Proof comment: rewrite the sum as a subtraction against the negated constant family.
    simpa [sub_eq_add_neg] using
      uniformIntegrable_sub hcondPowUI
        (uniformIntegrableSmul (μ := μ) (-1) hconstPowUI)
  have hscaledUI :
      UniformIntegrable (fun n ω ↦ (2 ^ (p - 1)) * (condPow n ω + |L ω| ^ p)) 1 μ := by
    -- Proof comment: the deterministic factor `2 ^ (p - 1)` is handled by the scalar-UI adapter.
    simpa [Pi.smul_apply] using uniformIntegrableSmul (μ := μ) (2 ^ (p - 1)) hsumUI
  have hpowMeas : ∀ n, AEStronglyMeasurable (fun ω ↦ |X n ω - L ω| ^ p) μ := by
    intro n
    have hcont : Continuous (fun x : ℝ ↦ |x| ^ p) :=
      continuous_abs.rpow_const fun _ ↦ Or.inr (show 0 ≤ p by linarith)
    exact hcont.comp_aestronglyMeasurable
      ((((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).sub hmem_limit.1)
  have hpowXDom : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ^ p ≤ condPow n ω := by
    intro n
    -- Proof comment: identify `X n` with the conditional expectation of the limit and apply Jensen.
    filter_upwards [hcondEq n, absRpow_condExp_le_ae (p := p) hmem_limit (ℱ.le n) hp.le] with
      ω hω hω'
    simpa [condPow, hω] using hω'
  have hpowDom :
      ∀ n, ∀ᵐ ω ∂μ,
        |(|X n ω - L ω| ^ p)| ≤ (2 ^ (p - 1)) * (condPow n ω + |L ω| ^ p) := by
    intro n
    filter_upwards [hpowXDom n] with ω hω
    have habs :
        |X n ω - L ω| ≤ |X n ω| + |L ω| := by
      simpa using (_root_.abs_sub_le (X n ω) 0 (L ω))
    have hsub :
        |X n ω - L ω| ^ p ≤ (|X n ω| + |L ω|) ^ p := by
      exact Real.rpow_le_rpow (abs_nonneg _) habs (by linarith)
    have hsum :
        (|X n ω| + |L ω|) ^ p ≤
          2 ^ (p - 1) * (|X n ω| ^ p + |L ω| ^ p) := by
      exact_mod_cast
        NNReal.rpow_add_le_mul_rpow_add_rpow
          (⟨|X n ω|, abs_nonneg _⟩ : ℝ≥0) (⟨|L ω|, abs_nonneg _⟩ : ℝ≥0) hp.le
    have hmul :
        2 ^ (p - 1) * (|X n ω| ^ p + |L ω| ^ p) ≤
          2 ^ (p - 1) * (condPow n ω + |L ω| ^ p) := by
      refine mul_le_mul_of_nonneg_left (add_le_add hω le_rfl) ?_
      exact Real.rpow_nonneg (by positivity) _
    calc
      |(|X n ω - L ω| ^ p)| = |X n ω - L ω| ^ p := by
        rw [abs_of_nonneg]
        exact Real.rpow_nonneg (abs_nonneg _) _
      _ ≤ (|X n ω| + |L ω|) ^ p := hsub
      _ ≤ 2 ^ (p - 1) * (|X n ω| ^ p + |L ω| ^ p) := hsum
      _ ≤ (2 ^ (p - 1)) * (condPow n ω + |L ω| ^ p) := hmul
  exact
    uniformIntegrable_of_abs_ae_le_of_uniformIntegrable
      hpowMeas hscaledUI hpowDom

/-- Helper for Theorem 11.10: `L¹` convergence of the powered absolute values implies convergence
of the original sequence in the `L^p` seminorm. -/
private theorem tendstoELpNormOfAbsRpowL1 {Y : ℕ → Ω → ℝ}
    (hp0 : 0 < p)
    (hpow :
      Tendsto (fun n ↦ eLpNorm (fun ω ↦ |Y n ω| ^ p) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (Y n) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hpow' :
      Tendsto (fun n ↦ eLpNorm (Y n) (ENNReal.ofReal p) μ ^ p) atTop (𝓝 0) := by
    convert hpow using 1
    funext n
    simpa [Real.norm_eq_abs, one_mul] using
      (eLpNorm_norm_rpow (μ := μ) (p := (1 : ℝ≥0∞)) (f := Y n) hp0).symm
  have hroot :
      Tendsto
        (fun n ↦ (eLpNorm (Y n) (ENNReal.ofReal p) μ ^ p) ^ (1 / p))
        atTop (𝓝 (0 ^ (1 / p))) :=
    Filter.Tendsto.ennrpow_const (1 / p) hpow'
  have hrewrite :
      (fun n ↦ (eLpNorm (Y n) (ENNReal.ofReal p) μ ^ p) ^ (1 / p)) =
        fun n ↦ eLpNorm (Y n) (ENNReal.ofReal p) μ := by
    funext n
    rw [one_div, ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
  -- Proof comment: take the `1 / p` power of the powered `L¹` norm convergence to recover the
  -- target `L^p` seminorm convergence.
  have hzero : (0 : ℝ≥0∞) ^ (1 / p) = 0 :=
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)
  rw [hrewrite] at hroot
  rw [hzero] at hroot
  exact hroot

-- Proof sketch: upgrade the uniform `L^p` bound to the canonical `L¹`-boundedness input for the
-- owner martingale convergence theorem, deduce almost-sure convergence to `ℱ.limitProcess X μ`,
-- use the owner `MemLp` theorem for the limit, and conclude `L^p` convergence by Vitali on the
-- finite measure space.
/-- Theorem 11.10: if a real-valued discrete martingale is uniformly bounded in `L^p` for some
`p > 1`, then its canonical limit process is `⨆ n, ℱ n`-measurable, belongs to `L^p(μ)`, and the
martingale converges to it both almost surely and in `L^p`. -/
theorem martingale_convergence_to_memLp_limitProcess_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    StronglyMeasurable[⨆ n, ℱ n] (ℱ.limitProcess X μ) ∧
      MemLp (ℱ.limitProcess X μ) (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
      (letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
       TendstoInLp (ENNReal.ofReal p) μ X (ℱ.limitProcess X μ)) :=
  by
    let L : Ω → ℝ := ℱ.limitProcess X μ
    letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    rcases hbounded with ⟨C, hC⟩
    have hUI_l1 : UniformIntegrable X 1 μ :=
      martingale_uniformIntegrable_of_lp_bounded hf hp ⟨C, hC⟩
    have hlimit_meas : StronglyMeasurable[⨆ n, ℱ n] L := by
      simpa [L] using
        (MeasureTheory.Filtration.stronglyMeasurable_limitProcess
          (f := X) (ℱ := ℱ) (μ := μ))
    have hmem_limit : MemLp L (ENNReal.ofReal p) μ :=
      hf.submartingale.memLp_limitProcess hC
    have hlimit_ae :
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (L ω)) :=
      by
        simpa [L] using
          hf.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hUI_l1
    have hpowUI :
        UniformIntegrable (fun n ω ↦ |X n ω - L ω| ^ p) 1 μ :=
      uniformIntegrableAbsSubLimitProcessRpowOfLpBounded hf hp ⟨C, hC⟩
    have hpowAe :
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ |X n ω - L ω| ^ p) atTop (𝓝 0) := by
      filter_upwards [hlimit_ae] with ω hω
      have hsub' :
          Tendsto (fun n ↦ X n ω - L ω) atTop (𝓝 (L ω - L ω)) :=
        hω.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ L ω) atTop (𝓝 (L ω)))
      have hsub :
          Tendsto (fun n ↦ X n ω - L ω) atTop (𝓝 0) := by
        simpa using hsub'
      have habs :
          Tendsto (fun n ↦ |X n ω - L ω|) atTop (𝓝 0) := by
        simpa [Real.norm_eq_abs] using hsub.norm
      simpa [Real.zero_rpow hp0.ne'] using
        Tendsto.rpow_const habs (Or.inr (show 0 ≤ p by linarith))
    have hpowNorm :
        Tendsto (fun n ↦ eLpNorm (fun ω ↦ |X n ω - L ω| ^ p) 1 μ) atTop (𝓝 0) := by
      have hpowMeas : ∀ n, AEStronglyMeasurable (fun ω ↦ |X n ω - L ω| ^ p) μ :=
        hpowUI.aestronglyMeasurable
      simpa using
        (MeasureTheory.tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp)
          hpowMeas (MemLp.zero : MemLp (0 : Ω → ℝ) 1 μ)
          hpowUI.unifIntegrable hpowAe)
    have hnorm :
        Tendsto (fun n ↦ eLpNorm (X n - L) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
      -- Proof comment: first prove `L¹` convergence of the powered errors, then take the `p`-th root.
      simpa [L, Pi.sub_apply] using
        tendstoELpNormOfAbsRpowL1 (μ := μ) (p := p) (Y := fun n ω ↦ X n ω - L ω) hp0 hpowNorm
    have hmem_X : ∀ n, MemLp (X n) (ENNReal.ofReal p) μ := by
      intro n
      exact ⟨((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable,
        lt_of_le_of_lt (hC n) ENNReal.coe_lt_top⟩
    refine ⟨hlimit_meas, hmem_limit, ?_, ?_⟩
    · simpa [L] using hlimit_ae
    · -- Proof comment: the `eLpNorm` criterion is the owner bridge from seminorm convergence to `L^p`.
      exact (tendstoInLp_iff_tendsto_eLpNorm).2 ⟨hmem_X, by simpa [L] using hmem_limit, by simpa [L] using hnorm⟩

/-- Theorem 11.10, owner-level `L^p`-convergence component: an `L^p`-bounded martingale with
`1 < p` converges in `L^p` to its canonical limit process. -/
theorem martingale_tendstoInLp_limitProcess_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
    TendstoInLp (ENNReal.ofReal p) μ X (ℱ.limitProcess X μ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  obtain ⟨_, _, _, h_tendsto⟩ :=
    martingale_convergence_to_memLp_limitProcess_of_lp_bounded hf hp hbounded
  exact h_tendsto

/-- Theorem 11.10, bridge `eLpNorm` formulation of the owner-level `L^p` convergence theorem. -/
theorem martingale_tendsto_eLpNorm_limitProcess_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    Tendsto (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  exact (martingale_tendstoInLp_limitProcess_of_lp_bounded hf hp hbounded).tendsto_eLpNorm

-- Proof sketch: first pass from `L^p` convergence to `ℱ.limitProcess X μ` to the conditional
-- expectation representation of each `X n`, then apply conditional Jensen to dominate
-- `|X n| ^ p` by the conditional expectations of `|ℱ.limitProcess X μ| ^ p`; the latter family is
-- uniformly integrable by the owner theorem `Integrable.uniformIntegrable_condExp_filtration`.
/-- Theorem 11.10, companion consequence: for an `L^p`-bounded martingale with `1 < p`, the
family `(|X_n| ^ p)_n` is uniformly integrable. -/
theorem martingale_uniformIntegrable_abs_rpow_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    UniformIntegrable (fun n ω ↦ |X n ω| ^ p) 1 μ := by
  let L : Ω → ℝ := ℱ.limitProcess X μ
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  have hUI_l1 : UniformIntegrable X 1 μ :=
    martingale_uniformIntegrable_of_lp_bounded hf hp hbounded
  rcases hbounded with ⟨C, hC⟩
  have hmem_limit : MemLp L (ENNReal.ofReal p) μ :=
    hf.submartingale.memLp_limitProcess hC
  have hcondEq : ∀ n, X n =ᵐ[μ] μ[L | ℱ n] := by
    intro n
    simpa [L] using hf.ae_eq_condExp_limitProcess hUI_l1 n
  have hpowIntegrable : Integrable (fun ω ↦ |L ω| ^ p) μ := by
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    simpa [L, Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      hmem_limit.integrable_norm_rpow
        (by simp [ENNReal.ofReal_eq_zero, not_le_of_gt hp0]) ENNReal.ofReal_ne_top
  let condPow : ℕ → Ω → ℝ := fun n ω ↦ μ[fun ω ↦ |L ω| ^ p | ℱ n] ω
  have hcondPowUI : UniformIntegrable condPow 1 μ := by
    simpa [condPow] using hpowIntegrable.uniformIntegrable_condExp_filtration (f := ℱ)
  have hpowMeas : ∀ n, AEStronglyMeasurable (fun ω ↦ |X n ω| ^ p) μ := by
    intro n
    have hcont : Continuous (fun x : ℝ ↦ |x| ^ p) :=
      continuous_abs.rpow_const fun _ ↦ Or.inr (show 0 ≤ p by linarith)
    exact hcont.comp_aestronglyMeasurable
      (((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable)
  have hpowDom : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ^ p ≤ condPow n ω := by
    intro n
    -- Proof comment: identify `X n` with the conditional expectation of the limit and apply Jensen.
    filter_upwards [hcondEq n, absRpow_condExp_le_ae (p := p) hmem_limit (ℱ.le n) hp.le] with
      ω hω hω'
    simpa [condPow, hω] using hω'
  exact
    uniformIntegrable_of_abs_ae_le_of_uniformIntegrable
      hpowMeas hcondPowUI (fun n ↦ by
        filter_upwards [hpowDom n] with ω hω
        simpa [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hω)

end

/- The source-facing theorem above exposes the full canonical limit-process conclusion publicly.
The shorter owner-level `TendstoInLp` consequence, its `eLpNorm` bridge, and the
uniform-integrability statement remain thin companions. -/

end MeasureTheory
