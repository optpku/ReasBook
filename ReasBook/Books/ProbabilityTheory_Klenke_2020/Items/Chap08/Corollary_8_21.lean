/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ENNReal ProbabilityTheory Topology

universe u

namespace MeasureTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Helper for Corollary 8.21: the function `x ↦ |x| ^ q` is convex on `ℝ` whenever `q ≥ 1`. -/
private lemma abs_rpow_convexOn_univ (q : ℝ) (hq_one : 1 ≤ q) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ q) := by
  have hrange_abs : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact abs_nonneg y
    · intro hx
      refine ⟨x, Set.mem_univ x, ?_⟩
      exact abs_of_nonneg hx
  have hrpow : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) (fun x : ℝ ↦ x ^ q) := by
    simpa [hrange_abs] using (convexOn_rpow hq_one)
  have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
    simpa [Real.norm_eq_abs] using
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
  -- Compose the convex absolute value with the convex power on `[0, ∞)`.
  simpa using hrpow.comp habs
    (by
      simpa [hrange_abs] using
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans zero_le_one hq_one)))

/-- Helper for Corollary 8.21: conditional Jensen gives the pointwise powered estimate in the
finite-`p` case. -/
private lemma abs_rpow_condExp_le_ae {X : Ω → ℝ} {ℱ : MeasurableSpace Ω}
    (hX : MemLp X p μ) (hℱ : ℱ ≤ mΩ) (hp_top : p ≠ ∞) :
    ∀ᵐ ω ∂μ, |μ[X | ℱ] ω| ^ p.toReal ≤ μ[fun ω ↦ |X ω| ^ p.toReal | ℱ] ω := by
  have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp_one)
  have hX_int : Integrable X μ :=
    memLp_one_iff_integrable.1 <| hX.mono_exponent hp_one
  have hX_rpow_int : Integrable (fun ω ↦ |X ω| ^ p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hX.integrable_norm_rpow hp_zero hp_top
  -- Apply conditional Jensen directly to `X` with the convex function `x ↦ |x| ^ p.toReal`.
  simpa [Function.comp_apply, Real.norm_eq_abs] using
    (abs_rpow_convexOn_univ p.toReal (by
      rw [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
      exact hp_one)).map_condExp_le_of_finiteDimensional
        hℱ hX_int hX_rpow_int

/-- Helper for Corollary 8.21: conditional expectation is an `L^p` contraction when `p < ∞`. -/
private lemma condExp_eLpNorm_le_finite {X : Ω → ℝ} {ℱ : MeasurableSpace Ω}
    (hX : MemLp X p μ) (hℱ : ℱ ≤ mΩ) (hp_top : p ≠ ∞) :
    eLpNorm (μ[X | ℱ]) p μ ≤ eLpNorm X p μ := by
  have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp_one)
  have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hpow_ae :
      ∀ᵐ ω ∂μ, |μ[X | ℱ] ω| ^ p.toReal ≤ μ[fun ω ↦ |X ω| ^ p.toReal | ℱ] ω :=
    @abs_rpow_condExp_le_ae Ω mΩ μ _ p _ X ℱ hX hℱ hp_top
  have hpow_le :
      eLpNorm (fun ω ↦ |μ[X | ℱ] ω| ^ p.toReal) 1 μ ≤
        eLpNorm (fun ω ↦ |X ω| ^ p.toReal) 1 μ := by
    calc
      eLpNorm (fun ω ↦ |μ[X | ℱ] ω| ^ p.toReal) 1 μ ≤
          eLpNorm (μ[fun ω ↦ |X ω| ^ p.toReal | ℱ]) 1 μ :=
        eLpNorm_mono_ae_real <|
          hpow_ae.mono
            (fun ω hω ↦ by
              have h_nonneg : 0 ≤ |μ[X | ℱ] ω| ^ p.toReal :=
                Real.rpow_nonneg (abs_nonneg _) _
              simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using hω)
      _ ≤ eLpNorm (fun ω ↦ |X ω| ^ p.toReal) 1 μ :=
        eLpNorm_one_condExp_le_eLpNorm _
  have hp_mul : 1 * ENNReal.ofReal p.toReal = p := by
    simp [ENNReal.ofReal_toReal hp_top]
  have hleft :
      eLpNorm (fun ω ↦ |μ[X | ℱ] ω| ^ p.toReal) 1 μ = eLpNorm (μ[X | ℱ]) p μ ^ p.toReal := by
    simpa [Real.norm_eq_abs, hp_mul] using
      (eLpNorm_norm_rpow (μ[X | ℱ]) hq_pos :
        eLpNorm (fun x ↦ ‖μ[X | ℱ] x‖ ^ p.toReal) 1 μ =
          eLpNorm (μ[X | ℱ]) (1 * ENNReal.ofReal p.toReal) μ ^ p.toReal)
  have hright :
      eLpNorm (fun ω ↦ |X ω| ^ p.toReal) 1 μ = eLpNorm X p μ ^ p.toReal := by
    simpa [Real.norm_eq_abs, hp_mul] using
      (eLpNorm_norm_rpow X hq_pos :
        eLpNorm (fun x ↦ ‖X x‖ ^ p.toReal) 1 μ =
          eLpNorm X (1 * ENNReal.ofReal p.toReal) μ ^ p.toReal)
  -- Rewrite both `L¹` norms as `L^p` norms raised to the same positive power and cancel it.
  rw [hleft, hright] at hpow_le
  exact (ENNReal.strictMono_rpow_of_pos hq_pos).le_iff_le.mp hpow_le

-- Proof sketch: combine conditional Jensen for the convex function `x ↦ ‖x‖ ^ p.toReal` when
-- `p < ∞` with the essential-supremum estimate for `p = ∞`, and use the finite-measure
-- assumption to keep all integrability side conditions available.
/-- Corollary 8.21 (1): conditional expectation is an `L^p` contraction on a finite-measure
space. -/
theorem condExp_eLpNorm_le {X : Ω → ℝ} {ℱ : MeasurableSpace Ω} (hX : MemLp X p μ)
    (hℱ : ℱ ≤ mΩ) :
    eLpNorm (μ[X | ℱ]) p μ ≤ eLpNorm X p μ := by
  by_cases hp_top : p = ∞
  · -- The `p = ∞` case is the textbook essential-supremum bound.
    let R : NNReal := ⟨(eLpNorm X ∞ μ).toReal, ENNReal.toReal_nonneg⟩
    have hX_ne_top : eLpNorm X ∞ μ ≠ ∞ := by
      simpa [hp_top] using hX.2.ne
    have hX_ess_ne_top : eLpNormEssSup X μ ≠ ∞ := by
      simpa [eLpNorm_exponent_top] using hX_ne_top
    have hX_ae_bound :
        ∀ᵐ ω ∂μ, |X ω| ≤ R := by
      filter_upwards [enorm_ae_le_eLpNormEssSup X μ] with ω hω
      have hω' : ‖X ω‖ₑ ≤ eLpNorm X ∞ μ := by
        simpa [eLpNorm_exponent_top] using hω
      have hω'' : ‖X ω‖ ≤ (eLpNorm X ∞ μ).toReal := by
        simpa using ENNReal.toReal_mono hX_ne_top hω'
      simpa [Real.norm_eq_abs] using hω''
    have hcond_abs_bound :
        ∀ᵐ ω ∂μ, |μ[X | ℱ] ω| ≤ R := ae_bdd_condExp_of_ae_bdd hX_ae_bound
    have hcond_ae_bound :
        ∀ᵐ ω ∂μ, ‖μ[X | ℱ] ω‖ ≤ (eLpNorm X ∞ μ).toReal := by
      filter_upwards [hcond_abs_bound] with ω hω
      simpa [Real.norm_eq_abs] using hω
    -- The conditional expectation inherits the same a.e. bound, hence the same `L∞` seminorm.
    calc
      eLpNorm (μ[X | ℱ]) p μ = eLpNorm (μ[X | ℱ]) ∞ μ := by simp [hp_top]
      _ = eLpNormEssSup (μ[X | ℱ]) μ := eLpNorm_exponent_top
      _ ≤ ENNReal.ofReal ((eLpNorm X ∞ μ).toReal) :=
        eLpNormEssSup_le_of_ae_bound hcond_ae_bound
      _ = eLpNorm X p μ := by
        rw [hp_top, eLpNorm_exponent_top]
        exact ENNReal.ofReal_toReal hX_ess_ne_top
  · exact @condExp_eLpNorm_le_finite Ω mΩ μ _ p _ X ℱ hX hℱ hp_top

/-- Corollary 8.21 (1), codomain form: for `p ≥ 1` on a finite-measure space, conditional
expectation sends `L^p(Ω, mΩ, μ)` into `L^p(Ω, ℱ, μ)`. -/
theorem MemLp.condExp_of_one_le {X : Ω → ℝ} {ℱ : MeasurableSpace Ω} (hX : MemLp X p μ)
    (hℱ : ℱ ≤ mΩ) :
    MemLp (μ[X | ℱ]) p μ := by
  refine ⟨(stronglyMeasurable_condExp.mono hℱ).aestronglyMeasurable, ?_⟩
  have hnorm : eLpNorm (μ[X | ℱ]) p μ ≤ eLpNorm X p μ :=
    @condExp_eLpNorm_le Ω mΩ μ _ p _ X ℱ hX hℱ
  exact hnorm.trans_lt hX.eLpNorm_lt_top

-- Proof sketch: use linearity of conditional expectation to rewrite the difference as the
-- conditional expectation of `XSeq n - X`, apply the contraction estimate termwise, and then use
-- squeeze at `0`.
/-- Corollary 8.21 (2): conditional expectation is continuous for `L^p` convergence on a
finite-measure space. -/
theorem tendsto_eLpNorm_condExp_sub_of_tendsto_eLpNorm {ℱ : MeasurableSpace Ω}
    (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ} {XSeq : ℕ → Ω → ℝ} (hX : MemLp X p μ)
    (hXSeq : ∀ n, MemLp (XSeq n) p μ)
    (h_tendsto : Tendsto (fun n ↦ eLpNorm (XSeq n - X) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (μ[XSeq n | ℱ] - μ[X | ℱ]) p μ) atTop (𝓝 0) := by
  have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hX_int : Integrable X μ :=
    memLp_one_iff_integrable.1 <| hX.mono_exponent hp_one
  have hterm_bound :
      ∀ n, eLpNorm (μ[XSeq n | ℱ] - μ[X | ℱ]) p μ ≤ eLpNorm (XSeq n - X) p μ := by
    intro n
    have hXSeq_int : Integrable (XSeq n) μ :=
      memLp_one_iff_integrable.1 <| (hXSeq n).mono_exponent hp_one
    -- Rewrite the difference of conditional expectations as the conditional expectation
    -- of the difference, then invoke the contraction estimate from part (1).
    calc
      eLpNorm (μ[XSeq n | ℱ] - μ[X | ℱ]) p μ = eLpNorm (μ[XSeq n - X | ℱ]) p μ := by
        exact eLpNorm_congr_ae (condExp_sub hXSeq_int hX_int ℱ).symm
      _ ≤ eLpNorm (XSeq n - X) p μ :=
        by
          have hsub :
              eLpNorm (μ[XSeq n - X | ℱ]) p μ ≤ eLpNorm (XSeq n - X) p μ :=
            @condExp_eLpNorm_le Ω mΩ μ _ p _ (XSeq n - X) ℱ ((hXSeq n).sub hX) hℱ
          exact hsub
  -- The sequence is squeezed between `0` and the given convergent error sequence.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto ?_ ?_
  · intro n
    exact zero_le _
  · intro n
    exact hterm_bound n

end MeasureTheory
