/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

universe u

open scoped ENNReal

namespace MeasureTheory

/-- Helper for Theorem 4.19: the canonical pointwise inclusion from `L^p(μ)` to `L^{p'}(μ)` on the
same almost-everywhere equivalence class. -/
noncomputable def lp_inclusion_fun {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p) :
    Lp ℝ p μ → Lp ℝ p' μ :=
  fun f ↦ ⟨(f : α →ₘ[μ] ℝ), Lp.antitone hp'le f.2⟩

/-- Helper for Theorem 4.19: the pointwise inclusion preserves addition because it keeps the same
underlying `AEEqFun`. -/
theorem lp_inclusion_fun_add {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p)
    (f g : Lp ℝ p μ) :
    lp_inclusion_fun μ hp'le (f + g) = lp_inclusion_fun μ hp'le f + lp_inclusion_fun μ hp'le g :=
  rfl

/-- Helper for Theorem 4.19: the pointwise inclusion commutes with scalar multiplication because
it keeps the same underlying `AEEqFun`. -/
theorem lp_inclusion_fun_smul {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p)
    (c : ℝ) (f : Lp ℝ p μ) :
    lp_inclusion_fun μ hp'le (c • f) = c • lp_inclusion_fun μ hp'le f :=
  rfl

/-- Helper for Theorem 4.19: the algebraic inclusion from `L^p(μ)` to `L^{p'}(μ)` as a linear
map before adding continuity. -/
noncomputable def lp_inclusion_linear {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p) :
    Lp ℝ p μ →ₗ[ℝ] Lp ℝ p' μ :=
  { toFun := lp_inclusion_fun μ hp'le
    map_add' := lp_inclusion_fun_add μ hp'le
    map_smul' := lp_inclusion_fun_smul μ hp'le }

/-- Helper for Theorem 4.19: the finite-measure comparison factor appearing in the `L^p` to
`L^{p'}` norm estimate. -/
noncomputable def lp_inclusion_bound {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (_hp'le : p' ≤ p) : ℝ :=
  ((μ Set.univ) ^ (1 / p'.toReal - 1 / p.toReal)).toReal

/-- Helper for Theorem 4.19: the finite-measure comparison factor is finite, so its `toReal`
value can be used in a norm inequality. -/
theorem lp_inclusion_factor_ne_top {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p) :
    μ Set.univ ^ (1 / p'.toReal - 1 / p.toReal) ≠ ∞ := by
  refine (ENNReal.rpow_lt_top_of_nonneg ?_ (by finiteness)).ne
  by_cases hp_top : p = ∞
  · simp [hp_top]
  have hp'_ne_top : p' ≠ ∞ := by
    intro hp'_top
    exact hp_top (top_unique (hp'_top ▸ hp'le))
  have hp'_one : 1 ≤ p' := Fact.out
  have hp_one : 1 ≤ p := Fact.out
  have hp'_real_pos : 0 < p'.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp'_one).ne' hp'_ne_top
  have hp_real_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp_one).ne' hp_top
  exact sub_nonneg.mpr <|
    one_div_le_one_div_of_le hp'_real_pos (ENNReal.toReal_mono hp_top hp'le)

/-- Helper for Theorem 4.19: the canonical inclusion from `L^p(μ)` to `L^{p'}(μ)` satisfies the
standard finite-measure comparison estimate. -/
theorem lp_inclusion_norm_le {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p)
    (f : Lp ℝ p μ) :
    ‖lp_inclusion_linear μ hp'le f‖ ≤ lp_inclusion_bound μ hp'le * ‖f‖ := by
  -- The comparison factor is finite, so we may pass from `eLpNorm` to the real norm via
  -- `ENNReal.toReal`.
  have h_factor_ne_top :
      μ Set.univ ^ (1 / p'.toReal - 1 / p.toReal) ≠ ∞ :=
    lp_inclusion_factor_ne_top μ hp'le
  -- Rewrite both norms using `Lp.norm_def`, then apply the finite-measure comparison theorem.
  rw [Lp.norm_def, Lp.norm_def, lp_inclusion_bound, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top h_factor_ne_top (Lp.eLpNorm_ne_top f)) ?_
  simpa [lp_inclusion_linear, lp_inclusion_fun, mul_comm] using
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp'le (Lp.aestronglyMeasurable f)

/-- The canonical continuous linear inclusion from `L^p(μ)` to `L^{p'}(μ)` on a finite-measure
space, for `1 ≤ p' ≤ p`. -/
noncomputable def lp_inclusion {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p) :
    Lp ℝ p μ →L[ℝ] Lp ℝ p' μ :=
  LinearMap.mkContinuous
    (lp_inclusion_linear μ hp'le)
    (lp_inclusion_bound μ hp'le)
    (lp_inclusion_norm_le μ hp'le)

/-- Helper for Theorem 4.19: the canonical inclusion between finite-measure `L^p` spaces
preserves the underlying almost-everywhere equivalence class. -/
-- Proof sketch: unfold the inclusion map; it only changes the membership proof and leaves the
-- represented `AEEqFun` untouched.
theorem lp_inclusion_coe {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p) (f : Lp ℝ p μ) :
    ((lp_inclusion μ hp'le f : Lp ℝ p' μ) : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ) :=
  rfl

/-- Theorem 4.19: If `μ` is a finite measure and `1 ≤ p' ≤ p`, then `ℒ^p(μ)` is contained in
`ℒ^{p'}(μ)` via the canonical inclusion `f ↦ f`, and this inclusion is continuous. -/
-- Proof sketch: construct the inclusion as a continuous linear map using the finite-measure
-- `eLpNorm` comparison estimate, then extract continuity from that bundled map.
theorem continuous_lp_inclusion_of_le {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {p' p : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ p)] (hp'le : p' ≤ p) :
    Continuous (lp_inclusion μ hp'le : Lp ℝ p μ → Lp ℝ p' μ) := by
  -- The bundled inclusion is already continuous by construction.
  exact (lp_inclusion μ hp'le).continuous

end MeasureTheory
