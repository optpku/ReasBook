/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Filter
open scoped Topology

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- Helper for Theorem 6.28: the derivative slice at a fixed point of the interval is almost
everywhere strongly measurable. -/
private lemma deriv_slice_aestronglyMeasurable_on_Ioo
    {a b x : ℝ} (hx : x ∈ Set.Ioo a b) {f f' : α → ℝ → ℝ}
    (h_int : ∀ y ∈ Set.Ioo a b, Integrable (fun ω ↦ f ω y) μ)
    (h_diff : ∀ᵐ ω ∂μ, ∀ y ∈ Set.Ioo a b, HasDerivAt (f ω) (f' ω y) y) :
    AEStronglyMeasurable (fun ω ↦ f' ω x) μ := by
  -- Choose a sequence approaching `x` from the right while staying in the interval.
  obtain ⟨y, _, hy_mem, hy_tendsto⟩ := by
    simpa [Set.mem_Ioo] using exists_seq_strictAnti_tendsto' hx.2
  have hy_mem' : ∀ n, y n ∈ Set.Ioo a b := fun n ↦
    ⟨hx.1.trans (hy_mem n).1, (hy_mem n).2⟩
  have hy_tendsto_ne : Tendsto y atTop (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    exact ⟨hy_tendsto, Eventually.of_forall (fun n ↦ (hy_mem n).1.ne')⟩
  have hslope_meas : ∀ n, AEStronglyMeasurable (fun ω ↦ slope (f ω) x (y n)) μ := by
    intro n
    -- Each slope is a scalar multiple of the difference of two integrable slices.
    simpa [slope] using
      (((h_int (y n) (hy_mem' n)).sub (h_int x hx)).aestronglyMeasurable).const_mul
        ((y n - x)⁻¹)
  have hslope_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ slope (f ω) x (y n)) atTop (𝓝 (f' ω x)) := by
    -- For almost every `ω`, the slopes converge to the derivative at `x`.
    filter_upwards [h_diff] with ω hω
    exact (hω x hx).tendsto_slope.comp hy_tendsto_ne
  exact aestronglyMeasurable_of_tendsto_ae atTop hslope_meas hslope_tendsto

/-- Helper for Theorem 6.28: on an open parameter set, the derivative slice at any point is
almost everywhere strongly measurable. -/
private lemma deriv_slice_aestronglyMeasurable
    {I : Set ℝ} (hI_open : IsOpen I) {x : ℝ} (hx : x ∈ I) {f f' : α → ℝ → ℝ}
    (h_int : ∀ y ∈ I, Integrable (fun ω ↦ f ω y) μ)
    (h_diff : ∀ᵐ ω ∂μ, ∀ y ∈ I, HasDerivAt (f ω) (f' ω y) y) :
    AEStronglyMeasurable (fun ω ↦ f' ω x) μ := by
  obtain ⟨a, b, hx', hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI_open.mem_nhds hx)
  have h_int_Ioo : ∀ y ∈ Set.Ioo a b, Integrable (fun ω ↦ f ω y) μ := fun y hy ↦
    h_int y (hIoo hy)
  have h_diff_Ioo : ∀ᵐ ω ∂μ, ∀ y ∈ Set.Ioo a b, HasDerivAt (f ω) (f' ω y) y := by
    filter_upwards [h_diff] with ω hω
    intro y hy
    exact hω y (hIoo hy)
  exact deriv_slice_aestronglyMeasurable_on_Ioo hx' h_int_Ioo h_diff_Ioo

-- Proof sketch: Fix `x ∈ I` and apply differentiation under the integral sign on the open
-- interval `I`. Derive almost-everywhere strong measurability of the derivative slice by
-- shrinking to a smaller open interval around `x`, then apply the canonical neighborhood-level
-- differentiation-under-the-integral theorem.
/-- Theorem 6.28: If `f : α → ℝ → ℝ` is integrable in `ω` for every parameter in an open set
`I ⊆ ℝ`, is almost everywhere differentiable there with derivative `f'`, and `‖f' ω x‖` is
uniformly dominated on `I` by an integrable function `bound`, then for every `x ∈ I` the slice
`ω ↦ f' ω x` is integrable and the map `x ↦ ∫ ω, f ω x ∂μ` has derivative
`∫ ω, f' ω x ∂μ` at `x`. This is the source-facing interval/set formulation, obtained as a thin
bridge to the canonical owner theorem
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem integrable_deriv_slice_and_hasDerivAt_integral_of_dominated_on_open
    {I : Set ℝ} (hI_open : IsOpen I) {x : ℝ} (hx : x ∈ I) {f f' : α → ℝ → ℝ}
    {bound : α → ℝ} (h_int : ∀ y ∈ I, Integrable (fun ω ↦ f ω y) μ)
    (h_diff : ∀ᵐ ω ∂μ, ∀ y ∈ I, HasDerivAt (f ω) (f' ω y) y)
    (h_bound : ∀ᵐ ω ∂μ, ∀ y ∈ I, ‖f' ω y‖ ≤ bound ω)
    (h_bound_int : Integrable bound μ) :
    Integrable (fun ω ↦ f' ω x) μ ∧
      HasDerivAt (fun y ↦ ∫ ω, f ω y ∂μ) (∫ ω, f' ω x ∂μ) x := by
  have h_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fun ω ↦ f ω y) μ := by
    -- Integrable slices are automatically almost everywhere strongly measurable.
    filter_upwards [hI_open.mem_nhds hx] with y hy
    exact (h_int y hy).aestronglyMeasurable
  exact
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (hI_open.mem_nhds hx) h_meas (h_int x hx)
      (deriv_slice_aestronglyMeasurable hI_open hx h_int h_diff) h_bound h_bound_int h_diff
