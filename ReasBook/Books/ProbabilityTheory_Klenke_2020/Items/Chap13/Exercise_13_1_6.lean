/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped Pointwise Topology

/-- Helper for Exercise 13.1.6: if `A` is `μ`-null, then the Radon-Nikodym derivative of `μ`
with respect to a reference measure `ν` vanishes `ν.restrict A`-almost everywhere. -/
lemma ae_rnDeriv_eq_zero_on_restrict_of_null
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [Measure.HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {A : Set α} (hA_null : μ A = 0) :
    μ.rnDeriv ν =ᵐ[ν.restrict A] 0 := by
  -- The null set hypothesis makes `μ` singular with respect to `ν.restrict A`.
  have hrestrict : ν.restrict A ≪ ν := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ hrestrict
  let s := toMeasurable μ A
  refine Measure.MutuallySingular.mk (s := s) (t := sᶜ) ?_ ?_ ?_
  · simpa [s] using (measure_toMeasurable (μ := μ) A).trans hA_null
  · rw [Measure.restrict_apply (measurableSet_toMeasurable μ A).compl]
    have hs : A ⊆ s := subset_toMeasurable μ A
    have : sᶜ ∩ A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx.1 (hs hx.2)
    rw [this, measure_empty]
  · intro x _
    by_cases hx : x ∈ s
    · exact Or.inl hx
    · exact Or.inr hx

/-- Helper for Exercise 13.1.6: a translated dilate of a set contained in `closedBall 0 R`
stays inside `closedBall x (r * R)` for `r ≥ 0`. -/
lemma translatedSmul_subset_closedBall
    {d : ℕ} {C : Set (Fin d → ℝ)} {R r : ℝ}
    (hC : C ⊆ Metric.closedBall (0 : Fin d → ℝ) R) (hr : 0 ≤ r)
    (x : Fin d → ℝ) :
    ({x} : Set (Fin d → ℝ)) + r • C ⊆ Metric.closedBall x (r * R) := by
  -- Rewrite points in the translated dilate as `x + r • y` and bound the displacement from `x`.
  intro z hz
  rcases hz with ⟨u, hu, w, hw, rfl⟩
  simp only [Set.mem_singleton_iff] at hu
  subst u
  simp only [Set.mem_smul_set] at hw
  rcases hw with ⟨v, hv, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hvR : ‖v‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC hv
  calc
    ‖x + r • v - x‖ = ‖r • v‖ := by simp
    _ = |r| * ‖v‖ := norm_smul _ _
    _ ≤ r * R := by
      rw [abs_of_nonneg hr]
      gcongr

/-- Helper for Exercise 13.1.6: the normalized closed-ball masses of a measure vanish on a
`μ`-null set. -/
lemma ae_tendsto_zero_scaled_closedBall_density_of_null
    {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsLocallyFiniteMeasure μ]
    {A : Set (Fin d → ℝ)} (hA_null : μ A = 0) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(volume.restrict A),
      Tendsto
        (fun r : ℝ ↦ μ.real (Metric.closedBall x (R * r)) / r ^ d)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hmul :
      Tendsto (fun r : ℝ ↦ R * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive rescaling preserves the right-hand neighborhood of `0`.
    have hmul_nhds : Tendsto (fun r : ℝ ↦ R * r) (𝓝 (0 : ℝ)) (𝓝 (R * 0)) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ R) (𝓝 (0 : ℝ)) (𝓝 R)).mul tendsto_id)
    have hmul_to_nhds : Tendsto (fun r : ℝ ↦ R * r) (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ)) :=
      by
        simpa using
          hmul_nhds.mono_left
            (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hmul_to_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using mul_pos hR hr
  have hrestrict : volume.restrict A ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hBes :
      ∀ᵐ x ∂(volume.restrict A),
        Tendsto
          (fun r : ℝ ↦ μ (Metric.closedBall x r) / volume (Metric.closedBall x r))
          (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv volume x)) :=
    hrestrict.ae_le (Besicovitch.ae_tendsto_rnDeriv μ volume)
  filter_upwards [hBes, ae_rnDeriv_eq_zero_on_restrict_of_null (μ := μ) (ν := volume) (A := A) hA_null]
    with x hx hzero
  have hzero' : μ.rnDeriv volume x = 0 := by simpa using hzero
  have hxZero :
      Tendsto
        (fun r : ℝ ↦ μ (Metric.closedBall x r) / volume (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [hzero'] using hx
  have hxScaled :
      Tendsto
        (fun r : ℝ ↦ μ (Metric.closedBall x (R * r)) / volume (Metric.closedBall x (R * r)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := hxZero.comp hmul
  have hxScaledReal :
      Tendsto
        (fun r : ℝ ↦
          ((μ (Metric.closedBall x (R * r)) / volume (Metric.closedBall x (R * r))).toReal : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hxScaled
  let c : ℝ := R ^ d * volume.real (Metric.ball (0 : Fin d → ℝ) 1)
  have hrewrite :
      (fun r : ℝ ↦ μ.real (Metric.closedBall x (R * r)) / r ^ d) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun r : ℝ ↦
          ((μ (Metric.closedBall x (R * r)) / volume (Metric.closedBall x (R * r))).toReal : ℝ) *
            c) := by
    -- Express the closed-ball mass using the Besicovitch ratio and the explicit Haar scaling law.
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpow : r ^ d ≠ 0 := pow_ne_zero d hr.ne'
    have hvol_ball_pos : 0 < volume.real (Metric.ball (0 : Fin d → ℝ) 1) := by
      exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Fin d → ℝ) zero_lt_one).ne'
        measure_ball_lt_top.ne
    have hvol :
        volume.real (Metric.closedBall x (R * r)) =
          (R * r) ^ d * volume.real (Metric.ball (0 : Fin d → ℝ) 1) := by
      rw [Measure.addHaar_real_closedBall volume x (mul_nonneg hR.le hr.le), Module.finrank_fin_fun]
    have hvol' :
        (volume (Metric.closedBall x (R * r))).toReal =
          (R * r) ^ d * volume.real (Metric.ball (0 : Fin d → ℝ) 1) := by
      simpa [measureReal_def] using hvol
    simp only [ENNReal.toReal_div, measureReal_def]
    rw [hvol']
    rw [mul_pow]
    simp [c]
    field_simp [hrpow, hR.ne', hvol_ball_pos.ne']
  have hconst :
      Tendsto
        (fun r : ℝ ↦
          ((μ (Metric.closedBall x (R * r)) / volume (Metric.closedBall x (R * r))).toReal : ℝ) *
            c)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [zero_mul] using
      (hxScaledReal.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ c) (𝓝[>] (0 : ℝ)) (𝓝 c)))
  exact Tendsto.congr' hrewrite.symm hconst

-- Proof sketch: apply the owner theorem `VitaliFamily.ae_tendsto_rnDeriv` to the Vitali family
-- generated by the translated dilates `x + r • C`; since `A` is `μ`-null, the
-- Radon--Nikodym derivative of `μ` with respect to Lebesgue vanishes Lebesgue-almost everywhere on
-- `A`, so the normalized masses tend to `0` there. Only local finiteness of `μ` is used.
/-- Exercise 13.1.6 (1): For a locally finite measure on `ℝ^d`, the normalized masses of the translated
dilates of a bounded open convex set `C` containing `0` converge to `0` at Lebesgue-almost every
point of a `μ`-null set. -/
theorem ae_tendsto_zero_scaled_set_density_of_null
    {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsLocallyFiniteMeasure μ]
    {A C : Set (Fin d → ℝ)}
    (hA_null : μ A = 0) (hC_bounded : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C) (hC_open : IsOpen C) (h0C : (0 : Fin d → ℝ) ∈ C) :
    ∀ᵐ x ∂(volume.restrict A),
      Tendsto
        (fun r : ℝ ↦ μ.real (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Route correction: the workspace dependency for Exercise 13.1.5 is not a usable covering
  -- theorem, so we compare the translated dilates to enclosing balls and use Besicovitch directly.
  obtain ⟨R, hR_pos, hRC⟩ := hC_bounded.subset_closedBall_lt (0 : ℝ) (0 : Fin d → ℝ)
  filter_upwards [ae_tendsto_zero_scaled_closedBall_density_of_null (μ := μ) (A := A) hA_null hR_pos]
    with x hx
  -- Squeeze the translated-dilate mass between `0` and the enclosing closed-ball mass.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hx ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpow_nonneg : 0 ≤ r ^ d := pow_nonneg hr.le _
    exact div_nonneg (by positivity) hrpow_nonneg
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hsubset :=
      translatedSmul_subset_closedBall (C := C) hRC hr.le x
    have hsubset' :
        ({x} : Set (Fin d → ℝ)) + r • C ⊆ Metric.closedBall x (R * r) := by
      simpa [mul_comm] using hsubset
    have hmono :
        μ.real (({x} : Set (Fin d → ℝ)) + r • C) ≤ μ.real (Metric.closedBall x (R * r)) := by
      exact measureReal_mono hsubset' measure_closedBall_lt_top.ne
    have hrpow_nonneg : 0 ≤ r ^ d := pow_nonneg hr.le _
    exact div_le_div_of_nonneg_right hmono hrpow_nonneg

-- Proof sketch: use part (1) for the Stieltjes measure `F.measure` on `ℝ` with a one-dimensional
-- convex neighborhood of `0`; then combine the resulting density limit with the owner theorem
-- `StieltjesFunction.ae_hasDerivAt` to identify the derivative as `0` on the `F.measure`-null set.
/-- Exercise 13.1.6 (2): If `F` is the distribution function of a Stieltjes measure and `A` is
`F.measure`-null, then `F` has derivative `0` Lebesgue-almost everywhere on `A`. -/
theorem ae_hasDerivAt_zero_on_stieltjes_null_set
    (F : StieltjesFunction ℝ) {A : Set ℝ} (hA_null : F.measure A = 0) :
    ∀ᵐ x ∂(volume.restrict A), HasDerivAt F 0 x := by
  have hrestrict : volume.restrict A ≪ volume := Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hDeriv : ∀ᵐ x ∂(volume.restrict A), HasDerivAt F (F.measure.rnDeriv volume x).toReal x :=
    hrestrict.ae_le F.ae_hasDerivAt
  filter_upwards [hDeriv,
    ae_rnDeriv_eq_zero_on_restrict_of_null (μ := F.measure) (ν := volume) (A := A) hA_null]
    with x hx hzero
  -- Rewrite the derivative supplied by the owner theorem using the null-set Radon-Nikodym value.
  simpa [hzero] using hx
