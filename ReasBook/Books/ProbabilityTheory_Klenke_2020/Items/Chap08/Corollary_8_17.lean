/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ProbabilityTheory InnerProductSpace
open MeasureTheory
open MeasureTheory.L2

universe u

variable {Ω : Type u} {m0 m : MeasurableSpace Ω} {μ : Measure[m0] Ω}

private lemma lp_norm_sq_eq_integral_sq (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = ⟪f, f⟫_ℝ := by simp
    _ = ∫ ω, ⟪f ω, f ω⟫_ℝ ∂μ := by rw [inner_def]
    _ = ∫ ω, (f ω) ^ 2 ∂μ := by
      simp [sq]

private lemma lp_sub_norm_sq_eq_integral_sq {f g : Lp ℝ 2 μ} {F G : Ω → ℝ}
    (hf : f =ᵐ[μ] F) (hg : g =ᵐ[μ] G) :
    ‖f - g‖ ^ 2 = ∫ ω, (F ω - G ω) ^ 2 ∂μ := by
  calc
    ‖f - g‖ ^ 2 = ∫ ω, ((f - g) ω) ^ 2 ∂μ := by
      simpa using lp_norm_sq_eq_integral_sq (f - g)
    _ = ∫ ω, (F ω - G ω) ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hf, hg, Lp.coeFn_sub f g] with ω hfω hgω hsub
      rw [hsub, Pi.sub_apply, hfω, hgω]

-- Proof sketch: pass to `Lp ℝ 2 μ`, where `condExpL2` is the orthogonal projection onto the
-- `m`-measurable subspace `lpMeas`. Apply the Pythagorean theorem to `X₂ - Y₂`, then translate
-- the three squared norms back to integrals of squared pointwise errors using `L2.inner_def`.
/-- Corollary 8.17: for any `m`-measurable `L²` random variable `Y`, the squared error decomposes
as the optimal conditional-expectation error plus the squared `L²`-distance from `Y` to
`μ[X | m]`. In particular, `μ[X | m]` is the unique mean-square minimizer up to almost-everywhere
equality. -/
theorem condExp_sq_error_decomposition [IsFiniteMeasure μ] (hm : m ≤ m0) {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hY_meas : Measurable[m] Y) :
    ∫ ω, (X ω - Y ω) ^ 2 ∂μ =
      ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ + ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ := by
  let _ : MeasurableSpace Ω := m0
  let _ : Fact (m ≤ m0) := ⟨hm⟩
  let U : Submodule ℝ (Lp ℝ 2 μ) := lpMeas ℝ ℝ m 2 μ
  let _ : CompleteSpace U := by infer_instance
  let _ : U.HasOrthogonalProjection := by infer_instance
  let X₂ : Lp ℝ 2 μ := hX.toLp X
  let Y₂ : Lp ℝ 2 μ := hY.toLp Y
  let Z₂ : Lp ℝ 2 μ := condExpL2 ℝ ℝ hm X₂
  have hY_mem : Y₂ ∈ U := by
    refine mem_lpMeas_iff_aestronglyMeasurable.mpr ?_
    exact hY_meas.aestronglyMeasurable.congr <| by simpa [Y₂] using hY.coeFn_toLp.symm
  have hZ_ae : Z₂ =ᵐ[μ] μ[X | m] := by
    simpa [X₂, Z₂] using hX.condExpL2_ae_eq_condExp hm
  have hproj_sub : U.starProjection (X₂ - Y₂) = Z₂ - Y₂ := by
    rw [map_sub]
    rw [show U.starProjection X₂ = Z₂ by rfl]
    congr 1
    exact U.starProjection_eq_self_iff.mpr hY_mem
  have horth_sub : Uᗮ.starProjection (X₂ - Y₂) = X₂ - Z₂ := by
    rw [U.starProjection_orthogonal']
    change (X₂ - Y₂) - U.starProjection (X₂ - Y₂) = X₂ - Z₂
    rw [hproj_sub]
    abel
  have hpyth :
      ‖X₂ - Y₂‖ ^ 2 = ‖Z₂ - Y₂‖ ^ 2 + ‖X₂ - Z₂‖ ^ 2 := by
    simpa [hproj_sub, horth_sub, add_comm] using
      U.norm_sq_eq_add_norm_sq_starProjection (X₂ - Y₂)
  calc
    ∫ ω, (X ω - Y ω) ^ 2 ∂μ = ‖X₂ - Y₂‖ ^ 2 := by
      simpa [X₂, Y₂] using (lp_sub_norm_sq_eq_integral_sq hX.coeFn_toLp hY.coeFn_toLp).symm
    _ = ‖X₂ - Z₂‖ ^ 2 + ‖Z₂ - Y₂‖ ^ 2 := by
      rw [hpyth, add_comm]
    _ = ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ + ‖Z₂ - Y₂‖ ^ 2 := by
      congr 1
      simpa [X₂] using lp_sub_norm_sq_eq_integral_sq hX.coeFn_toLp hZ_ae
    _ = ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ + ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ := by
      congr 1
      simpa [Y₂] using lp_sub_norm_sq_eq_integral_sq hZ_ae hY.coeFn_toLp

/-- Corollary 8.17, inequality form: among `m`-measurable `L²` random variables, the conditional
expectation minimizes the mean squared error. -/
theorem condExp_sq_error_le [IsFiniteMeasure μ] (hm : m ≤ m0) {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hY_meas : Measurable[m] Y) :
    ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂μ := by
  rw [condExp_sq_error_decomposition hm hX hY hY_meas]
  have hnonneg : 0 ≤ ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ := by
    exact integral_nonneg fun ω ↦ sq_nonneg _
  linarith

/-- Corollary 8.17, equality characterization: equality in the mean-square minimization holds
exactly when `Y` is almost everywhere equal to the conditional expectation. -/
theorem condExp_sq_error_eq_iff [IsFiniteMeasure μ] (hm : m ≤ m0) {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hY_meas : Measurable[m] Y) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂μ = ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ) ↔
      Y =ᵐ[μ] μ[X | m] := by
  have hcond : MemLp (μ[X | m]) 2 μ := hX.condExp
  have hdiff : MemLp (μ[X | m] - Y) 2 μ := hcond.sub hY
  have hdecomp := condExp_sq_error_decomposition hm hX hY hY_meas
  have hsq_zero :
      (∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ = 0) ↔
        (fun ω ↦ (μ[X | m] ω - Y ω) ^ 2) =ᵐ[μ] 0 := by
    refine integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg ((μ[X | m] - Y) ω)) ?_
    simpa using hdiff.integrable_sq
  constructor
  · intro h
    have hs : ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ = 0 := by
      linarith [hdecomp, h]
    have hsq : (fun ω ↦ (μ[X | m] ω - Y ω) ^ 2) =ᵐ[μ] 0 := hsq_zero.mp hs
    filter_upwards [hsq] with ω hω
    have hzero : μ[X | m] ω - Y ω = 0 := by
      simpa [sq] using hω
    linarith
  · intro h
    have hsq : (fun ω ↦ (μ[X | m] ω - Y ω) ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [h] with ω hω
      simp [hω]
    have hs : ∫ ω, (μ[X | m] ω - Y ω) ^ 2 ∂μ = 0 := hsq_zero.mpr hsq
    linarith [hdecomp, hs]

/-- Bundled textbook formulation of Corollary 8.17. The stronger identity is
`condExp_sq_error_decomposition`; this theorem packages its inequality and equality consequences in
the original textbook style. -/
theorem condExp_sq_error_le_sq_error_iff [IsFiniteMeasure μ] (hm : m ≤ m0) {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hY_meas : Measurable[m] Y) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂μ) ≥ ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ ∧
      ((∫ ω, (X ω - Y ω) ^ 2 ∂μ) = ∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ ↔
        Y =ᵐ[μ] μ[X | m]) := by
  refine ⟨condExp_sq_error_le hm hX hY hY_meas, condExp_sq_error_eq_iff hm hX hY hY_meas⟩
