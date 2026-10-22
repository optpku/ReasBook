/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Theorem_9_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set

universe u

namespace ERealFunction

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] [NeZero μ]

omit [NeZero μ] in
/-- Helper for Proposition 9.24: composing an integrable real-valued function with a continuous
affine self-map of `ℝ` preserves integrability. -/
lemma continuousAffineMap_comp_integrable_real
    (g : ℝ →ᴬ[ℝ] ℝ) {x : Ω → ℝ} (hx : Integrable x μ) :
    Integrable (fun ω ↦ g (x ω)) μ := by
  -- Decompose the affine map into its linear part plus a constant, then use stability of
  -- integrability under linear composition and addition of a constant.
  have hdecomp : ∀ t : ℝ, g t = g.contLinear t + g 0 := by
    intro t
    simpa [Pi.add_apply, Function.const_apply] using congrFun (ContinuousAffineMap.decomp g) t
  have hlinear : Integrable (fun ω ↦ g.contLinear (x ω)) μ :=
    g.contLinear.integrable_comp hx
  have hconst : Integrable (fun _ : Ω ↦ g 0) μ :=
    integrable_const (g 0)
  refine (hlinear.add hconst).congr ?_
  filter_upwards with ω
  simpa using (hdecomp (x ω)).symm

/-- Helper for Proposition 9.24: a continuous affine self-map of `ℝ` sends the average of an
integrable function to the average of its composition. -/
lemma continuousAffineMap_map_average_real
    (g : ℝ →ᴬ[ℝ] ℝ) {x : Ω → ℝ} (hx : Integrable x μ) :
    ⨍ ω, g (x ω) ∂μ = g (⨍ ω, x ω ∂μ) := by
  -- First handle the linear part of the affine map by commuting it with integration.
  have hlinear_average :
      ⨍ ω, g.contLinear (x ω) ∂μ = g.contLinear (⨍ ω, x ω ∂μ) := by
    calc
      ⨍ ω, g.contLinear (x ω) ∂μ
          = (μ.real univ)⁻¹ • ∫ ω, g.contLinear (x ω) ∂μ := by
              rw [MeasureTheory.average_eq]
      _ = (μ.real univ)⁻¹ • g.contLinear (∫ ω, x ω ∂μ) := by
            rw [ContinuousLinearMap.integral_comp_comm _ hx]
      _ = g.contLinear ((μ.real univ)⁻¹ • ∫ ω, x ω ∂μ) := by
            rw [← map_smul]
      _ = g.contLinear (⨍ ω, x ω ∂μ) := by
            rw [MeasureTheory.average_eq]
  have hdecomp : ∀ t : ℝ, g t = g.contLinear t + g 0 := by
    intro t
    simpa [Pi.add_apply, Function.const_apply] using congrFun (ContinuousAffineMap.decomp g) t
  -- Then rewrite both sides using the affine decomposition and the constant-average identity.
  calc
    ⨍ ω, g (x ω) ∂μ
        = ⨍ ω, (g.contLinear (x ω) + g 0) ∂μ := by
            apply MeasureTheory.average_congr
            filter_upwards with ω
            rw [hdecomp]
    _ = (μ.real univ)⁻¹ • ∫ ω, (g.contLinear (x ω) + g 0) ∂μ := by
          rw [MeasureTheory.average_eq]
    _ = (μ.real univ)⁻¹ •
          (∫ ω, g.contLinear (x ω) ∂μ + ∫ ω, g 0 ∂μ) := by
            rw [integral_add (g.contLinear.integrable_comp hx) (integrable_const (g 0))]
    _ = (μ.real univ)⁻¹ • ∫ ω, g.contLinear (x ω) ∂μ +
          (μ.real univ)⁻¹ • ∫ ω, g 0 ∂μ := by
            rw [smul_add]
    _ = ⨍ ω, g.contLinear (x ω) ∂μ + (μ.real univ)⁻¹ • ∫ ω, g 0 ∂μ := by
          rw [← MeasureTheory.average_eq]
    _ = g.contLinear (⨍ ω, x ω ∂μ) + (μ.real univ)⁻¹ • ∫ ω, g 0 ∂μ := by
          rw [hlinear_average]
    _ = g.contLinear (⨍ ω, x ω ∂μ) + g 0 := by
          have hμpos : 0 < μ.real univ :=
            ENNReal.toReal_pos ((Measure.measure_univ_ne_zero).2 (NeZero.ne μ))
              (measure_ne_top μ univ)
          calc
            g.contLinear (⨍ ω, x ω ∂μ) + (μ.real univ)⁻¹ • ∫ ω, g 0 ∂μ
                = g.contLinear (⨍ ω, x ω ∂μ) + ((μ.real univ)⁻¹ * μ.real univ) * g 0 := by
                    rw [integral_const, smul_eq_mul, smul_eq_mul]
                    ring
            _ = g.contLinear (⨍ ω, x ω ∂μ) + g 0 := by
                  rw [inv_mul_cancel₀ hμpos.ne', one_mul]
    _ = g (⨍ ω, x ω ∂μ) := by
          exact (hdecomp _).symm

omit [IsFiniteMeasure μ] [NeZero μ] in
/-- Helper for Proposition 9.24: an affine EReal-valued minorant becomes a real-valued pointwise
minorant on points where the `Γ₀` function is finite. -/
lemma ae_le_toReal_of_minorant_and_ae_mem_effectiveDomain
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (g : ℝ →ᴬ[ℝ] ℝ) {x : Ω → ℝ}
    (hminorant : ∀ y : ℝ, ((g y : ℝ) : EReal) ≤ (φ y : EReal))
    (hφx_mem : ∀ᵐ ω ∂μ, x ω ∈ effectiveDomain φ) :
    ∀ᵐ ω ∂μ, g (x ω) ≤ (φ (x ω) : EReal).toReal := by
  -- On the effective domain, `φ (x ω)` is finite, so the EReal inequality can be converted back
  -- to an inequality in `ℝ`.
  filter_upwards [hφx_mem] with ω hω
  have htop : (φ (x ω) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hω)
  have hbot : (φ (x ω) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ (x ω) : EReal) from (φ (x ω)).2)
  have hcast : ((g (x ω) : ℝ) : EReal) ≤ (((φ (x ω) : EReal).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal htop hbot] using hminorant (x ω)
  exact_mod_cast hcast

-- Proof sketch: apply
-- `exists_supporting_affine_minorant_of_mem_interior_effectiveDomain_of_mem_gammaZero`
-- at the average point `⨍ ω, x ω ∂μ` to obtain a supporting affine minorant of `φ`, evaluate it
-- along `x`, and integrate the resulting pointwise inequality. The average of the affine term
-- collapses to `φ` at the average because the linear part has mean zero by definition of
-- `MeasureTheory.average`.
/-- Proposition 9.24: Jensen's inequality for a `Γ₀(ℝ)` function over a finite nonzero measure
space. If `x` is integrable, `x` takes values in `effectiveDomain φ` almost everywhere,
`EReal.toReal ∘ φ ∘ x` is integrable, and the average value of `x` lies in
`interior (effectiveDomain φ)`, then the real-valued representative of `φ` at that average is
bounded above by the average of the real-valued representative along `x`. -/
theorem jensen_inequality_of_mem_gammaZero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (x : Ω → ℝ) (hx : Integrable x μ)
    (hφx_mem : ∀ᵐ ω ∂μ, x ω ∈ effectiveDomain φ)
    (hφx_toReal : Integrable (fun ω ↦ (φ (x ω) : EReal).toReal) μ)
    (h_average_mem : (⨍ ω, x ω ∂μ) ∈ interior (effectiveDomain φ)) :
    (φ (⨍ ω, x ω ∂μ) : EReal).toReal ≤ ⨍ ω, (φ (x ω) : EReal).toReal ∂μ := by
  -- Apply Theorem 9.23 at the average point to obtain the supporting affine minorant from the
  -- source proof.
  obtain ⟨g, hg_average, hminorant⟩ :=
    exists_supporting_affine_minorant_of_mem_interior_effectiveDomain_of_mem_gammaZero
      (f := φ) hφ h_average_mem
  -- Compose the supporting affine map with `x` and convert the EReal support inequality to `ℝ`.
  have hgx_int : Integrable (fun ω ↦ g (x ω)) μ :=
    continuousAffineMap_comp_integrable_real (μ := μ) g hx
  have hpointwise :
      ∀ᵐ ω ∂μ, g (x ω) ≤ (φ (x ω) : EReal).toReal :=
    ae_le_toReal_of_minorant_and_ae_mem_effectiveDomain (μ := μ) φ g hminorant hφx_mem
  -- Integrating the pointwise inequality gives the average comparison after rewriting the affine
  -- average.
  have hintegral_le :
      ∫ ω, g (x ω) ∂μ ≤ ∫ ω, (φ (x ω) : EReal).toReal ∂μ :=
    integral_mono_ae hgx_int hφx_toReal hpointwise
  have haverage_le :
      ⨍ ω, g (x ω) ∂μ ≤ ⨍ ω, (φ (x ω) : EReal).toReal ∂μ := by
    rw [MeasureTheory.average_eq, MeasureTheory.average_eq, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hintegral_le (inv_nonneg.mpr ENNReal.toReal_nonneg)
  calc
    (φ (⨍ ω, x ω ∂μ) : EReal).toReal = g (⨍ ω, x ω ∂μ) := by
      simpa using hg_average.symm
    _ = ⨍ ω, g (x ω) ∂μ := by
      simpa using (continuousAffineMap_map_average_real (μ := μ) g hx).symm
    _ ≤ ⨍ ω, (φ (x ω) : EReal).toReal ∂μ := haverage_le

end ERealFunction
