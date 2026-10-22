/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private lemma continuous_uncurry_of_norm_bound₂ (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) {β : ℝ}
    (hβ : ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖) :
    Continuous (Function.uncurry fun x y ↦ T x y) := by
  -- Package the bilinear map as a continuous bilinear map with the same pointwise values.
  simpa [LinearMap.mkContinuous₂_apply] using
    (T.mkContinuous₂ β hβ).continuous₂

private lemma norm_bound₂_of_small_ball_control (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖T x y‖ ≤ 1) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  have hβ0 : 0 ≤ r⁻¹ * r⁻¹ := by positivity
  refine ⟨r⁻¹ * r⁻¹, hβ0, ?_⟩
  intro x y
  by_cases hx : x = 0
  · -- If the first variable vanishes, bilinearity forces the value to vanish.
    simp [hx]
  by_cases hy : y = 0
  · -- If the second variable vanishes, bilinearity again forces the value to vanish.
    simp [hy]
  have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let x' : X := (r / ‖x‖) • x
  let y' : Y := (r / ‖y‖) • y
  have hx'_norm : ‖x'‖ = r := by
    -- The normalization sends `x` to the sphere of radius `r`.
    calc
      ‖x'‖ = ‖(r / ‖x‖ : ℝ)‖ * ‖x‖ := by simp [x', norm_smul]
      _ = (r / ‖x‖) * ‖x‖ := by
        rw [Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg x))]
      _ = r := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hxnorm_pos.ne', mul_one]
  have hy'_norm : ‖y'‖ = r := by
    -- The same normalization argument works for `y`.
    calc
      ‖y'‖ = ‖(r / ‖y‖ : ℝ)‖ * ‖y‖ := by simp [y', norm_smul]
      _ = (r / ‖y‖) * ‖y‖ := by
        rw [Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg y))]
      _ = r := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hynorm_pos.ne', mul_one]
  have hx'_le : ‖x'‖ ≤ r := by simp [hx'_norm]
  have hy'_le : ‖y'‖ ≤ r := by simp [hy'_norm]
  have hxy'_bound : ‖T x' y'‖ ≤ 1 := hsmall x' y' hx'_le hy'_le
  have hx_scale : (‖x‖ / r) • x' = x := by
    -- Rescaling back recovers the original vector.
    calc
      (‖x‖ / r) • x' = ((‖x‖ / r) * (r / ‖x‖)) • x := by simp [x', smul_smul]
      _ = (1 : ℝ) • x := by
        congr 1
        field_simp [hxnorm_pos.ne', hr.ne']
      _ = x := one_smul ℝ x
  have hy_scale : (‖y‖ / r) • y' = y := by
    -- Rescaling back recovers the second vector as well.
    calc
      (‖y‖ / r) • y' = ((‖y‖ / r) * (r / ‖y‖)) • y := by simp [y', smul_smul]
      _ = (1 : ℝ) • y := by
        congr 1
        field_simp [hynorm_pos.ne', hr.ne']
      _ = y := one_smul ℝ y
  have hsmul₂ :
      ∀ (a b : ℝ) (u : X) (v : Y), T (a • u) (b • v) = (a * b) • T u v := by
    intro a b u v
    -- Bilinearity converts separate scalar rescalings into a single product scalar.
    rw [map_smul, map_smul]
    simp [smul_smul, mul_comm]
  have hxy_expand :
      T x y = ((‖x‖ / r) * (‖y‖ / r)) • T x' y' := by
    -- Bilinearity turns the rescaling into a scalar factor on the value.
    calc
      T x y = T ((‖x‖ / r) • x') ((‖y‖ / r) • y') := by rw [hx_scale, hy_scale]
      _ = ((‖x‖ / r) * (‖y‖ / r)) • T x' y' := by
        simpa using hsmul₂ (‖x‖ / r) (‖y‖ / r) x' y'
  have hcoeff_nonneg : 0 ≤ (‖x‖ / r) * (‖y‖ / r) := by
    exact mul_nonneg (div_nonneg (norm_nonneg x) hr.le) (div_nonneg (norm_nonneg y) hr.le)
  calc
    ‖T x y‖ = ‖((‖x‖ / r) * (‖y‖ / r)) • T x' y'‖ := by rw [hxy_expand]
    _ = ((‖x‖ / r) * (‖y‖ / r)) * ‖T x' y'‖ := by
      rw [norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
    _ ≤ ((‖x‖ / r) * (‖y‖ / r)) * 1 := by
      gcongr
    _ = (r⁻¹ * r⁻¹) * ‖x‖ * ‖y‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

private lemma norm_bound₂_of_continuousAt_zero_uncurry (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z)
    (hT : ContinuousAt (Function.uncurry fun x y ↦ T x y) (0, 0)) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hT) 1 zero_lt_one
  have hr : 0 < δ / 2 := by positivity
  refine norm_bound₂_of_small_ball_control T hr ?_
  intro x y hx hy
  have hpair_lt : dist (x, y) (0, 0) < δ := by
    -- Bounds on each coordinate control the product norm.
    rw [Prod.dist_eq]
    have hmax : max ‖x‖ ‖y‖ ≤ δ / 2 := max_le hx hy
    simpa [dist_eq_norm] using lt_of_le_of_lt hmax (by linarith)
  have hvalue_lt : dist (T x y) (T 0 0) < 1 := hδ hpair_lt
  -- Since a bilinear map sends `(0,0)` to `0`, the image lies in the unit ball.
  simpa [dist_eq_norm] using le_of_lt hvalue_lt

/-- Fact 2.21 in bundled form: a bilinear map is continuous exactly when it comes from a
`ContinuousLinearMap` with the same pointwise values. -/
theorem continuous_uncurry_iff_exists_continuousLinearMap (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    Continuous (Function.uncurry fun x y ↦ T x y) ↔
      ∃ S : X →L[ℝ] Y →L[ℝ] Z, ∀ x y, S x y = T x y := by
  constructor
  · intro hT
    obtain ⟨β, -, hβ⟩ := norm_bound₂_of_continuousAt_zero_uncurry T hT.continuousAt
    exact ⟨T.mkContinuous₂ β hβ, fun x y ↦ rfl⟩
  · rintro ⟨S, hS⟩
    simpa [Function.uncurry, hS] using S.continuous₂

/-- Fact 2.21: for a bilinear map already packaged as `T : X →ₗ[ℝ] Y →ₗ[ℝ] Z`, continuity of the
uncurried map is equivalent to the unbundled library predicate `IsBoundedBilinearMap`. This is a
thin bridge from the bundled `ContinuousLinearMap` criterion. -/
theorem isBoundedBilinearMap_uncurry_iff_continuous (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    IsBoundedBilinearMap ℝ (Function.uncurry fun x y ↦ T x y) ↔
      Continuous (Function.uncurry fun x y ↦ T x y) := by
  constructor
  · intro hT
    exact hT.continuous
  · intro hT
    rcases (continuous_uncurry_iff_exists_continuousLinearMap T).mp hT with ⟨S, hS⟩
    simpa [Function.uncurry, hS] using S.isBoundedBilinearMap

/-- The textbook norm estimate in Fact 2.21, presented in the library-facing `Function.uncurry`
form and with the canonical existential `∃ β` rather than a separate nonnegativity conjunct. -/
theorem continuous_uncurry_iff_exists_bound₂ (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    Continuous (Function.uncurry fun x y ↦ T x y) ↔
      ∃ β : ℝ, ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  constructor
  · intro hT
    obtain ⟨β, -, hβ⟩ := norm_bound₂_of_continuousAt_zero_uncurry T hT.continuousAt
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact continuous_uncurry_of_norm_bound₂ T hβ

-- Proof sketch: use the same unit-ball argument as in the global continuity criterion, noting
-- that bilinearity reduces continuity everywhere to continuity at the origin.
/-- Continuity of a bilinear map at the origin is equivalent to the existence of a global bilinear
norm bound. -/
theorem continuousAt_zero_uncurry_iff_exists_bound₂ (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    ContinuousAt (Function.uncurry fun x y ↦ T x y) (0, 0) ↔
      ∃ β : ℝ, ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  constructor
  · intro hT
    -- The converse engine is the local estimate obtained from continuity at the origin.
    obtain ⟨β, -, hβ⟩ := norm_bound₂_of_continuousAt_zero_uncurry T hT
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    -- The forward bound already gives global continuity, hence continuity at `(0,0)`.
    exact (continuous_uncurry_of_norm_bound₂ T hβ).continuousAt

end LinearMap
