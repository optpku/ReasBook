/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace LinearMap

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private lemma continuousAt_zero_of_exists_continuousAt
    (T : X →ₗ[ℝ] Y) (hT : ∃ x₀ : X, ContinuousAt T x₀) : ContinuousAt T 0 := by
  rcases hT with ⟨x₀, hx₀⟩
  have hshift : ContinuousAt (fun z : X ↦ T (x₀ + z) - T x₀) 0 := by
    have hTx₀ : ContinuousAt T (x₀ + 0) := by
      simpa using hx₀
    exact (hTx₀.comp <| continuousAt_const.add continuousAt_id).sub continuousAt_const
  simpa [LinearMap.map_add] using hshift

/-- A real linear map is continuous if and only if it is globally Lipschitz. -/
theorem continuous_iff_exists_lipschitzWith (T : X →ₗ[ℝ] Y) :
    Continuous T ↔ ∃ K : NNReal, LipschitzWith K T := by
  constructor
  · intro hT
    let T' : X →L[ℝ] Y := ⟨T, hT⟩
    refine ⟨‖T'‖₊, ?_⟩
    simpa [T'] using T'.lipschitz
  · rintro ⟨K, hK⟩
    exact hK.continuous

end LinearMap

/-- Fact 2.20 in the textbook phrasing: a real linear map is continuous at some point if and only
if it is globally Lipschitz. -/
theorem linearMap_continuousAt_some_iff_exists_lipschitz_constant
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →ₗ[ℝ] Y) :
    (∃ x₀ : X, ContinuousAt T x₀) ↔ ∃ K : NNReal, LipschitzWith K T := by
  constructor
  · intro hT
    exact (LinearMap.continuous_iff_exists_lipschitzWith T).mp <|
      continuous_of_continuousAt_zero T <|
        LinearMap.continuousAt_zero_of_exists_continuousAt T hT
  · intro hT
    exact ⟨0, (LinearMap.continuous_iff_exists_lipschitzWith T).mpr hT |>.continuousAt⟩

/-- Fact 2.20 in the textbook norm-inequality form. -/
theorem linearMap_continuousAt_some_iff_exists_nonneg_real_lipschitz_constant
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →ₗ[ℝ] Y) :
    (∃ x₀ : X, ContinuousAt T x₀) ↔
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : X, ‖T x - T y‖ ≤ L * ‖x - y‖ := by
  rw [linearMap_continuousAt_some_iff_exists_lipschitz_constant]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, K.2, ?_⟩
    intro x y
    simpa [dist_eq_norm] using hK.dist_le_mul x y
  · rintro ⟨L, hL, hT⟩
    refine ⟨Real.toNNReal L, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa [dist_eq_norm, Real.toNNReal_of_nonneg hL] using hT x y
