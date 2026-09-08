module

public import Mathlib.Data.Real.Basic
public import ReasLib.Order.FiniteFamily

public section

universe u

/-- Lemma 6.7a (Master choice of one initial scale satisfying all smallness requirements):
a finite family of positive preliminary thresholds and the positive Hessian constant `K`
admit one positive scale below every threshold and below `(2 * K)⁻¹`. -/
theorem existsCommonInitialScale {ι : Type u} [Finite ι] (threshold : ι → ℝ) (K : ℝ)
    (h_threshold : ∀ i, 0 < threshold i) (hK : 0 < K) :
    ∃ ε₀ ∈ Set.Ioc 0 ((2 * K)⁻¹), ∀ i, ε₀ ≤ threshold i := by
  have hInvPos : 0 < (2 * K)⁻¹ := by
    exact inv_pos.mpr (mul_pos (by norm_num) hK)
  obtain ⟨ε₀, hε₀, hε₀Inv, hε₀Threshold⟩ :=
    Finite.exists_pos_le (2 * K)⁻¹ threshold hInvPos h_threshold
  exact ⟨ε₀, ⟨hε₀, hε₀Inv⟩, hε₀Threshold⟩
