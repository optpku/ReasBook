/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_6_7a_Master_choice_of_one_initial_scale_satisfying_all_smallness_requireme.lean
-/

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
