/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProduct MinimalSingularValue

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}
  [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂] [FiniteDimensional 𝕜 E₂]

/-
 Lemma 4.4.6 lies in the Hilbert-space adjoint / singular-value domain.

Sampled owner-style declarations:
- `minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the chapter owner for the
  textbook least singular value;
- the recall-only owner `#check (0 < σ_min(A†))` in `Definition_4_4_6`, which already expresses
  dual nondegeneracy canonically;
- `ContinuousLinearMap.minimalSingularValue_mul_norm_le` in `Proposition_4_4_1`, the owner-derived
  lower bound attached to `σ_min`;
- `LinearMap.orthogonal_ker` and `LinearMap.finrank_range_adjoint` in mathlib, the finite-
  dimensional adjoint owners relating `ker(A)ᗮ`, `range(A†)`, and the shared rank of `A` and
  `A†`.

Source/core/bridge triage:
- source-facing: the textbook pointwise conclusion that each right-hand side `b` has a controlled
  preimage;
- core/canonical: the dual nondegeneracy proposition `0 < σ_min(A†)`;
- bridge/view: the canonical decomposition of a preimage into its `ker(A)` and `ker(A)ᗮ`
  components, with the latter identified with `range(A†)`.
-/

-- Proof sketch: Proposition 4.4.1 applied to `A†` makes `A†` injective, hence
-- `finrank range(A†) = finrank E₂`. By `LinearMap.finrank_range_adjoint`, the same holds for
-- `A`, so `A` is surjective. Decompose any preimage `x₀` of `b` as `y + z` with
-- `y ∈ ker(A)` and `z ∈ ker(A)ᗮ = range(A†)`. Writing `z = A† w`, the adjoint identity gives
-- `‖z‖² ≤ ‖A z‖ ‖w‖`, while Proposition 4.4.1 on `A†` bounds
-- `‖w‖ ≤ ‖z‖ / σ_min(A†)`. Cancelling one factor of `‖z‖` yields
-- `σ_min(A†) * ‖z‖ ≤ ‖A z‖ = ‖b‖`.
namespace ContinuousLinearMap

/-- Lemma 4.4.6: if the adjoint of a linear operator has positive minimal singular value, then
every right-hand side `b` admits a preimage whose norm is bounded by `‖b‖ / σ_min(A†)`. -/
theorem exists_preimage_norm_le_of_adjoint_minimalSingularValue_pos
    (A : E₁ →L[𝕜] E₂) (hA : 0 < σ_min(A†)) (b : E₂) :
    ∃ x : E₁, A x = b ∧ ‖x‖ ≤ ‖b‖ / σ_min(A†) := by
  have hAadj_inj : Function.Injective (A†) := by
    intro y₁ y₂ hEq
    have hsub : (A†) (y₁ - y₂) = 0 := by
      simp [map_sub, hEq]
    have hlower : σ_min(A†) * ‖y₁ - y₂‖ ≤ ‖(A†) (y₁ - y₂)‖ := by
      simpa using (A†).minimalSingularValue_mul_norm_le (y₁ - y₂)
    have hnorm_zero : ‖y₁ - y₂‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖y₁ - y₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      rw [hsub] at hlower
      have hlower' : σ_min(A†) * ‖y₁ - y₂‖ ≤ 0 := by
        simpa only [norm_zero] using hlower
      exact not_lt_of_ge hlower' (mul_pos hA hpos)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  have hfinrangeAdj : Module.finrank 𝕜 ↥((A†).toLinearMap.range) = Module.finrank 𝕜 E₂ :=
    LinearMap.finrank_range_of_inj hAadj_inj
  have hfinrange : Module.finrank 𝕜 ↥A.toLinearMap.range = Module.finrank 𝕜 E₂ := by
    calc
      Module.finrank 𝕜 ↥A.toLinearMap.range = Module.finrank 𝕜 ↥((A†).toLinearMap.range) := by
        simpa using (A.toLinearMap.finrank_range_adjoint).symm
      _ = Module.finrank 𝕜 E₂ := hfinrangeAdj
  have hsurj : Function.Surjective A :=
    (LinearMap.range_eq_top).mp <|
      by simpa using Submodule.eq_top_of_finrank_eq hfinrange
  obtain ⟨x₀, hx₀⟩ := hsurj b
  let Aₗ : E₁ →ₗ[𝕜] E₂ := A.toLinearMap
  let K : Submodule 𝕜 E₁ := A.toLinearMap.ker
  obtain ⟨y, hyK, z, hzK, hdecomp⟩ := K.exists_add_mem_mem_orthogonal x₀
  have hy0 : A y = 0 := by
    simpa [K, LinearMap.mem_ker] using hyK
  have hz_preimage : A z = b := by
    calc
      A z = A (y + z) := by simp [hy0]
      _ = b := by simpa [hdecomp] using hx₀
  have hz_range : z ∈ (A†).range := by
    have hz_range' : z ∈ Aₗ.adjoint.range := by
      rw [← Aₗ.orthogonal_ker]
      simpa [Aₗ, K] using hzK
    simpa [Aₗ] using hz_range'
  rcases hz_range with ⟨w, rfl⟩
  have hw_preimage : A ((A†) w) = b := by
    simpa using hz_preimage
  have hw_bound : ‖w‖ ≤ ‖(A†) w‖ / σ_min(A†) := by
    exact (le_div_iff₀ hA).2 <| by
      simpa [mul_comm] using (A†).minimalSingularValue_mul_norm_le w
  have hw_mul : σ_min(A†) * ‖w‖ ≤ ‖(A†) w‖ := by
    simpa [mul_comm] using (le_div_iff₀ hA).1 hw_bound
  have hzsq_le : ‖(A†) w‖ ^ 2 ≤ ‖A ((A†) w)‖ * ‖w‖ := by
    calc
      ‖(A†) w‖ ^ 2 = ‖inner 𝕜 ((A†) w) ((A†) w)‖ := by
        simp [inner_self_eq_norm_sq_to_K]
      _ = ‖inner 𝕜 (A ((A†) w)) w‖ := by rw [A.adjoint_inner_right]
      _ ≤ ‖A ((A†) w)‖ * ‖w‖ := norm_inner_le_norm _ _
  have hz_mul : σ_min(A†) * ‖(A†) w‖ ^ 2 ≤ ‖A ((A†) w)‖ * ‖(A†) w‖ := by
    calc
      σ_min(A†) * ‖(A†) w‖ ^ 2 ≤ σ_min(A†) * (‖A ((A†) w)‖ * ‖w‖) := by
        gcongr
      _ = ‖A ((A†) w)‖ * (σ_min(A†) * ‖w‖) := by ring
      _ ≤ ‖A ((A†) w)‖ * ‖(A†) w‖ := by gcongr
  have hz_bound : σ_min(A†) * ‖(A†) w‖ ≤ ‖A ((A†) w)‖ := by
    by_cases hwz : (A†) w = 0
    · simp [hwz]
    · have hwz_pos : 0 < ‖(A†) w‖ := norm_pos_iff.mpr hwz
      exact le_of_mul_le_mul_right
        (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hz_mul)
        hwz_pos
  refine ⟨(A†) w, hw_preimage, ?_⟩
  exact (le_div_iff₀ hA).2 <| by
    simpa [hw_preimage, mul_comm] using hz_bound

end ContinuousLinearMap
