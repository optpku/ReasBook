/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Gradient Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 1.4.10 is refined here by the textbook secant-limit proof.

Source/core/bridge triage:
- source-facing: orthogonality of a tangent direction to the level set of a differentiable function
- core/canonical: the affine-approximation little-o remainder at a differentiability point
- bridge/view: the normalized-secant characterization of `tangentDirectionsToLevelSet`

Primary domain:
- first-order orthogonality of level-set tangent directions in a real inner-product space

Relevant owner-style declarations sampled before refinement:
- `hasGradientAt_iff_isLittleO`
- `mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit`
- `IsLittleO.comp_tendsto`
- `IsLittleO.tendsto_div_nhds_zero`
-/

-- Route correction: follow the textbook affine-expansion proof along a level-set secant sequence,
-- rather than the owner-side local-extremum shortcut through the tangent cone.

/-- Helper for Lemma 1.4.10: the affine-approximation remainder becomes negligible after
normalizing by the secant length along a sequence converging to `xbar`. -/
private lemma affine_remainder_ratio_tendsto_zero_along_level_set_sequence
    {f : E → ℝ} {xbar g : E} {y : ℕ → E}
    (hrem : (fun z ↦ f z - (f xbar + inner ℝ g (z - xbar))) =o[𝓝 xbar] fun z ↦ ‖z - xbar‖)
    (hy : Tendsto y atTop (𝓝 xbar)) :
    Tendsto (fun k ↦ (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖)
      atTop (𝓝 0) := by
  -- Pull the little-o remainder along the convergent secant sequence and immediately translate it
  -- into convergence of the normalized scalar remainder.
  simpa [Function.comp] using (hrem.comp_tendsto hy).tendsto_div_nhds_zero

/-- Helper for Lemma 1.4.10: on the level set, dividing the first-order expansion by the secant
length yields the normalized inner-product identity from the textbook proof. -/
private lemma level_set_secant_inner_add_remainder_eq_zero
    {f : E → ℝ} {xbar g : E} {y : ℕ → E}
    (hy_ne : ∀ k, y k ≠ xbar)
    (hy_level : ∀ k, f (y k) = f xbar) :
    ∀ k,
      inner ℝ g (‖y k - xbar‖⁻¹ • (y k - xbar)) +
        (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ = 0 := by
  intro k
  have hnorm_ne : ‖y k - xbar‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hy_ne k))
  -- Rewrite the exact level-set equality as the vanishing of the affine term plus remainder.
  have hsum :
      inner ℝ g (y k - xbar) +
          (f (y k) - (f xbar + inner ℝ g (y k - xbar))) = 0 := by
    linarith [hy_level k]
  -- Rewrite the target as the divided form of `hsum`.
  have htarget :
      inner ℝ g (‖y k - xbar‖⁻¹ • (y k - xbar)) +
        (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ =
      (inner ℝ g (y k - xbar) +
          (f (y k) - (f xbar + inner ℝ g (y k - xbar)))) / ‖y k - xbar‖ := by
    calc
      inner ℝ g (‖y k - xbar‖⁻¹ • (y k - xbar)) +
          (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ =
          ‖y k - xbar‖⁻¹ * inner ℝ g (y k - xbar) +
            (f (y k) - (f xbar + inner ℝ g (y k - xbar))) / ‖y k - xbar‖ := by
        rw [inner_smul_right]
      _ = (inner ℝ g (y k - xbar) +
            (f (y k) - (f xbar + inner ℝ g (y k - xbar)))) / ‖y k - xbar‖ := by
        field_simp [hnorm_ne, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [htarget]
  simp [hsum]

/-- Helper for Lemma 1.4.10: a normalized secant limit along the level set forces orthogonality
with the gradient at the base point. -/
private lemma inner_gradient_eq_zero_of_level_set_secant_limit
    {f : E → ℝ} {xbar s : E} (hf : DifferentiableAt ℝ f xbar)
    {y : ℕ → E} (hy : Tendsto y atTop (𝓝 xbar))
    (hy_ne : ∀ k, y k ≠ xbar) (hy_level : ∀ k, f (y k) = f xbar)
    (hy_secant : Tendsto (fun k ↦ ‖y k - xbar‖⁻¹ • (y k - xbar)) atTop (𝓝 s)) :
    inner ℝ (∇ f xbar) s = 0 := by
  -- Translate differentiability into the textbook affine expansion with little-o remainder.
  have hrem :
      (fun z ↦ f z - (f xbar + inner ℝ (∇ f xbar) (z - xbar))) =o[𝓝 xbar]
        fun z ↦ ‖z - xbar‖ := by
    simpa [Asymptotics.isLittleO_norm_right, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using
        (hasGradientAt_iff_isLittleO :
          HasGradientAt f (∇ f xbar) xbar ↔
            (fun z : E ↦ f z - f xbar - inner ℝ (∇ f xbar) (z - xbar)) =o[𝓝 xbar]
              fun z ↦ z - xbar).mp hf.hasGradientAt
  -- The remainder term disappears after normalization along the chosen sequence.
  have hratio :=
    affine_remainder_ratio_tendsto_zero_along_level_set_sequence hrem hy
  -- The normalized inner-product term converges by continuity of the inner product.
  have hinner :
      Tendsto (fun k ↦ inner ℝ (∇ f xbar) (‖y k - xbar‖⁻¹ • (y k - xbar)))
        atTop (𝓝 (inner ℝ (∇ f xbar) s)) := by
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp hy_secant
  have hsum :
      Tendsto
        (fun k ↦
          inner ℝ (∇ f xbar) (‖y k - xbar‖⁻¹ • (y k - xbar)) +
            (f (y k) - (f xbar + inner ℝ (∇ f xbar) (y k - xbar))) / ‖y k - xbar‖)
        atTop (𝓝 (inner ℝ (∇ f xbar) s + 0)) :=
    hinner.add hratio
  -- The divided identity holds at every index, so the same sequence also converges to `0`.
  have hsum_zero :
      Tendsto
        (fun k ↦
          inner ℝ (∇ f xbar) (‖y k - xbar‖⁻¹ • (y k - xbar)) +
            (f (y k) - (f xbar + inner ℝ (∇ f xbar) (y k - xbar))) / ‖y k - xbar‖)
        atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Eventually.of_forall fun k ↦
      (level_set_secant_inner_add_remainder_eq_zero hy_ne hy_level k).symm
  have hlimit : inner ℝ (∇ f xbar) s + 0 = 0 :=
    tendsto_nhds_unique hsum hsum_zero
  simpa using hlimit

/-- Lemma 1.4.10: if `f` is differentiable at `xbar`, then every tangent direction to the level
set of `f` at `xbar` is orthogonal to the gradient at `xbar`. -/
theorem inner_gradient_eq_zero_of_mem_tangentDirectionsToLevelSet
    {f : E → ℝ} {xbar s : E} (hf : DifferentiableAt ℝ f xbar)
    (hs : s ∈ tangentDirectionsToLevelSet f xbar) :
    inner ℝ (∇ f xbar) s = 0 := by
  -- Unpack the tangent-direction hypothesis into the normalized-secant sequence from
  -- Definition 1.4.9.
  rcases mem_tangentDirectionsToLevelSet_iff_exists_level_set_secant_limit.mp hs with
    ⟨y, hy, hy_ne, hy_level, hy_secant⟩
  -- The sequence-form source proof is now exactly the structural helper above.
  apply inner_gradient_eq_zero_of_level_set_secant_limit hf hy hy_ne
  · intro k
    simpa using hy_level k
  · exact hy_secant
