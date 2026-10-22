/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Operations

section InexactNewtonMethod

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

-- Source/core/bridge triage:
-- * source-facing: local inverse-derivative regularity near a regular point in Chapter 3.6
-- * core/canonical: `ContDiffAt 𝕜 1 F xStar` and `ContinuousLinearMap.IsInvertible`
-- * bridge/view: the nearby invertibility and local inverse-norm bound for `fderiv 𝕜 F`
--
-- Semantic recall: mathlib already owns the inverse-map regularity API via
-- `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`, so this file keeps the Chapter 3.6
-- lemmas at that owner level instead of restating them through a neighborhood `ContDiffOn`
-- witness on a concrete Euclidean model.

/-- Helper for Chapter03 Lemma 3.6.1: an invertible continuous linear map lies in the neighborhood
of the range of continuous linear equivalences. -/
lemma equivRangeMemNhdsAtFDeriv {A : E →L[𝕜] E} (hA : A.IsInvertible) :
    Set.range (fun e : E ≃L[𝕜] E ↦ (e : E →L[𝕜] E)) ∈ nhds A := by
  -- Re-express the invertible map as a continuous linear equivalence and use its standard
  -- neighborhood in the ambient operator space.
  rcases hA with ⟨e, rfl⟩
  simpa using e.nhds

/-- Helper for Chapter03 Lemma 3.6.1: sufficiently near `xStar`, the derivative stays invertible. -/
lemma exists_isInvertible_fderiv_ball
    (F : E → E) (xStar : E)
    (h_contDiff : ContDiffAt 𝕜 1 F xStar)
    (h_invertible : (fderiv 𝕜 F xStar).IsInvertible) :
    ∃ δ > 0, ∀ ⦃y : E⦄, ‖y - xStar‖ < δ → (fderiv 𝕜 F y).IsInvertible := by
  -- Continuity of `fderiv` pulls the neighborhood of invertible operators back to a
  -- neighborhood of the base point.
  have h_fderiv : ContinuousAt (fderiv 𝕜 F) xStar :=
    h_contDiff.continuousAt_fderiv one_ne_zero
  have h_range :
      Set.range (fun e : E ≃L[𝕜] E ↦ (e : E →L[𝕜] E)) ∈ nhds (fderiv 𝕜 F xStar) :=
    equivRangeMemNhdsAtFDeriv h_invertible
  have h_near :
      {y : E | fderiv 𝕜 F y ∈ Set.range (fun e : E ≃L[𝕜] E ↦ (e : E →L[𝕜] E))} ∈ nhds xStar :=
    h_fderiv h_range
  rcases Metric.mem_nhds_iff.mp h_near with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hy_ball : y ∈ Metric.ball xStar δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  rcases hδsub hy_ball with ⟨e, he⟩
  -- Membership in the range produces a nearby continuous linear equivalence witnessing
  -- invertibility of the derivative at `y`.
  simpa [he] using (ContinuousLinearMap.isInvertible_equiv (f := e))

/-- Helper for Chapter03 Lemma 3.6.1: near `xStar`, the inverse derivatives admit a uniform
operator-norm bound. -/
lemma exists_inverseNormBound_fderiv_ball
    (F : E → E) (xStar : E)
    (h_contDiff : ContDiffAt 𝕜 1 F xStar)
    (h_invertible : (fderiv 𝕜 F xStar).IsInvertible) :
    ∃ δ > 0, ∀ ⦃y : E⦄, ‖y - xStar‖ < δ →
      ‖(fderiv 𝕜 F y).inverse‖ ≤ ‖(fderiv 𝕜 F xStar).inverse‖ + 1 := by
  -- First compose the continuity of `fderiv` with the inverse-map continuity at an invertible
  -- operator to control nearby inverse derivatives.
  have h_fderiv : ContinuousAt (fderiv 𝕜 F) xStar :=
    h_contDiff.continuousAt_fderiv one_ne_zero
  have h_inverse :
      ContinuousAt (fun A : E →L[𝕜] E ↦ A.inverse) (fderiv 𝕜 F xStar) := by
    exact (h_invertible.contDiffAt_map_inverse (𝕜 := 𝕜) (n := 1)).continuousAt
  have h_inverseFderiv : ContinuousAt (fun y : E ↦ (fderiv 𝕜 F y).inverse) xStar := by
    exact h_inverse.comp' h_fderiv
  have h_near :
      {y : E | ‖(fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse‖ < 1} ∈ nhds xStar := by
    simpa [Set.preimage, Metric.mem_ball, dist_eq_norm] using
      h_inverseFderiv (Metric.ball_mem_nhds ((fderiv 𝕜 F xStar).inverse) zero_lt_one)
  rcases Metric.mem_nhds_iff.mp h_near with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hy_ball : y ∈ Metric.ball xStar δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hclose :
      ‖(fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse‖ < 1 := hδsub hy_ball
  have htriangle :
      ‖(fderiv 𝕜 F y).inverse‖ ≤
        ‖(fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse‖ +
          ‖(fderiv 𝕜 F xStar).inverse‖ := by
    -- Rewrite the target inverse as a sum with the base inverse, then apply the triangle
    -- inequality in the operator norm.
    calc
      ‖(fderiv 𝕜 F y).inverse‖ =
          ‖((fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse) +
              (fderiv 𝕜 F xStar).inverse‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖(fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse‖ +
            ‖(fderiv 𝕜 F xStar).inverse‖ :=
          norm_add_le _ _
  have hclose_le :
      ‖(fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse‖ ≤ 1 :=
    le_of_lt hclose
  have hsum :
      ‖(fderiv 𝕜 F y).inverse - (fderiv 𝕜 F xStar).inverse‖ +
          ‖(fderiv 𝕜 F xStar).inverse‖ ≤
        1 + ‖(fderiv 𝕜 F xStar).inverse‖ := by
    -- Add the base inverse norm to both sides of the distance estimate.
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hclose_le ‖(fderiv 𝕜 F xStar).inverse‖
  have hbound' :
      ‖(fderiv 𝕜 F y).inverse‖ ≤ 1 + ‖(fderiv 𝕜 F xStar).inverse‖ :=
    le_trans htriangle hsum
  simpa [add_comm] using hbound'

/-- Chapter03 Lemma 3.6.1 (1): if `F` is `C¹` at `xStar` and `fderiv 𝕜 F xStar` is invertible,
then the nearby derivatives `fderiv 𝕜 F y` remain invertible and their inverses are uniformly
bounded in operator norm. -/
theorem exists_isInvertible_fderiv_near
    (F : E → E) (xStar : E)
    (h_contDiff : ContDiffAt 𝕜 1 F xStar)
    (h_invertible : (fderiv 𝕜 F xStar).IsInvertible) :
    ∃ δ > 0, ∃ ξ > 0, ∀ ⦃y : E⦄, ‖y - xStar‖ < δ →
      (fderiv 𝕜 F y).IsInvertible ∧ ‖(fderiv 𝕜 F y).inverse‖ ≤ ξ := by
  -- Combine the local invertibility and local inverse-norm estimates on a common smaller ball.
  rcases exists_isInvertible_fderiv_ball F xStar h_contDiff h_invertible with ⟨δ₁, hδ₁, hinv⟩
  rcases exists_inverseNormBound_fderiv_ball F xStar h_contDiff h_invertible with
    ⟨δ₂, hδ₂, hbound⟩
  let ξ : ℝ := ‖(fderiv 𝕜 F xStar).inverse‖ + 1
  have hξ : 0 < ξ := by
    exact add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ξ, hξ, ?_⟩
  intro y hy
  have hy₁ : ‖y - xStar‖ < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy₂ : ‖y - xStar‖ < δ₂ := lt_of_lt_of_le hy (min_le_right _ _)
  -- The smaller radius inherits both conclusions from the two helper lemmas.
  exact ⟨hinv hy₁, by simpa [ξ] using hbound hy₂⟩

/-- Chapter03 Lemma 3.6.1 (2): under the same hypotheses, the inverse derivative map
`y ↦ (fderiv 𝕜 F y).inverse` is continuous at `xStar`. -/
theorem continuousAt_inverse_fderiv
    (F : E → E) (xStar : E)
    (h_contDiff : ContDiffAt 𝕜 1 F xStar)
    (h_invertible : (fderiv 𝕜 F xStar).IsInvertible) :
    ContinuousAt (fun y : E ↦ (fderiv 𝕜 F y).inverse) xStar := by
  -- Compose the continuity of `fderiv` with the inverse-map continuity at the invertible base
  -- derivative.
  have h_fderiv : ContinuousAt (fderiv 𝕜 F) xStar :=
    h_contDiff.continuousAt_fderiv one_ne_zero
  have h_inverse :
      ContinuousAt (fun A : E →L[𝕜] E ↦ A.inverse) (fderiv 𝕜 F xStar) := by
    exact (h_invertible.contDiffAt_map_inverse (𝕜 := 𝕜) (n := 1)).continuousAt
  exact h_inverse.comp' h_fderiv

end InexactNewtonMethod
