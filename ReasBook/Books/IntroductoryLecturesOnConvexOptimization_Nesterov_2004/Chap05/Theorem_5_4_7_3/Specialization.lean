/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_3.Prereqs

noncomputable section

attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance 10000] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance 10000] Chap05RealProdL2.instCompleteSpaceRealProdProd

namespace Nesterov.Chap05.Theorem_5_4_7_3.Specialization

/-- Helper for Theorem 5.4.7.3: restate the orthant logarithmic barrier in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem powerConeBarrierIsTwoSelfConcordantBarrierL2 :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior powerConeQ1)
      (2 : NNReal)
      powerConeBarrier := by
  -- The orthant barrier theorem already matches the current geometry once the owner is pinned.
  simpa using power_cone_barrier_is_two_self_concordant_barrier

/-- Helper for Theorem 5.4.7.3: restate the `β = 1` compatibility witness in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem powerConeGeometricMeanIsOneCompatibleWithPowerConeBarrierL2
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    @IsBetaCompatibleWith
      (ℝ × ℝ)
      ℝ
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      powerConeBarrier
      (1 : NNReal)
      (powerConeGeometricMean α) := by
  -- The compatibility theorem already has the right mathematics; this wrapper only pins the
  -- ambient geometry consumed by the specialization boundary.
  exact powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier hα₀ hα₁

-- Proof sketch: keep the heavy witness layer in `Prereqs.lean`, then specialize the generic
-- cone-composition theorem once and unfold the raw outer owner alias at the boundary.
/-- Helper for Theorem 5.4.7.3: the generic cone-composition theorem specializes to the
power-cone data once the expensive prerequisite witnesses are imported from the theorem-local
support file. -/
theorem coneCompositionBarrier_powerConeQ2Raw_isSelfConcordantBarrierOnWith
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          (powerConeGeometricMean α)
          powerConeQ2))
      ((2 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      (coneCompositionBarrier
        powerConeBarrier
        ((sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0) +
          (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0))
        (powerConeGeometricMean α)
        1) := by
  have hF :
      IsSelfConcordantBarrierOnWith
        (interior powerConeQ1)
        (2 : NNReal)
        powerConeBarrier :=
    powerConeBarrierIsTwoSelfConcordantBarrierL2
  have hΦ :
      IsSelfConcordantBarrierOnWith
        (interior powerConeQ2)
        (2 : NNReal)
        Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2OuterBarrier := by
    -- The raw outer barrier theorem is proved once in `Prereqs.lean`; reuse it here to keep this
    -- specialization theorem as a thin owner-stable boundary.
    simpa using
      Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2RawBarrierIsTwoSelfConcordantBarrier
  have hbarrier :=
    coneCompositionBarrier_isSelfConcordantBarrierOnWith
      (Q := powerConeQ1)
      (K := ConvexCone.positive ℝ ℝ)
      (Q₂ := powerConeQ2)
      (F := powerConeBarrier)
      (Φ := Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2OuterBarrier)
      (ξ := powerConeGeometricMean α)
      (β := (1 : NNReal))
      (ν := (2 : NNReal))
      (μ := (2 : NNReal))
      (Nesterov.Chap05.Theorem_5_4_7_3.Prereqs
        .power_cone_geometric_mean_is_three_times_cont_diff_concave_on_with hα₀ hα₁)
      (powerConeGeometricMeanIsOneCompatibleWithPowerConeBarrierL2 hα₀ hα₁)
      Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2_closed
      Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2_convex
      hF
      hΦ
      (fun {s} hs {p} hp τ hτ ↦
        Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2_positive_recession hs hp τ hτ)
  -- The public theorem keeps the raw split-log owner spelling from the source-facing target file.
  simpa [Nesterov.Chap05.Theorem_5_4_7_3.Prereqs.powerConeQ2OuterBarrier] using hbarrier

end Nesterov.Chap05.Theorem_5_4_7_3.Specialization
