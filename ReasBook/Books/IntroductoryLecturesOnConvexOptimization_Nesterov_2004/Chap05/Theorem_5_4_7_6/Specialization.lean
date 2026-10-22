/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_6.Prereqs

noncomputable section

open scoped Gradient HessianLocalNorm

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

namespace Nesterov.Chap05.Theorem_5_4_7_6.Specialization

-- Route correction: keep only the raw specialization boundary in this support file so the item
-- file can stay source-facing while re-planning focuses on one theorem.
/-- Helper for Theorem 5.4.7.6: restate the entropy concavity witness in the chapter `RealProdL2`
pair ambient consumed by the generic cone-composition theorem. -/
private theorem entropyEpigraphRelativeEntropyIsThreeTimesContDiffConcaveOnWithL2 :
    @IsThreeTimesContDiffConcaveOnWith
      (ℝ × ℝ)
      ℝ
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instNormedSpaceRealProd
      Real.normedAddCommGroup
      RCLike.toInnerProductSpaceReal.toNormedSpace
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      entropyEpigraphRelativeEntropy := by
  -- The prerequisite theorem already proves the desired concavity; this wrapper only normalizes
  -- the owner spelling at the specialization boundary.
  simpa using entropyEpigraphRelativeEntropy_is_three_times_cont_diff_concave_on_with

/-- Helper for Theorem 5.4.7.6: restate the `β = 1` compatibility witness in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem entropyEpigraphRelativeEntropyIsOneCompatibleWithPowerConeBarrierL2 :
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
      entropyEpigraphRelativeEntropy := by
  -- The prerequisite theorem already has the right mathematics; this wrapper only normalizes the
  -- owner before the specialization call.
  simpa using entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier

/-- Helper for Theorem 5.4.7.6: restate the orthant logarithmic barrier in the chapter
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

/-- Helper for Theorem 5.4.7.6: restate the outer `Q₂` logarithmic barrier in the chapter
`RealProdL2` pair ambient consumed by the generic cone-composition theorem. -/
private theorem entropyEpigraphQ2RawBarrierIsOneSelfConcordantBarrierL2 :
    @IsSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      (interior entropyEpigraphQ2)
      (1 : NNReal)
      (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0) := by
  -- The outer barrier theorem already matches the raw owner spelling consumed by the generic
  -- theorem, so no extra alias transport is needed at the specialization boundary.
  simpa using
    entropyEpigraphQ2_sublevel_log_barrier_is_one_self_concordant_barrier

/-- Helper for Theorem 5.4.7.6: the generic cone-composition theorem should specialize to the raw
entropy-epigraph data in the chapter `Chap05RealProdL2` ambient with no extra `WithLp`
transport layer. -/
theorem coneCompositionBarrier_entropyEpigraphQ2Raw_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith
      (interior
        (coneCompositionFeasibleSet
          powerConeQ1
          (ConvexCone.positive ℝ ℝ)
          entropyEpigraphRelativeEntropy
          entropyEpigraphQ2))
      ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
      (coneCompositionBarrier
          powerConeBarrier
          (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0)
          entropyEpigraphRelativeEntropy
          1) := by
  have hxi :
      @IsThreeTimesContDiffConcaveOnWith
        (ℝ × ℝ)
        ℝ
        Chap05RealProdL2.instNormedAddCommGroupRealProd
        Chap05RealProdL2.instNormedSpaceRealProd
        Real.normedAddCommGroup
        RCLike.toInnerProductSpaceReal.toNormedSpace
        powerConeQ1
        (ConvexCone.positive ℝ ℝ)
        entropyEpigraphRelativeEntropy :=
    entropyEpigraphRelativeEntropyIsThreeTimesContDiffConcaveOnWithL2
  have hbeta :
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
        entropyEpigraphRelativeEntropy :=
    entropyEpigraphRelativeEntropyIsOneCompatibleWithPowerConeBarrierL2
  have hF :
      IsSelfConcordantBarrierOnWith
        (interior powerConeQ1)
        (2 : NNReal)
        powerConeBarrier :=
    powerConeBarrierIsTwoSelfConcordantBarrierL2
  have hPhi :
      IsSelfConcordantBarrierOnWith
        (interior entropyEpigraphQ2)
        (1 : NNReal)
        (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0) :=
    entropyEpigraphQ2RawBarrierIsOneSelfConcordantBarrierL2
  -- Route correction: after exposing the missing product ambient instances in
  -- `Theorem_5_4_6_13`, pin the pair and triple `Chap05RealProdL2` structures directly at the
  -- generic theorem call site so the specialization lives in one ambient spelling world.
  exact
    @coneCompositionBarrier_isSelfConcordantBarrierOnWith
      (ℝ × ℝ)
      ℝ
      ℝ
      _
      _
      _
      _
      _
      _
      _
      powerConeQ1
      entropyEpigraphQ2
      (ConvexCone.positive ℝ ℝ)
      powerConeBarrier
      (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0)
      entropyEpigraphRelativeEntropy
      (1 : NNReal)
      (1 : NNReal)
      (2 : NNReal)
      Chap05RealProdL2.instNormedAddCommGroupRealProdProd
      Chap05RealProdL2.instInnerProductSpaceRealProdProd
      Chap05RealProdL2.instCompleteSpaceRealProdProd
      Chap05RealProdL2.instNormedAddCommGroupRealProd
      Chap05RealProdL2.instInnerProductSpaceRealProd
      Chap05RealProdL2.instCompleteSpaceRealProd
      hxi
      hbeta
      entropyEpigraphQ2_closed
      entropyEpigraphQ2_convex
      hF
      hPhi
      (fun {s} hs {p} hp τ hτ ↦
        entropyEpigraphQ2_positive_recession hs hp τ hτ)

end Nesterov.Chap05.Theorem_5_4_7_6.Specialization
