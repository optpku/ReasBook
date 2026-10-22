/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_3.Prereqs
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_4.Specialization

-- Declarations for this item will be appended below by the statement pipeline.

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

open scoped PowerConePlus
open scoped QTwoPlus
open scoped Gradient

/-- The logarithmic barrier `Ψ_P^+` for the one-sided power cone `K_α^+`, presented as the
source-facing specialization of the chapter's canonical cone-composition barrier owner. -/
def power_cone_plus_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0)
    (powerConeGeometricMean α)
    1

/-- Helper for Theorem 5.4.7.4: the source-facing barrier owner is exactly the generic
cone-composition barrier specialization. -/
lemma powerConePlusBarrier_eq_coneCompositionBarrier
    (α : ℝ) :
    power_cone_plus_barrier α =
      coneCompositionBarrier
        powerConeBarrier
        (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0)
        (powerConeGeometricMean α)
        1 := by
  -- This is a definitional owner bridge for the final source-facing rewrite.
  rfl

/-- Helper for Theorem 5.4.7.4: the source-facing cone owner `K_[α]⁺` is exactly the generic
cone-composition feasible set used by the chapter theorem. -/
lemma powerConePlus_eq_coneCompositionFeasibleSet
    (α : ℝ) :
    K_[α]⁺ =
      coneCompositionFeasibleSet
        powerConeQ1
        (ConvexCone.positive ℝ ℝ)
        (powerConeGeometricMean α)
        Q₂⁺ := by
  -- This is the matching definitional bridge for the feasible-set owner.
  rfl

/-- Helper for Theorem 5.4.7.4: the cone-composition parameter `1 + 1^3 * 2` simplifies to `3`. -/
private theorem powerConePlusBarrierParameter :
    ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal)) = 3 := by
  -- Normalize the cone-composition parameter once so the wrapper theorem stays flat.
  norm_num

/-- Helper for Theorem 5.4.7.4: the support-file specialization rewrites directly to the
source-facing `K_[α]⁺` barrier statement. -/
private theorem powerConePlusBarrier_of_specialization
    {α : ℝ}
    (h :
      IsSelfConcordantBarrierOnWith
        (interior
          (coneCompositionFeasibleSet
            powerConeQ1
            (ConvexCone.positive ℝ ℝ)
            (powerConeGeometricMean α)
            Q₂⁺))
        ((1 : NNReal) + (1 : NNReal) ^ 3 * (2 : NNReal))
        (coneCompositionBarrier
          powerConeBarrier
          (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0)
          (powerConeGeometricMean α)
          1)) :
    IsSelfConcordantBarrierOnWith
      (interior (K_[α]⁺))
      (3 : NNReal)
      (power_cone_plus_barrier α) := by
  -- Route correction: the heavy cone-composition specialization now lives in the support file,
  -- so this main file only rewrites the source-facing cone, barrier, and parameter owners.
  simpa only
      [powerConePlus_eq_coneCompositionFeasibleSet,
        powerConePlusBarrier_eq_coneCompositionBarrier,
        powerConePlusBarrierParameter]
    using h

-- Proof sketch: import the canonical cone-composition specialization from the support file and
-- rewrite it back to the textbook cone/barrier statement.
/-- Theorem 5.4.7.4: for `0 < α < 1`, the function
`Ψ_P^+((x₁, x₂), z) = -log (x₁^α x₂^(1 - α) - z) - log x₁ - log x₂` is a
`3`-self-concordant barrier for the one-sided power cone `K_α^+`. -/
theorem power_cone_plus_barrier_is_three_self_concordant_barrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior (K_[α]⁺))
      (3 : NNReal)
      (power_cone_plus_barrier α) := by
  -- Reuse the isolated support-file specialization before rewriting to the public statement.
  exact powerConePlusBarrier_of_specialization
    (coneCompositionBarrier_powerConePlusQTwoPlus_isSelfConcordantBarrierOnWith hα₀ hα₁)
