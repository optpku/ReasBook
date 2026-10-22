/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_3_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_2_extra_2

noncomputable section

/-
Chapter06 Exercise 6.12 compares the canonical Chapter 6 owner surfaces for the trust-region
quadratic model, the conic model, the collinear-scaling rewrite, and the tensor/quadratic trial
point transition. Primary domain sampling for this refine pass:

- source-facing/core owner: `TrustRegionSubproblem` for the quadratic trust-region model.
- source-facing/core owner: `ConicTrustRegionSubproblem` for the conic trust-region model.
- bridge/view: `ConicTrustRegionSubproblem.CollinearScalingRewrite` for the `s = J w / (1 + hᵀ w)`
  reformulation and its admissible-set/objective comparison API.
- source-facing/core owner: `TensorMethodTransition` for the Step `3`-`8` tensor/quadratic trial
  point transition.

Primitive data stay in those owners; this exercise recalls only their derived public API rather
than introducing a second wrapper layer.

- `TrustRegionSubproblem.quadraticModel` is the standard trust-region quadratic model
  `q^(k) (s) = f(x_k) + g_kᵀ s + (1 / 2) sᵀ B_k s`.
- `ConicTrustRegionSubproblem.objective` is the conic model
  `ψ(s) = f + (gᵀ s) / (1 - aᵀ s) + (1 / 2) (sᵀ A s) / (1 - aᵀ s)^2`
  on admissible steps `s ∈ P.admissibleSet`.
- `ConicTrustRegionSubproblem.CollinearScalingRewrite.step` records the collinear-scaling
  substitution `s = J w / (1 + hᵀ w)`.
- `ConicTrustRegionSubproblem.CollinearScalingRewrite.exists_parameter_of_mem_admissibleSet`
  records the reverse representation of every admissible conic step by some parameter `w`.
- `ConicTrustRegionSubproblem.CollinearScalingRewrite.objective_eq_of_pos` records the
  side-conditioned comparison turning the conic objective into a quadratic objective in `w`.
- `TensorMethodTransition.xNext_eq_choose` records the Step `7` comparison between the
  tensor-model and quadratic-model trial points.
-/
#check TrustRegionSubproblem.quadraticModel
#check ConicTrustRegionSubproblem.objective
#check ConicTrustRegionSubproblem.CollinearScalingRewrite.step
#check ConicTrustRegionSubproblem.CollinearScalingRewrite.exists_parameter_of_mem_admissibleSet
#check ConicTrustRegionSubproblem.CollinearScalingRewrite.objective_eq_of_pos
#check TensorMethodTransition.tensorTrialPoint
#check TensorMethodTransition.quadraticTrialPoint
#check TensorMethodTransition.xNext_eq_choose
