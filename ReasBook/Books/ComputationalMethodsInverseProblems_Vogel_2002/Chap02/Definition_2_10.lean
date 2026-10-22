/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic

public section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- Definition 2.10. A bounded linear operator `K : H₁ →L[𝕜] H₂` is compact if and only if, for
every bounded set `S : Set H₁`, the closure of `K '' S` is a compact subset of `H₂`. -/
theorem isCompactOperator_iff_forall_isCompact_closure_image_of_bounded
    (K : H₁ →L[𝕜] H₂) :
    IsCompactOperator K ↔
      ∀ {S : Set H₁}, Bornology.IsBounded S → IsCompact (closure (K '' S)) := by
  constructor
  · intro hK S hS
    exact hK.isCompact_closure_image_of_bounded hS
  · intro hK
    refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image K).2 ?_
    exact ⟨Metric.closedBall (0 : H₁) 1, Metric.closedBall_mem_nhds (0 : H₁) zero_lt_one,
      hK Metric.isBounded_closedBall⟩

end ContinuousLinearMap
