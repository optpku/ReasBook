/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

public section

universe u v w

namespace ContinuousLinearMap

open Submodule

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

private theorem isCompactOperator_subtypeL_of_finiteDimensional
    (S : Submodule 𝕜 H₂) (hS : FiniteDimensional 𝕜 S) :
    IsCompactOperator S.subtypeL := by
  have hLoc : LocallyCompactSpace S :=
    @LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 S
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hS
  have hId : IsCompactOperator (id : S → S) :=
    @isCompactOperator_id S inferInstance inferInstance inferInstance hLoc
  simpa using hId.clm_comp S.subtypeL

/-- Exercise 2.10. A bounded linear operator `K : H₁ →L[𝕜] H₂` whose range `K.range` is
finite-dimensional is compact. -/
theorem isCompactOperator_of_finiteDimensional_range
    (K : H₁ →L[𝕜] H₂) (h_range_fin : FiniteDimensional 𝕜 K.range) :
    IsCompactOperator K := by
  let Kr : H₁ →L[𝕜] K.range := K.rangeRestrict
  have hSubtype : IsCompactOperator K.range.subtypeL :=
    isCompactOperator_subtypeL_of_finiteDimensional K.range h_range_fin
  have hKr : Subtype.val ∘ Kr = K := by
    funext x
    rfl
  simpa [hKr] using hSubtype.comp_clm Kr

end ContinuousLinearMap
