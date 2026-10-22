/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

public section

universe u v w

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [SeminormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

namespace IsBoundedLinearMap

/-- Evaluating the bundled operator associated to `hf` recovers the original map. -/
@[simp] theorem toContinuousLinearMap_apply {f : H₁ → H₂} (hf : IsBoundedLinearMap 𝕜 f)
    (x : H₁) :
    IsBoundedLinearMap.toContinuousLinearMap f hf x = f x :=
  rfl

end IsBoundedLinearMap

namespace ContinuousLinearMap

/-- Bundling the unbundled bounded-linearity witness of `K` recovers `K`. -/
@[simp] theorem toContinuousLinearMap_isBoundedLinearMap (K : H₁ →L[𝕜] H₂) :
    IsBoundedLinearMap.toContinuousLinearMap K K.isBoundedLinearMap = K := by
  ext x
  rfl

end ContinuousLinearMap
