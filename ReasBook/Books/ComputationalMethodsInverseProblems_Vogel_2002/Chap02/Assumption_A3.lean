/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A3.Comparison

public section

universe u v w

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [SeminormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/- Assumption A3. The canonical Lean notion of a bounded linear operator
`K : H₁ → H₂` is the bundled type `H₁ →L[𝕜] H₂`. The companion module
`Book.Ch2.Assumption_A3.Comparison` records the standard passage between the bundled and
unbundled bounded-linearity interfaces used in mathlib. -/

#check (H₁ →L[𝕜] H₂)
#check ContinuousLinearMap.isBoundedLinearMap
#check IsBoundedLinearMap.toContinuousLinearMap
