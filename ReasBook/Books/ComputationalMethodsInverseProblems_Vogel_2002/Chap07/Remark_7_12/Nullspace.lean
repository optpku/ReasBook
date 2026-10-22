/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError

public section

namespace FilterRegularization

universe u v

section Nullspace

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Chapter 7 nullspace component vanishes asymptotically along the
operator family `K n`. -/
abbrev HasVanishingNullspaceComponent (K : ℕ → H →L[ℝ] F) (fTrue : H) : Prop :=
  Filter.Tendsto (fun n ↦ nullspaceComponent (K n) fTrue) Filter.atTop (nhds 0)

@[simp] theorem hasVanishingNullspaceComponent_iff
    (K : ℕ → H →L[ℝ] F) (fTrue : H) :
    HasVanishingNullspaceComponent K fTrue ↔
      Filter.Tendsto (fun n ↦ nullspaceComponent (K n) fTrue) Filter.atTop (nhds 0) :=
  Iff.rfl

end Nullspace

end FilterRegularization
