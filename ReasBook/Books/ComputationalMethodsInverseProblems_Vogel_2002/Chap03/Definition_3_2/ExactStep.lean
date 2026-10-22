/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.Profile
public import Mathlib.Order.Filter.Extr

public section

namespace LineSearch

universe u

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- A step size `τ` solves the source line-search problem
`min_{σ > 0} J (f_v + σ • p_v)` when it is positive and minimizes the
line-search profile on the positive ray. -/
def IsExactStep (J : X → ℝ) (f_v p_v : X) (τ : ℝ) : Prop :=
  0 < τ ∧ IsMinOn (profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ

/-- A source exact line-search step is exactly a positive minimizer of the
profile on `Set.Ioi (0 : ℝ)`. -/
theorem isExactStep_iff {J : X → ℝ} {f_v p_v : X} {τ : ℝ} :
    IsExactStep J f_v p_v τ ↔
      0 < τ ∧ IsMinOn (profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ :=
  Iff.rfl

/-- An exact line-search step is admissible for the positive-ray problem. -/
theorem IsExactStep.pos {J : X → ℝ} {f_v p_v : X} {τ : ℝ}
    (hτ : IsExactStep J f_v p_v τ) :
    0 < τ :=
  hτ.1

/-- An exact line-search step belongs to the positive ray `Set.Ioi (0 : ℝ)`. -/
theorem IsExactStep.mem_Ioi {J : X → ℝ} {f_v p_v : X} {τ : ℝ}
    (hτ : IsExactStep J f_v p_v τ) :
    τ ∈ Set.Ioi (0 : ℝ) :=
  hτ.1

/-- An exact line-search step gives the canonical minimizer surface on the
positive ray. -/
theorem IsExactStep.isMinOn {J : X → ℝ} {f_v p_v : X} {τ : ℝ}
    (hτ : IsExactStep J f_v p_v τ) :
    IsMinOn (profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ :=
  hτ.2

end LineSearch
