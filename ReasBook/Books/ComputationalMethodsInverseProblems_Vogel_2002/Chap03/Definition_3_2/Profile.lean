/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Real.Basic

public section

namespace LineSearch

universe u

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- The one-dimensional line-search profile `τ ↦ J (f_v + τ • p_v)`. -/
@[expose]
def profile (J : X → ℝ) (f_v p_v : X) : ℝ → ℝ :=
  fun τ ↦ J (f_v + τ • p_v)

/-- Evaluating `LineSearch.profile` recovers `J (f_v + τ • p_v)`. -/
theorem profile_apply (J : X → ℝ) (f_v p_v : X) (τ : ℝ) :
    profile J f_v p_v τ = J (f_v + τ • p_v) := rfl

end LineSearch
