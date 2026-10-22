/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

public section

noncomputable section

namespace ConstraintQualification

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type v}

/-- The linear independence constraint qualification at `f` holds when the
gradients of the active constraints are linearly independent. -/
def SatisfiesLICQ (c : ι → H → ℝ) (active : H → Set ι) (f : H) : Prop :=
  LinearIndepOn ℝ (fun i ↦ gradient (c i) f) (active f)

/-- `SatisfiesLICQ c active f` is exactly the linear independence of the active
constraint gradients at `f`. -/
theorem satisfiesLICQ_iff (c : ι → H → ℝ) (active : H → Set ι) (f : H) :
    SatisfiesLICQ c active f ↔
      LinearIndepOn ℝ (fun i ↦ gradient (c i) f) (active f) := Iff.rfl

/-- A regular point is a point where LICQ holds for the active constraints of `c`. -/
abbrev IsRegularPoint (c : ι → H → ℝ) (f : H) : Prop :=
  SatisfiesLICQ c (ActiveSet.active c) f

/-- A regular point is exactly a point where LICQ holds for `ActiveSet.active c`. -/
theorem isRegularPoint_iff_satisfiesLICQ
    (c : ι → H → ℝ) (f : H) :
    IsRegularPoint c f ↔ SatisfiesLICQ c (ActiveSet.active c) f := Iff.rfl

/-- A regular point is characterized by the linear independence of the active
constraint gradients at that point. -/
theorem isRegularPoint_iff (c : ι → H → ℝ) (f : H) :
    IsRegularPoint c f ↔
      LinearIndepOn ℝ (fun i ↦ gradient (c i) f) (ActiveSet.active c f) := Iff.rfl

end ConstraintQualification
