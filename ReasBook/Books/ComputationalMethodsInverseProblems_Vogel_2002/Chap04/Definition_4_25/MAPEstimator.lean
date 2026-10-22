/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Theorem_4_24.PosteriorPmf
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace ProbabilityTheory.JointPmf

universe v w

variable {α : Type v} {β : Type w}

/-- A candidate `xMap` is a maximum a posteriori estimator for `joint` at observation `y` when
it maximizes the posterior PMF `condFstGivenSnd joint y hy` on `Set.univ`. -/
abbrev IsMAPEstimator (joint : PMF (α × β)) (y : β) (hy : sndMarginal joint y ≠ 0)
    (xMap : α) : Prop :=
  IsMaxOn (condFstGivenSnd joint y hy) Set.univ xMap

/-- The defining characterization of `IsMAPEstimator`. -/
theorem isMAPEstimator_iff (joint : PMF (α × β)) (y : β) (hy : sndMarginal joint y ≠ 0)
    (xMap : α) :
    IsMAPEstimator joint y hy xMap ↔ IsMaxOn (condFstGivenSnd joint y hy) Set.univ xMap :=
  Iff.rfl

end ProbabilityTheory.JointPmf
