/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_1.Step
public import Mathlib.Topology.EMetricSpace.Lipschitz

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `IsIterateSequence J f` means that each increment `f (v + 1) - f v` is a Newton
step for `J` at `f v`. -/
def IsIterateSequence (J : H → ℝ) (f : ℕ → H) : Prop :=
  ∀ v : ℕ, IsStep J (f v) (f (v + 1) - f v)

/-- The Newton convergence constant associated to a Hessian Lipschitz constant `K`
and an explicit lower spectral bound `μ`. -/
def convergenceConstant (K : NNReal) (μ : ℝ) : ℝ :=
  (K : ℝ) / μ

/-- Specification lemma for `Newton.IsIterateSequence`. -/
theorem isIterateSequence_iff (J : H → ℝ) (f : ℕ → H) :
    IsIterateSequence J f ↔ ∀ v : ℕ, IsStep J (f v) (f (v + 1) - f v) := sorry

/-- Unfolding lemma for `Newton.convergenceConstant`. -/
theorem convergenceConstant_eq (K : NNReal) (μ : ℝ) :
    convergenceConstant K μ = (K : ℝ) / μ := sorry

end Newton
