/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.Operator
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

public section

noncomputable section

namespace Fredholm1D

/-- An `L²` class has a smooth representative on `s` when some representative `g`
belongs to the class and is `ContDiffOn ℝ ⊤` on `s`. -/
def HasContDiffRepresentativeOn (μ : MeasureTheory.Measure ℝ) (s : Set ℝ)
    (f : MeasureTheory.Lp ℝ 2 μ) : Prop :=
  ∃ g : ℝ → ℝ, ∃ h_mem : MeasureTheory.MemLp g 2 μ,
    h_mem.toLp g = f ∧ ContDiffOn ℝ ⊤ g s

/-- Membership in `HasContDiffRepresentativeOn` is exactly the existence of a
smooth representative realizing the given `L²` class. -/
theorem hasContDiffRepresentativeOn_iff (μ : MeasureTheory.Measure ℝ) (s : Set ℝ)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    HasContDiffRepresentativeOn μ s f ↔
      ∃ g : ℝ → ℝ, ∃ h_mem : MeasureTheory.MemLp g 2 μ,
        h_mem.toLp g = f ∧ ContDiffOn ℝ ⊤ g s := sorry

/-- The Gaussian `L²(0, 1)` blur has a globally smooth representative. -/
theorem gaussianBlurL2_hasSmoothRepresentative (C γ : ℝ)
    (z : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    HasContDiffRepresentativeOn unitIntervalMeasure Set.univ (gaussianBlurL2 C γ z) := sorry

end Fredholm1D
