/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Function.LpOrder
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_28.Instances

public section

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealL2

/-- The `μ`-a.e. nonnegative cone in real `L²(Ω)` is the positive cone of the order on
`MeasureTheory.Lp ℝ 2 μ`. -/
theorem aeNonneg_set_eq_Ici (μ : Measure Ω) :
    {f : Lp ℝ 2 μ | 0 ≤ᵐ[μ] (f : Ω → ℝ)} = Set.Ici (0 : Lp ℝ 2 μ) := by
  ext f
  simpa [Set.mem_Ici] using (Lp.coeFn_nonneg f)

/-- Example 2.28 (1). The set of real `L²(Ω)` classes that are nonnegative `μ`-a.e. is closed. -/
theorem aeNonneg_isClosed (μ : Measure Ω) :
    IsClosed {f : Lp ℝ 2 μ | 0 ≤ᵐ[μ] (f : Ω → ℝ)} := by
  rw [aeNonneg_set_eq_Ici μ]
  exact isClosed_Ici

/-- Example 2.28 (2). The set of real `L²(Ω)` classes that are nonnegative `μ`-a.e. is convex. -/
theorem aeNonneg_isConvex (μ : Measure Ω) :
    Convex ℝ {f : Lp ℝ 2 μ | 0 ≤ᵐ[μ] (f : Ω → ℝ)} := by
  rw [aeNonneg_set_eq_Ici μ]
  exact convex_Ici (0 : Lp ℝ 2 μ)

end RealL2
