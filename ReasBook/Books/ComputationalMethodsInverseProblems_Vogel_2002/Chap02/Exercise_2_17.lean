/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_22.WeakSeqTendsto
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_17.Instances
import Mathlib.Analysis.LocallyConvex.WeakSpace

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exercise 2.17 (1). Strong sequential convergence implies weak sequential convergence. -/
theorem weakSeqTendsto_of_tendsto {f : ℕ → H} {fStar : H}
    (h : Filter.Tendsto f Filter.atTop (nhds fStar)) : weakSeqTendsto f fStar := by
  rw [weakSeqTendsto_iff]
  convert (toWeakSpaceCLM ℝ H).continuous.tendsto fStar |>.comp h using 1
  · ext n
    simp [toWeakSpaceCLM_eq_toWeakSpace]
  · simp [toWeakSpaceCLM_eq_toWeakSpace]

/-- Exercise 2.17 (2). In finite-dimensional spaces, weak and strong sequential convergence are
equivalent. -/
theorem weakSeqTendsto_iff_tendsto [FiniteDimensional ℝ H] {f : ℕ → H} {fStar : H} :
    weakSeqTendsto f fStar ↔ Filter.Tendsto f Filter.atTop (nhds fStar) := by
  let e : H ≃L[ℝ] WeakSpace ℝ H := (toWeakSpace ℝ H).toContinuousLinearEquiv
  constructor
  · intro h
    rw [weakSeqTendsto_iff] at h
    have hsymm : Continuous e.symm := e.symm.continuous
    convert hsymm.tendsto (toWeakSpace ℝ H fStar) |>.comp h using 1
    · ext n
      simp [e]
    · simp [e]
  · exact weakSeqTendsto_of_tendsto
