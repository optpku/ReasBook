/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.Moments.Covariance

public section

universe u v

namespace ProbabilityTheory

/-- The covariance between distinct components of a mutually independent
real-valued family is zero. -/
theorem iIndepFun.covariance_eq_zero
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_memLp : ∀ i, MeasureTheory.MemLp (X i) 2 μ) {i j : ι} (hij : i ≠ j) :
    cov[X i, X j; μ] = 0 :=
  (h_indep.indepFun hij).covariance_eq_zero (h_memLp i) (h_memLp j)

end ProbabilityTheory
