/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Exercise_6_2.Benchmark

public section

namespace Exercise62

namespace Benchmark

variable {n m : ℕ}

/-- Exercise 6.2. A conductivity sample is an estimator for the Figure 6.2 benchmark when it
minimizes the regularized output-least-squares objective over the admissible conductivity set. -/
def IsEstimate (benchmark : Benchmark n m) (J : AdmissibleConductivity n → ℝ) (α : ℝ)
    (κHat : AdmissibleConductivity n) : Prop :=
  IsMinOn (benchmark.objective J α) Set.univ κHat

/-- `IsEstimate` is exactly the unconstrained minimizer predicate on the admissible conductivity
subtype. -/
theorem isEstimate_iff (benchmark : Benchmark n m) (J : AdmissibleConductivity n → ℝ) (α : ℝ)
    (κHat : AdmissibleConductivity n) :
    benchmark.IsEstimate J α κHat ↔ IsMinOn (benchmark.objective J α) Set.univ κHat :=
  Iff.rfl

end Benchmark

end Exercise62
