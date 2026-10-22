/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_3_1.Run
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Exercise_6_2

public section

/-!
Exercise 6.8 reuses the Figure 6.2 benchmark objective and estimator predicate
from Exercise 6.2 together with the generic BFGS backend from Algorithm 3.3.1.
This file records that source-facing reuse surface rather than restating the
benchmark objective locally.
-/

/- Exercise 6.8. A benchmark-specialized BFGS formulation for Figure 6.2 uses
`Exercise62.Benchmark.objective` as the objective owner, targets
`Exercise62.Benchmark.IsEstimate`, and then applies the generic BFGS run
infrastructure. -/
#check Exercise62.Benchmark.objective
#check Exercise62.Benchmark.IsEstimate
#check Exercise62.Benchmark.isEstimate_iff

#check BFGS.IsRun
#check BFGS.IsRun.isRun_iff
#check BFGS.Step
#check BFGS.initialState
#check BFGS.direction
#check LineSearch.profile

/- Verified backend anchors for the benchmark-specialization route. -/
#check BFGS.IsRun.init_eq
#check BFGS.IsRun.step
#check BFGS.IsRun.hessian_isUnit
#check BFGS.IsRun.lineSearch
#check BFGS.IsRun.point_eq
#check BFGS.IsRun.gradient_eq
#check BFGS.IsRun.hessian_eq
