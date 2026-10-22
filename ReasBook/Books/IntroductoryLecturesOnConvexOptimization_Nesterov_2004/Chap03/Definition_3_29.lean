/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_28
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open scoped WithTopConvexAnalysis

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]

/- Definition 3.29 lies in the convex-analysis max-representation oracle domain.

Primary domain:
- pointwise-max representations of convex objectives and oracle access to active slices.

Sampled owner-style declarations:
- `MaxRepresentationPrimalDualProblem`
- `MaxRepresentationPrimalDualProblem.objective_eq_kernel_of_isMaxOn`
- `subdifferentialWithin`
- `IsMaxOn`

Best owner abstraction:
- `MaxRepresentationPrimalDualProblem E U`, which already owns the primal feasible set, parameter
  set, objective, and kernel;
- `IsMaxOn` for maximizer optimality on the parameter set;
- the generic `subdifferentialWithin` owner from `Theorem_3_44` for relative slice subgradients.

Source/core/bridge triage:
- `source-facing`: the combined oracle of Definition 3.29;
- `core/canonical`: the owner problem `MaxRepresentationPrimalDualProblem E U` together with the
  owner notions `IsMaxOn` and `subdifferentialWithin`;
- `bridge/view`: the owner theorems
  `MaxRepresentationPrimalDualProblem.objective_eq_kernel_of_isMaxOn` and
  `MaxRepresentationPrimalDualProblem.subgradient_mem_subdifferentialWithin_of_isMaxOn`, which
  turn maximizer optimality and active-slice relative subgradients into represented-objective
  statements.

Primitive data:
- `answer : problem.feasibleSet → problem.dualSet × E`

Derived API:
- the selected maximizer `u(x)` and slice subgradient `g(x)` obtained by projecting `answer x`
- value attainment in the owner objective `problem.objective`
- maximizer optimality via `IsMaxOn`
- the owner bridge
  `MaxRepresentationPrimalDualProblem.subgradient_mem_subdifferentialWithin_of_isMaxOn`
  from active-slice relative subgradients to represented-objective relative subgradients
- relative subgradient membership via `subdifferentialWithin`

This file therefore keeps the source-facing oracle notion, but attaches it directly to the chapter
owner problem instead of repeating `P`, `S`, `f`, and `Ψ` as parallel parameters. -/

/-- Definition 3.29: for a max-representation problem, an oracle chooses at each feasible query
point `x ∈ P` a feasible maximizer `u(x) ∈ S` and a relative subgradient of the active slice
`Ψ(·, u(x))` at `x`. The equality `f(x) = Ψ(x, u(x))` is derived from maximizer optimality via
the owner problem. -/
structure MaxRepresentationOracle
    (problem : MaxRepresentationPrimalDualProblem E U) where
  /-- The oracle reply at the feasible query point `x`, consisting of the selected maximizer
  `u(x)` together with the selected relative subgradient `g(x)`. -/
  answer : problem.feasibleSet → problem.dualSet × E
  /-- At feasible query points, the selected `u(x)` maximizes `Ψ(x, ·)` over the parameter set. -/
  maximizer_spec :
    ∀ x : problem.feasibleSet,
      IsMaxOn (problem.kernel x) problem.dualSet (answer x).1
  /-- At feasible query points, the selected `g(x)` lies in the relative subdifferential of the
  active slice `Ψ(·, u(x))` over the primal set. -/
  subgradient_spec :
    ∀ x : problem.feasibleSet,
      (answer x).2 ∈
        ∂[problem.feasibleSet]
          (((fun y ↦ problem.kernel y ((answer x).1 : U)) : E → ℝ))
          ((x : E))

namespace MaxRepresentationOracle

variable {problem : MaxRepresentationPrimalDualProblem E U}
variable (oracle : MaxRepresentationOracle problem)

/-- The selected maximizer `u(x)` at the feasible query point `x`. -/
def maximizer (x : problem.feasibleSet) : problem.dualSet :=
  (oracle.answer x).1

/-- The selected relative subgradient `g(x)` at the feasible query point `x`. -/
def subgradient (x : problem.feasibleSet) : E :=
  (oracle.answer x).2

/-- The first component of the oracle reply is the selected maximizer. -/
@[simp] theorem answer_fst (x : problem.feasibleSet) :
    (oracle.answer x).1 = oracle.maximizer x :=
  rfl

/-- The second component of the oracle reply is the selected slice subgradient. -/
@[simp] theorem answer_snd (x : problem.feasibleSet) :
    (oracle.answer x).2 = oracle.subgradient x :=
  rfl

/-- At a feasible query point, the oracle's selected maximizer realizes the represented objective
value. -/
theorem objective_eq_kernel (x : problem.feasibleSet) :
    problem x = problem.kernel x (oracle.maximizer x) :=
  problem.objective_eq_kernel_of_isMaxOn
    x.2 (oracle.maximizer x) (oracle.maximizer_spec x)

/-- At a feasible query point, the oracle's selected slice subgradient is also a relative
subgradient of the represented objective over the primal feasible set. -/
theorem subgradient_mem_subdifferentialWithin (x : problem.feasibleSet) :
    oracle.subgradient x ∈ ∂[problem.feasibleSet] problem ((x : E)) := by
  exact
    problem.subgradient_mem_subdifferentialWithin_of_isMaxOn
      x (oracle.maximizer x) (oracle.maximizer_spec x) (oracle.subgradient_spec x)

end MaxRepresentationOracle

end
