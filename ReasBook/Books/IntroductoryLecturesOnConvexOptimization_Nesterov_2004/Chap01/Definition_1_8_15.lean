/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [SeminormedAddCommGroup E]

/-
Definition 1.8.15 is source-facing: it records superlinear convergence of a trajectory family near
`xStar`.

Primary domain:
- trajectory-level superlinear convergence organized around genuine convergence
  `Filter.Tendsto (trajectory x0) Filter.atTop (nhds xStar)`
  together with the scalar recurrence owner
  `HasEventuallySuperlinearErrorBound`.

Relevant owner-style declarations sampled before refining:
- `HasEventuallySuperlinearErrorBound` from `Definition_1_2_7.lean`
- `gradient_descent_local_linear_rate` from `Theorem_1_6_15.lean`
- `LocalQuadraticNewtonConvergence` from `Theorem_5_0_5.lean`

Owner abstraction:
- for each admissible initial point `x0`, the trajectory itself tends to `xStar`, while its
  induced scalar error sequence `fun k ↦ ‖trajectory x0 k - xStar‖` carries an eventual
  superlinear bound `HasEventuallySuperlinearErrorBound ... lag c N`

Primitive data:
- the trajectory family `trajectory`
- the reference point `xStar`
- the lag `lag`

Derived API:
- the neighborhood constants `ε` and `c`
- convergence of `trajectory x0` to `xStar`
- equivalently, convergence of the induced scalar error sequence to `0`
- the eventual recurrence bound for the induced scalar error sequence

The previous version fixed the ambient space to the concrete display model `EuclideanSpace ℝ
(Fin dim)` even though the definition only uses the seminormed additive-group structure through
`‖trajectory x0 k - xStar‖` and the induced neighborhood filter of `xStar`. The owner layer is
therefore trajectory convergence plus the induced scalar recurrence, not a coordinate presentation
of the ambient space.
-/

/-- Definition 1.8.15: a trajectory family has a superlinear rate of convergence to `xStar` with
lag `lag` if there are positive constants `ε` and `c` such that every initial point `x₀` with
`‖x₀ - xStar‖ < ε` generates a trajectory starting at `x₀`, the induced error sequence
`‖x_k - xStar‖` is eventually controlled by the superlinear recurrence, while the trajectory
itself converges to `xStar`, and from some index `N ≥ lag`
onward, satisfying
`‖x_{k+1} - xStar‖ ≤ c * ‖x_k - xStar‖ * ‖x_{k-lag} - xStar‖`. -/
def HasSuperlinearRateOfConvergence
    (trajectory : E → ℕ → E)
    (xStar : E) (lag : ℕ) : Prop :=
  ∃ ε > 0, ∃ c > 0,
    ∀ ⦃x0 : E⦄, ‖x0 - xStar‖ < ε →
      trajectory x0 0 = x0 ∧
        Filter.Tendsto (trajectory x0) Filter.atTop (nhds xStar) ∧
        ∃ N,
          HasEventuallySuperlinearErrorBound
            (fun k ↦ ‖trajectory x0 k - xStar‖)
            lag c N
