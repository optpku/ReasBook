/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

variable {m : ℕ} {X : Type u}
local notation "R" => EuclideanSpace ℝ (Fin m)

/- Example 1.1.6 lies in the constrained-optimization / least-squares reformulation domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` and
  `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem` in
  `Chap01/Definition_1_3_3`, the Chapter 1 owner for an unconstrained objective on the feasible
  subtype `Q` and its zero-constraint bridge;
* `vectorMap` in `Chap03/Lemma_3_1_16`, the project owner for a finite scalar family packaged as
  an `ℝ^m`-valued residual map;
* `euclideanNormSq_isMeritFunction` in `Chap04/Definition_4_4_1`, the merit-function theorem for
  the canonical squared Euclidean residual scalarization.

Best owner abstraction:
* `SetConstrainedMinimizationProblem Q` for the least-squares reformulation on the structural set
  `Q`;
* `vectorMap` and ordinary composition for packaging the scalar equation family into the
  canonical residual map and merit scalarization.

Primitive data:
* the structural set `Q`;
* the scalar equation family `f_j(x) = a_j`.

Derived API:
* `equationSystemResidual`, the residual vector of the original equality system;
* `equationSystemOptimizationProblem`, the unconstrained squared-residual minimization problem on
  the subtype `Q`;
* the companion sum-of-squares and zero-set lemmas for that owner object.

Source/core/bridge triage:
* source-facing: the least-squares reformulation of `f_j(x) = a_j` on `Q`;
* core/canonical: `SetConstrainedMinimizationProblem Q`;
* bridge/view: `equationSystemResidual`, the specialization of `vectorMap` to the
  coordinates `f_j(x) - a_j`.

The source states `Q ⊆ ℝⁿ`, but this example's reformulation uses no linear, topological, or
metric structure on the ambient space. The faithful primitive data are only the structural set
`Q` and the equation family on its subtype, so the public API is refined to an arbitrary ambient
type `X`.
-/

/-- The residual map of the system `f_j(x) = a_j` on the structural set `Q`. -/
noncomputable abbrev equationSystemResidual
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ) :
    Q → R :=
  vectorMap (fun j x ↦ f j x - a j)

@[simp] theorem equationSystemResidual_apply
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q)
    (j : Fin m) :
    equationSystemResidual f a x j = f j x - a j := by
  simp [equationSystemResidual]

/-- Example 1.1.6: A system of equations `f_j(x) = a_j` on a set `Q ⊆ ℝⁿ` can be converted into
the minimization of the canonical squared residual norm on `Q`; for the coordinate residual map
attached to `f_j(x) = a_j`, this is exactly the textbook sum of squared residuals. The set `Q`
may encode any additional constraints imposed on `x`. -/
noncomputable def equationSystemOptimizationProblem
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ) : SetConstrainedMinimizationProblem Q where
  feasibleSet := Set.univ
  objective := (fun u : R ↦ ‖u‖ ^ (2 : ℕ)) ∘ equationSystemResidual f a

/-- For the coordinate residual map `x ↦ (f_j(x) - a_j)_j`, the squared residual norm is the
textbook sum of squared residuals. -/
theorem equationSystemOptimizationProblem_objective_eq_sum_sq
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q) :
    equationSystemOptimizationProblem f a x =
      ∑ j : Fin m, (f j x - a j) ^ 2 := by
  simpa [equationSystemOptimizationProblem, equationSystemResidual, Function.comp_apply] using
    EuclideanSpace.real_norm_sq_eq (equationSystemResidual f a x)

/-- The coordinate residual map vanishes exactly at solutions of the original system. -/
theorem equationSystemResidual_eq_zero_iff
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q) :
    equationSystemResidual f a x = 0 ↔ ∀ j : Fin m, f j x = a j := by
  constructor
  · intro h j
    exact sub_eq_zero.mp <| by
      simpa using congrArg (fun r : R ↦ r j) h
  · intro hx
    ext j
    rw [equationSystemResidual_apply]
    exact sub_eq_zero.mpr (hx j)

/-- The residual objective for the system `f_j(x) = a_j` vanishes exactly at solutions on `Q`. -/
theorem equationSystemOptimizationProblem_objective_eq_zero_iff
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q) :
    equationSystemOptimizationProblem f a x = 0 ↔
      ∀ j : Fin m, f j x = a j := by
  have hφ : IsMeritFunction (fun u : R ↦ ‖u‖ ^ (2 : ℕ)) :=
    euclideanNormSq_isMeritFunction m
  simpa [equationSystemOptimizationProblem, equationSystemResidual, Function.comp_apply] using
    ((hφ.eq_zero_iff (equationSystemResidual f a x)).trans
      (equationSystemResidual_eq_zero_iff f a x))

/-
Example 1.1.6 is formalized by `equationSystemOptimizationProblem` together with
`equationSystemOptimizationProblem_objective_eq_zero_iff`.
-/
