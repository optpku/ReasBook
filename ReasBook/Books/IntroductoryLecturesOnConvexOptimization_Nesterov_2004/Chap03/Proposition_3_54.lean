/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_52

universe u

/- Proposition 3.54 lies in the chapter's finite sampled constrained-level stopping domain.

Relevant owner declarations sampled before refining this file:
* `setConstrainedParametricObjective` in `Proposition_3_52`, the chapter owner for the pointwise
  max-objective `x ↦ max (f x - tk) (fBar x)`;
* `parametricValueFunction` in `Lemma_3_3_6`, the set-level canonical infimum of that owner;
* `Finset.inf'`, `Finset.inf'_le`, and `Finset.exists_mem_eq_inf'`, the mathlib owners for
  nonempty finite minima and their canonical bound / attainment API;
* `minGradientNormAlongIterates` and `minGradientNormAlongIterates.exists_eq` in
  `Chap02/Definition_2_23`, the earlier project instance of the same `Finset.inf'` bridge shape.

Source/core/bridge triage:
* source-facing: the finite sampled constrained-level minimum on the search set `X`;
* core/canonical: `setConstrainedParametricObjective f fBar tk` and
  `parametricValueFunction (↑X : Set α) f fBar tk`;
* bridge/view: `constrained_level_minimum`, its finite attainment theorem, and the component
  bounds extracted from a bound on the canonical owner objective.

Primitive data:
* the nonempty finite search set `X`;
* the iteration parameter `tk`;
* the functions `f` and `fBar`.

Derived API:
* the finite minimum `constrained_level_minimum`;
* the source-facing notation `f*[X; f; fBar](tk)` for that finite minimum;
* the owner-style finite-minimum API `constrained_level_minimum.le` and
  `constrained_level_minimum.exists_eq`;
* the canonical bridge
  `parametricValueFunction_coe_eq_constrained_level_minimum`;
* the attainment theorem `global_stop_exists_minimizer`;
* the owner component bounds `setConstrainedParametricObjective.f_le_of_le` and
  `setConstrainedParametricObjective.fBar_le_of_le`.

This file therefore keeps only the finite-sample operational bridge and reuses the existing
Chapter 3 owner `setConstrainedParametricObjective` directly instead of introducing a duplicate
pointwise stopping-value owner.
-/

variable {α : Type u}

/-- The finite minimum of the constrained parametric objective over the search set `X`. -/
def constrained_level_minimum (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) : ℝ :=
  X.inf' (Fact.out : X.Nonempty) (setConstrainedParametricObjective f fBar tk)

namespace ConstrainedLevelMinimum

scoped notation:max "f*[" X:arg "; " f:arg "; " fBar:arg "](" tk:arg ")" =>
  constrained_level_minimum X tk f fBar

end ConstrainedLevelMinimum

open scoped ConstrainedLevelMinimum

namespace constrained_level_minimum

/-- The finite minimum is bounded above by the constrained parametric objective at each point of
the search set. -/
-- Proof sketch: unfold `constrained_level_minimum` and apply `Finset.inf'_le` to the point `x`.
theorem le (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) {x : α} (hx : x ∈ X) :
    f*[X; f; fBar](tk) ≤ setConstrainedParametricObjective f fBar tk x := by
  exact Finset.inf'_le (setConstrainedParametricObjective f fBar tk) hx

/-- Some point of the finite search set attains the constrained-level minimum. -/
-- Proof sketch: apply the canonical finite-attainment theorem `Finset.exists_mem_eq_inf'` to the
-- owner objective on `X`.
theorem exists_eq (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) :
    ∃ xStar ∈ X,
      f*[X; f; fBar](tk) = setConstrainedParametricObjective f fBar tk xStar := by
  exact X.exists_mem_eq_inf' (Fact.out : X.Nonempty) (setConstrainedParametricObjective f fBar tk)

end constrained_level_minimum

/-- Evaluating the chapter owner `parametricValueFunction` on the finite feasible set `↑X`
recovers the finite constrained-level minimum. -/
-- Proof sketch: pick a minimizer of the finite minimum, show it is a genuine minimizer on the
-- coerced feasible set `↑X`, then apply the Chapter 1 owner theorem
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`.
theorem parametricValueFunction_coe_eq_constrained_level_minimum
    (X : Finset α) [Fact X.Nonempty] (tk : ℝ) (f fBar : α → ℝ) :
    parametricValueFunction (↑X : Set α) f fBar tk =
      (f*[X; f; fBar](tk) : EReal) := by
  let problem : SetConstrainedMinimizationProblem α :=
    SetConstrainedMinimizationProblem.mk (↑X : Set α)
      (setConstrainedParametricObjective f fBar tk)
  rcases constrained_level_minimum.exists_eq X tk f fBar with ⟨xStar, hxStar, hmin⟩
  have hxStar' : xStar ∈ (↑X : Set α) := by
    simpa using hxStar
  have hminOn : IsMinOn (setConstrainedParametricObjective f fBar tk) (↑X : Set α) xStar := by
    intro y hy
    simpa [hmin] using constrained_level_minimum.le X tk f fBar hy
  simpa [problem, parametricValueFunction, hmin] using
    problem.optimalValue_eq_of_isMinOn hxStar' hminOn

/-- Proposition 3.54: if the global stop condition holds, then some point of the finite set `X`
attains the finite minimum of `x ↦ max (f x - tk) (fBar x)` and this value is at most `ε`. -/
-- Proof sketch: choose a minimizer of the owner objective on the nonempty finset `X`, identify
-- its value with `constrained_level_minimum`, and combine that equality with the global stop
-- inequality.
theorem global_stop_exists_minimizer (X : Finset α) [Fact X.Nonempty] (tk ε : ℝ)
    (f fBar : α → ℝ) (hstop : f*[X; f; fBar](tk) ≤ ε) :
    ∃ xStar ∈ X,
      setConstrainedParametricObjective f fBar tk xStar = f*[X; f; fBar](tk) ∧
        setConstrainedParametricObjective f fBar tk xStar ≤ ε := by
  rcases constrained_level_minimum.exists_eq X tk f fBar with ⟨xStar, hxStar, hmin⟩
  refine ⟨xStar, hxStar, hmin.symm, ?_⟩
  simpa [hmin] using hstop

namespace setConstrainedParametricObjective

/-- A point whose constrained parametric objective is at most `ε` also satisfies
the corresponding bound on `f`. -/
-- Proof sketch: rewrite the owner objective as `max (f x - tk) (fBar x)`, use `max_le_iff` to
-- read off `f x - tk ≤ ε`, then combine it with `tk ≤ tStar`.
theorem f_le_of_le {tk tStar ε : ℝ} {f fBar : α → ℝ} {x : α}
    (hvalue : setConstrainedParametricObjective f fBar tk x ≤ ε) (htk : tk ≤ tStar) :
    f x ≤ tStar + ε := by
  rw [setConstrainedParametricObjective_apply] at hvalue
  rcases max_le_iff.mp hvalue with ⟨hf, _⟩
  linarith

/-- A point whose constrained parametric objective is at most `ε` also satisfies
`fBar x ≤ ε`. -/
-- Proof sketch: rewrite the owner objective as a pointwise maximum and read off the second
-- component using `max_le_iff`.
theorem fBar_le_of_le {tk ε : ℝ} {f fBar : α → ℝ} {x : α}
    (hvalue : setConstrainedParametricObjective f fBar tk x ≤ ε) :
    fBar x ≤ ε := by
  rw [setConstrainedParametricObjective_apply] at hvalue
  exact (max_le_iff.mp hvalue).2

end setConstrainedParametricObjective
