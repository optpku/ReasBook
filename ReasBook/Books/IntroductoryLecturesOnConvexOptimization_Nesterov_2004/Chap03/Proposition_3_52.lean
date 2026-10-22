/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin ConstrainedThreshold

/- Proposition 3.52 lies in the chapter's scalar parametric max-objective / value-function
domain.

Mandatory domain-style sampling before refinement:
- `setConstrainedParametricObjective`, `parametricValueFunction`, and `parametricValueFunction_def`
  in `Chap03/Lemma_3_3_6`, the earlier chapter owners for the pointwise scalar model
  `x ↦ max (f x - t) (fBar x)` and its feasible-set infimum;
- `constrainedThreshold` and `constrainedThreshold_eq_minimum_of_feasible_minimizer` in
  `Chap03/Lemma_3_3_4`, the chapter owner for exact threshold values on a feasible slice and the
  canonical attained-minimum realization of that threshold;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_mem_argmin` in
  `Chap01/Definition_1_3_7`, the project owner abstraction for attained constrained minima;
- `LagrangianProblem.constrainedAuxiliaryObjective` in `Chap02/Lemma_2_21`, the earlier project
  owner shape for the same objective-gap-plus-constraint maximum, now in a packaged finite-family
  setting;
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the more general finite maximum owner underlying that
  packaged construction.

Best owner abstraction:
- `parametricValueFunction Q f fBar`

Primitive data:
- the feasible set `Q`;
- the objective `f`;
- the constraint function `fBar`;
- the scalar parameter `t`.

Derived API:
- the upstream pointwise owner `setConstrainedParametricObjective f fBar t`;
- the owner argmin set `argmin[Q] (setConstrainedParametricObjective f fBar t)`;
- the existing exact-threshold owner
  `constrainedThreshold Q (fun _ _ ↦ f) (fun _ _ ↦ fBar) () ()`;
- the source-facing smallest-root statement for `parametricValueFunction Q f fBar`.

Source/core/bridge triage:
- source-facing: Proposition 3.52's smallest-root characterization for the scalar value function;
- core/canonical: `parametricValueFunction Q f fBar`;
- bridge/view: the pointwise objective `setConstrainedParametricObjective f fBar t`, together with
  the specialized threshold owner `constrainedThreshold` when one wants the attained feasible
  minimum rather than the root characterization.

The sampled finite-max owners from Chapters 1 and 2 confirm the mathematical domain, but they do
not provide an exact owner with the same unbundled interface as the textbook two-term model
`x ↦ max (f x - t) (fBar x)`. This file therefore keeps that pointwise objective only as a thin
bridge and centers the public proposition on the canonical value-function owner
`parametricValueFunction Q f fBar`. The exact threshold itself is already owned upstream by
`constrainedThreshold`, so no parallel local threshold definition is kept here.
-/

/-- Proposition 3.52: if `xStar ∈ argmin[Q ∩ {x | fBar x ≤ 0}] f` and every root of the owner
value function `parametricValueFunction Q f fBar` is attained by a minimizer of the corresponding
owner objective `setConstrainedParametricObjective f fBar t`, then `f xStar` is the smallest root
of `parametricValueFunction Q f fBar`. -/
-- Proof sketch: the exact feasible minimizer `xStar` makes the owner value at `t = f xStar`
-- equal to `0`. The exact-threshold owner from Lemma 3.3.4 identifies that same value with the
-- constrained threshold `t*[Q; (fun _ _ ↦ f); (fun _ _ ↦ fBar)]((), ())`. For `t < f xStar`, an
-- attained root would give a feasible point with `f x ≤ t`, forcing the exact threshold to be at
-- most `t`; the threshold identification then contradicts `t < f xStar`.
theorem optimalValue_is_smallest_root_of_parametricValueFunction
    {X : Type u} {Q : Set X} {f fBar : X → ℝ} {xStar : X}
    (hxStar : xStar ∈ argmin[Q ∩ {x | fBar x ≤ 0}] f)
    (hroot_attain : ∀ ⦃t : ℝ⦄, parametricValueFunction Q f fBar t = 0 →
      (argmin[Q] (setConstrainedParametricObjective f fBar t)).Nonempty) :
    IsLeast {t : ℝ | parametricValueFunction Q f fBar t = (0 : EReal)} (f xStar) := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_feasible, hxStar_min⟩
  rw [isMinOn_iff] at hxStar_min
  have hxStar_constraint : fBar xStar ≤ 0 := hxStar_feasible.2
  have hthreshold :
      t*[Q; (fun _ _ ↦ f); (fun _ _ ↦ fBar)]((), ()) = (f xStar : EReal) := by
    simpa using
      constrainedThreshold_eq_minimum_of_feasible_minimizer
        Q
        (fun _ _ ↦ f)
        (fun _ _ ↦ fBar)
        ()
        ()
        hxStar
  refine ⟨?_, ?_⟩
  · let problem : SetConstrainedMinimizationProblem X :=
      .mk Q (setConstrainedParametricObjective f fBar (f xStar))
    have hxStar_objective_zero :
        setConstrainedParametricObjective f fBar (f xStar) xStar = 0 := by
      calc
        setConstrainedParametricObjective f fBar (f xStar) xStar
            = max (f xStar - f xStar) (fBar xStar) := rfl
        _ = max 0 (fBar xStar) := by simp
        _ = 0 := by exact max_eq_left hxStar_constraint
    have hxStar_parametricMin :
        IsMinOn (setConstrainedParametricObjective f fBar (f xStar)) Q xStar := by
      rw [isMinOn_iff]
      intro y hyQ
      have hy_nonneg : 0 ≤ setConstrainedParametricObjective f fBar (f xStar) y := by
        by_cases hyBar : fBar y ≤ 0
        · have hy_feasible : y ∈ Q ∩ {x | fBar x ≤ 0} := ⟨hyQ, hyBar⟩
          have hy_obj_nonneg : 0 ≤ f y - f xStar := by
            exact sub_nonneg.mpr (hxStar_min y hy_feasible)
          simpa [setConstrainedParametricObjective] using
            (le_max_of_le_left hy_obj_nonneg :
              0 ≤ max (f y - f xStar) (fBar y))
        · have hyBar_nonneg : 0 ≤ fBar y := le_of_not_ge hyBar
          simpa [setConstrainedParametricObjective] using
            (le_max_of_le_right hyBar_nonneg :
              0 ≤ max (f y - f xStar) (fBar y))
      rw [hxStar_objective_zero]
      exact hy_nonneg
    have hvalue :
        parametricValueFunction Q f fBar (f xStar) =
          (setConstrainedParametricObjective f fBar (f xStar) xStar : EReal) := by
      simpa [parametricValueFunction, problem] using
        problem.optimalValue_eq_of_isMinOn hxStar_feasible.1 hxStar_parametricMin
    calc
      parametricValueFunction Q f fBar (f xStar) =
          (setConstrainedParametricObjective f fBar (f xStar) xStar : EReal) := hvalue
      _ = 0 := by exact_mod_cast hxStar_objective_zero
  · intro t ht
    by_contra htfx
    rcases hroot_attain ht with ⟨x, hx⟩
    rcases mem_constrainedArgmin_iff.mp hx with ⟨hxQ, _⟩
    let problem : SetConstrainedMinimizationProblem X :=
      .mk Q (setConstrainedParametricObjective f fBar t)
    have hvalue :
        parametricValueFunction Q f fBar t =
          (setConstrainedParametricObjective f fBar t x : EReal) := by
      simpa [parametricValueFunction, problem] using
        problem.optimalValue_eq_of_mem_argmin hx
    have hobjective_zero : setConstrainedParametricObjective f fBar t x = 0 := by
      have hobjective_zero' :
          ((setConstrainedParametricObjective f fBar t x : ℝ) : EReal) = 0 := by
        calc
          ((setConstrainedParametricObjective f fBar t x : ℝ) : EReal) =
              parametricValueFunction Q f fBar t := by
                simpa using hvalue.symm
          _ = 0 := ht
      exact_mod_cast hobjective_zero'
    have hobjective_le :
        setConstrainedParametricObjective f fBar t x ≤ 0 := by
      rw [hobjective_zero]
    have hx_components : f x - t ≤ 0 ∧ fBar x ≤ 0 := by
      simpa [setConstrainedParametricObjective] using (max_le_iff.mp hobjective_le)
    have hfx_le_t : f x ≤ t := by
      linarith
    have hx_exact_feasible : x ∈ Q ∩ {x | fBar x ≤ 0} := ⟨hxQ, hx_components.2⟩
    let exactProblem : SetConstrainedMinimizationProblem X :=
      .mk (Q ∩ {x | fBar x ≤ 0}) f
    have hthreshold_le_fx :
        t*[Q; (fun _ _ ↦ f); (fun _ _ ↦ fBar)]((), ()) ≤ (f x : EReal) := by
      simpa [constrainedThreshold, exactProblem] using
        exactProblem.optimalValue_le_of_mem_feasibleSet hx_exact_feasible
    have hthreshold_le_t :
        t*[Q; (fun _ _ ↦ f); (fun _ _ ↦ fBar)]((), ()) ≤ (t : EReal) :=
      hthreshold_le_fx.trans (by exact_mod_cast hfx_le_t)
    have hxStar_le_t : (f xStar : EReal) ≤ (t : EReal) := by
      simpa [hthreshold] using hthreshold_le_t
    exact htfx (by exact_mod_cast hxStar_le_t)

end
