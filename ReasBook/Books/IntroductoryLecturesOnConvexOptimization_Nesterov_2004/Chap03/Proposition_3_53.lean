/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_52

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped ConstrainedArgmin ConstrainedThreshold

section

variable {Index : Type u} {Param : Type v} {Decision : Type w}

/- Proposition 3.53 lies in the chapter's constrained parametric-value / threshold-comparison
domain from §3.3.4.

Mandatory domain-style sampling before refinement:
- `constrainedThreshold` and `constrainedThreshold_eq_minimum_of_feasible_minimizer` in
  `Chap03/Lemma_3_3_4`, the chapter owner for the model root `t_k^*(X)` and its attained-minimum
  realization on the feasible slice;
- `parametricValueFunction` in `Chap03/Lemma_3_3_6`, the chapter owner for the exact and model
  scalar value functions `t ↦ min_{x ∈ Q} max (f x - t) (fBar x)`;
- `optimalValue_is_smallest_root_of_parametricValueFunction` in `Chap03/Proposition_3_52`, the
  canonical least-root theorem for the exact parametric value function;
- `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet` in
  `Chap01/Definition_1_3_7`, the canonical owner upper-bound theorem for evaluating the threshold
  at one feasible model point.

Best owner abstraction:
- source-facing: the chapter threshold `constrainedThreshold Q hatFn checkFn k X`, i.e. the model
  smallest root `t_k^*(X)`;
- core/canonical: `constrainedThreshold` itself, both for the model threshold
  `constrainedThreshold Q hatFn checkFn k X` and for the exact threshold specialization
  `constrainedThreshold Q (fun _ _ ↦ f) (fun _ _ ↦ fBar) () ()`;
- bridge/view: pointwise model domination on `Q`, which turns the exact feasible minimizer into a
  feasible upper bound for the model threshold, together with Proposition 3.52's least-root
  theorem for the exact value function.

Primitive data:
- the feasible set `Q`;
- the model objective/constraint pair `hatFn k X`, `checkFn k X`;
- the exact objective/constraint pair `f`, `fBar`;
- a chosen exact feasible minimizer `xStar`.

Derived API:
- the model threshold `constrainedThreshold Q hatFn checkFn k X`;
- the direct comparison `constrainedThreshold Q hatFn checkFn k X ≤ f xStar`;
- the owner-level comparison with the exact threshold specialization
  `constrainedThreshold Q (fun _ _ ↦ f) (fun _ _ ↦ fBar) () ()`;
- the Proposition 3.52 bridge
  `IsLeast {t : ℝ | parametricValueFunction Q f fBar t = 0} (f xStar)` in the local
  `argmin` vocabulary.

Source/core/bridge triage:
- source-facing: Proposition 3.53's direct comparison `t_k^*(X) ≤ f xStar`;
- core/canonical: `constrainedThreshold`;
- bridge/view: the pointwise inequalities `hatFn k X ≤ f` and `checkFn k X ≤ fBar` on `Q`,
  together with the attained-minimum identification of the exact threshold via
  `constrainedThreshold_eq_minimum_of_feasible_minimizer` and the least-root characterization
  from `optimalValue_is_smallest_root_of_parametricValueFunction`.

The previous version drifted to a generic theorem about arbitrary least nonpositive parameters of
scalar functions and then made a parallel exact-threshold owner the main conclusion. The source-
facing statement here is restored to the direct chapter comparison
`constrainedThreshold … ≤ f xStar`, and the companion exact-threshold comparison now reuses the
same owner `constrainedThreshold` specialized to the exact data instead of introducing a second
threshold API. The Proposition 3.52 bridge is exposed through its actual `IsLeast` theorem rather
than through a parallel local root wrapper.
-/

variable {Q : Set Decision} {hatFn checkFn : Index → Param → Decision → ℝ}
variable {k : Index} {X : Param} {f fBar : Decision → ℝ}

/-- If `xStar` is feasible for the exact constrained problem and its model objective/constraint
values are bounded by the exact ones at that same point, then the model threshold is at most
`f xStar`. -/
-- Proof sketch: the pointwise comparison at `xStar` makes the exact feasible point feasible for
-- the model slice `Q ∩ {x | checkFn k X x ≤ 0}`. Since `constrainedThreshold` is the infimum of
-- `hatFn k X` on that slice, it is bounded above by `hatFn k X xStar`, hence by `f xStar`.
theorem constrainedThreshold_le_of_feasible_pointwise_bounds
    {xStar : Decision}
    (hxStar : xStar ∈ Q ∩ {x | fBar x ≤ 0})
    (hhat_le : hatFn k X xStar ≤ f xStar)
    (hcheck_le : checkFn k X xStar ≤ fBar xStar) :
    t*[Q; hatFn; checkFn](k, X) ≤ f xStar := by
  have hxStar_model_feasible : xStar ∈ Q ∩ {x | checkFn k X x ≤ 0} := by
    refine ⟨hxStar.1, ?_⟩
    exact hcheck_le.trans hxStar.2
  let modelProblem : SetConstrainedMinimizationProblem Decision :=
    .mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X)
  have hthreshold_le_hat : t*[Q; hatFn; checkFn](k, X) ≤ (hatFn k X xStar : EReal) := by
    simpa [constrainedThreshold, modelProblem] using
      modelProblem.optimalValue_le_of_mem_feasibleSet hxStar_model_feasible
  have hhat_le' : (hatFn k X xStar : EReal) ≤ f xStar := by
    exact_mod_cast hhat_le
  exact hthreshold_le_hat.trans hhat_le'

/-- Proposition 3.53: if the model objective and model constraint are pointwise dominated by the
exact objective and exact constraint on `Q`, then the model threshold `t_k^*(X)` is bounded above
by the exact feasible optimum value `f xStar`. -/
-- Proof sketch: the pointwise domination on `Q` specializes at the exact feasible minimizer
-- `xStar`, so `constrainedThreshold` is at most `f xStar` by the feasible-point bridge above.
theorem constrainedThreshold_le_of_pointwise_le
    {xStar : Decision}
    (hxStar : xStar ∈ argmin[Q ∩ {x | fBar x ≤ 0}] f)
    (hhat_le : ∀ ⦃x : Decision⦄, x ∈ Q → hatFn k X x ≤ f x)
    (hcheck_le : ∀ ⦃x : Decision⦄, x ∈ Q → checkFn k X x ≤ fBar x) :
    t*[Q; hatFn; checkFn](k, X) ≤ f xStar := by
  rw [mem_constrainedArgmin_iff] at hxStar
  exact constrainedThreshold_le_of_feasible_pointwise_bounds
    hxStar.1
    (hhat_le hxStar.1.1)
    (hcheck_le hxStar.1.1)

/-- Pointwise domination of the model objective and constraint on `Q` yields the corresponding
owner-level comparison with the exact threshold, reusing `constrainedThreshold` specialized to
the exact data `(f, fBar)`. -/
theorem constrainedThreshold_le_exactThreshold_of_pointwise_le
    (hhat_le : ∀ ⦃x : Decision⦄, x ∈ Q → hatFn k X x ≤ f x)
    (hcheck_le : ∀ ⦃x : Decision⦄, x ∈ Q → checkFn k X x ≤ fBar x) :
    t*[Q; hatFn; checkFn](k, X) ≤
      t*[Q; (fun _ _ ↦ f); (fun _ _ ↦ fBar)]((), ()) := by
  let modelProblem : SetConstrainedMinimizationProblem Decision :=
    .mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X)
  let restrictedExactProblem : SetConstrainedMinimizationProblem Decision :=
    .mk (Q ∩ {x | fBar x ≤ 0}) (hatFn k X)
  let exactProblem : SetConstrainedMinimizationProblem Decision :=
    .mk (Q ∩ {x | fBar x ≤ 0}) f
  have hmodel_le_restricted : modelProblem.optimalValue ≤ restrictedExactProblem.optimalValue := by
    rw [restrictedExactProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hxExact, rfl⟩
    have hxModel : x ∈ modelProblem.feasibleSet := by
      refine ⟨hxExact.1, ?_⟩
      exact (hcheck_le hxExact.1).trans hxExact.2
    simpa [modelProblem] using modelProblem.optimalValue_le_of_mem_feasibleSet hxModel
  have hrestricted_le_exact :
      restrictedExactProblem.optimalValue ≤ exactProblem.optimalValue := by
    refine SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      restrictedExactProblem
      exactProblem
      rfl
      ?_
    intro x hx
    exact hhat_le hx.1
  simpa [constrainedThreshold, modelProblem, exactProblem] using
    hmodel_le_restricted.trans hrestricted_le_exact

end
