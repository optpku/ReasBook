/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped ConstrainedArgmin ConstrainedThreshold

section

variable {Index : Type u} {Param : Type v} {Decision : Type w}
variable (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ)
variable (k : Index) (X : Param)

/-
Lemma 3.36 lies in the chapter's constrained-threshold / feasible-value domain.

Sampled owner-style declarations:
- `constrainedThreshold` in `Lemma_3_3_4`, the chapter owner for the threshold `t_k^*(X)` as the
  `EReal` infimum of the feasible objective values on the slice
  `Q ∩ {x | checkFn k X x ≤ 0}`;
- `constrainedThreshold_eq_minimum_of_feasible_minimizer` in `Lemma_3_3_4`, the source-facing
  attained-minimum form on the feasible slice `Q ∩ {x | checkFn k X x ≤ 0}`;
- `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_7`,
  the Chapter 1 owner bridge from the feasible slice to the corresponding `EReal` `sInf`;
- `IsLeast.csInf_eq` in mathlib, the canonical bridge from an attained least value of a set to the
  corresponding `sInf` identity.

Best owner abstraction:
- `t*[Q; hatFn; checkFn](k, X)`, with owner feasible-value image
  `(fun x ↦ (hatFn k X x : EReal)) '' (Q ∩ {x | checkFn k X x ≤ 0})`.

Primitive data:
- the ambient feasible set `Q`;
- the objective map `hatFn`;
- the constraint map `checkFn`;
- the index `k` and parameter `X`.

Derived API:
- the owner threshold `t*[Q; hatFn; checkFn](k, X)`;
- the real feasible objective-value set `(hatFn k X) '' (Q ∩ {x | checkFn k X x ≤ 0})`;
- the direct `sInf` identification from `IsLeast.csInf_eq`, used only internally after coercing
  that real value set into `EReal`.

Source/core/bridge triage:
- source-facing: Lemma 3.36's statement that the threshold equals the least feasible objective
  value when the real feasible objective-value set has a least element;
- core/canonical: `constrainedThreshold` from `Lemma_3_3_4`;
- bridge/view: `IsLeast.csInf_eq` on the internally coerced owner feasible-value image.

This file therefore keeps no parallel local copies of the feasible set or threshold. It only adds
the source-facing real-minimum consequence, proved by extracting a feasible minimizer and then
reusing the owner attained-minimum theorem from `Lemma_3_3_4`.
-/

/-- Lemma 3.36: if the feasible objective values attain a least element `m`, then `t_k^*(X)`
equals that minimum value. -/
-- Proof sketch: extract a feasible point whose objective value is `m`, show that point belongs to
-- the constrained argmin of the feasible slice, and then apply the owner attained-minimum bridge
-- `constrainedThreshold_eq_minimum_of_feasible_minimizer`.
lemma constrainedThreshold_eq_minimum_of_isLeast
    {m : ℝ}
    (hmin : IsLeast ((hatFn k X) '' (Q ∩ {x | checkFn k X x ≤ 0})) m) :
    t*[Q; hatFn; checkFn](k, X) = (m : EReal) := by
  rcases hmin.1 with ⟨xStar, hxStar, rfl⟩
  have hxStar_argmin : xStar ∈ argmin[Q ∩ {x | checkFn k X x ≤ 0}] (hatFn k X) := by
    rw [mem_constrainedArgmin_iff]
    refine ⟨hxStar, ?_⟩
    rw [isMinOn_iff]
    intro y hy
    exact hmin.2 ⟨y, hy, rfl⟩
  simpa using
    constrainedThreshold_eq_minimum_of_feasible_minimizer
      Q hatFn checkFn k X hxStar_argmin

end
