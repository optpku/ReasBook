/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped ConstrainedArgmin

section

variable {Index : Type u} {Param : Type v} {Decision : Type w}

/-
Lemma 3.3.4 lies in the chapter's constrained-threshold / set-constrained minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the chapter owner
  for feasible minimizers on a fixed feasible slice;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in
  `Chap01/Definition_1_3_7`, the canonical owner optimal-value API on the feasible slice;
- mathlib `sInf`, used only in the companion upper-bound presentation after coercing the
  source-facing real upper bounds into `EReal`.

Best owner abstraction:
- source-facing: the textbook threshold `constrainedThreshold Q hatFn checkFn k X`;
- core/canonical: the feasible-slice owner
  `(.mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X) :
    SetConstrainedMinimizationProblem Decision).optimalValue`;
- bridge/view: the `EReal` infimum of the real upper-bound set attached to the same feasible
  slice.

Primitive data:
- the feasible set `Q`;
- the objective family `hatFn`;
- the constraint family `checkFn`;
- the stage/index data `k` and `X`.

Derived API:
- the source-facing threshold `constrainedThreshold Q hatFn checkFn k X`;
- the upper-bound presentation in `constrainedThreshold_def`;
- the direct attained-minimum identification of the threshold;
- the direct feasible-slice owner expression when downstream arguments genuinely need the
  Chapter 1 packaged API.

Source/core/bridge triage:
- source-facing: the textbook threshold `t_k^*(X)`;
- core/canonical: the direct feasible-slice owner optimal value;
- bridge/view: the `sInf` presentation of the corresponding real upper-bound set in `EReal`.

The threshold itself remains the source-facing owner because it is a named chapter object, but
its definition now reuses the Chapter 1 owner `optimalValue` so empty or unbounded-below feasible
slices are represented faithfully in `EReal`. The feasible-slice
`SetConstrainedMinimizationProblem` is kept only as a direct bridge expression, not as a second
public owner with wrapper lemmas.
-/

/-- The threshold value `t_k^*(X)` defined as the infimum of `hatFn k X` on the feasible slice
`Q ∩ {x | checkFn k X x ≤ 0}`, viewed in `EReal` so empty or unbounded-below slices are
represented faithfully. -/
noncomputable def constrainedThreshold
    (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ) (k : Index)
    (X : Param) : EReal :=
  (SetConstrainedMinimizationProblem.mk
      (Q ∩ {x | checkFn k X x ≤ 0})
      (hatFn k X)).optimalValue

namespace ConstrainedThreshold

scoped notation:max "t*[" Q "; " hatFn "; " checkFn "](" k ", " X ")" =>
  constrainedThreshold Q hatFn checkFn k X

end ConstrainedThreshold

open scoped ConstrainedThreshold

/-- Recovering the source-facing upper-bound presentation of `constrainedThreshold`. -/
-- Proof sketch: package the feasible slice as a `SetConstrainedMinimizationProblem`, expand the
-- owner optimal value as an `EReal` infimum of the feasible objective-value image, and identify
-- that image with the coerced real upper-bound set attached to the same slice.
theorem constrainedThreshold_def
    (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ) (k : Index)
    (X : Param) :
    t*[Q; hatFn; checkFn](k, X) =
      sInf (((↑) : ℝ → EReal) ''
        {t : ℝ | ∃ x ∈ Q, hatFn k X x ≤ t ∧ checkFn k X x ≤ 0}) := by
  let feasibleValues : Set EReal :=
    (fun x ↦ (hatFn k X x : EReal)) '' (Q ∩ {x | checkFn k X x ≤ 0})
  let upperBounds : Set EReal :=
    ((↑) : ℝ → EReal) '' {t : ℝ | ∃ x ∈ Q, hatFn k X x ≤ t ∧ checkFn k X x ≤ 0}
  have hthreshold :
      t*[Q; hatFn; checkFn](k, X) = sInf feasibleValues := by
    let problem : SetConstrainedMinimizationProblem Decision :=
      .mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X)
    simpa [constrainedThreshold, feasibleValues, problem] using
      problem.optimalValue_eq_sInf_image
  have hfeasible_le_upper : sInf feasibleValues ≤ sInf upperBounds := by
    refine le_sInf ?_
    rintro _ ⟨t, ⟨x, hxQ, hhat, hcheck⟩, rfl⟩
    have hx : ((hatFn k X x : ℝ) : EReal) ∈ feasibleValues := by
      exact ⟨x, ⟨hxQ, hcheck⟩, rfl⟩
    have hhat' : ((hatFn k X x : ℝ) : EReal) ≤ t := by
      exact_mod_cast hhat
    exact (csInf_le ⟨⊥, fun _ _ ↦ bot_le⟩ hx).trans hhat'
  have hupper_le_feasible : sInf upperBounds ≤ sInf feasibleValues := by
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ((hatFn k X x : ℝ) : EReal) ∈ upperBounds := by
      refine ⟨hatFn k X x, ?_, rfl⟩
      exact ⟨x, hx.1, le_rfl, hx.2⟩
    exact csInf_le ⟨⊥, fun _ _ ↦ bot_le⟩ hx'
  have hsInf_eq : sInf upperBounds = sInf feasibleValues := by
    exact le_antisymm hupper_le_feasible hfeasible_le_upper
  calc
    t*[Q; hatFn; checkFn](k, X) = sInf feasibleValues := hthreshold
    _ = sInf upperBounds := hsInf_eq.symm
    _ =
        sInf (((↑) : ℝ → EReal) ''
          {t : ℝ | ∃ x ∈ Q, hatFn k X x ≤ t ∧ checkFn k X x ≤ 0}) := rfl

/-- Lemma 3.3.4: if `xStar` attains the minimum of `hatFn k X` on the feasible set
`Q ∩ {x | checkFn k X x ≤ 0}`, then `t_k^*(X)` equals that constrained minimum value. -/
-- Proof sketch: package the feasible slice as a `SetConstrainedMinimizationProblem` and apply
-- the Chapter 1 owner theorem `optimalValue_eq_of_isMinOn`.
theorem constrainedThreshold_eq_minimum_of_feasible_minimizer
    (Q : Set Decision) (hatFn checkFn : Index → Param → Decision → ℝ) (k : Index)
    (X : Param) {xStar : Decision}
    (hxStar : xStar ∈ argmin[Q ∩ {x | checkFn k X x ≤ 0}] (hatFn k X)) :
    t*[Q; hatFn; checkFn](k, X) = (hatFn k X xStar : EReal) := by
  rw [mem_constrainedArgmin_iff] at hxStar
  let problem : SetConstrainedMinimizationProblem Decision :=
    .mk (Q ∩ {x | checkFn k X x ≤ 0}) (hatFn k X)
  simpa [constrainedThreshold, problem] using
    problem.optimalValue_eq_of_isMinOn hxStar.1 hxStar.2

end
