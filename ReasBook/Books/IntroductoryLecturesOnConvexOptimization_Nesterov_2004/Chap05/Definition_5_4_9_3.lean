/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.9.3 lies in the Chapter 5 logarithmic barrier / strict-epigraph domain.

Sampled owner declarations:
* `separableLogBarrierF4` from `Definition_5_4_8_12`, the existing Chapter 5 owner for the
  textbook scalar barrier `f(y, t) = -log t - log (t^(2 / p) - y^2)`;
* `separableLogBarrierF4_apply` from `Definition_5_4_8_12`, the coordinate evaluation bridge for
  that owner;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the chapter owner for strict epigraph
  domains;
* `mem_strictConstrainedEpigraph_iff` from `Theorem_5_3_5`, the canonical membership expansion
  for that owner.

Best owner abstraction:
* source-facing: the textbook scalar sub-function `f(y, t)`;
* core/canonical: the existing owner `separableLogBarrierF4 p : ℝ × ℝ → ℝ`;
* bridge/view: the strict-epigraph description of the points where the two logarithmic arguments
  are positive.

Primitive data:
* the scalar exponent `p`.

Derived API:
* the recalled owner `separableLogBarrierF4 p`;
* its coordinate formula `separableLogBarrierF4_apply`;
* the strict-epigraph bridge describing the natural finiteness domain.

This refinement removes the duplicate subtype-valued wrapper and keeps Definition 5.4.9.3 as a
recall of the existing Chapter 5 owner `separableLogBarrierF4`, with the domain side expressed
through the chapter strict-epigraph owner instead of a bespoke set definition. -/

recall separableLogBarrierF4
recall separableLogBarrierF4_apply
recall strictConstrainedEpigraph
recall mem_strictConstrainedEpigraph_iff

/- Definition 5.4.9.3 recalls the Chapter 5 owner `separableLogBarrierF4 p` for the textbook
sub-function `f(y, t) = -log t - log (t^(2 / p) - y^2)`. -/
variable (p : ℝ) in
#check separableLogBarrierF4 p

/-- The points where the textbook scalar barrier formula has positive logarithmic arguments are
exactly the points with `t > 0` for which `(y, t^(2 / p))` lies in the strict epigraph of the
square function. -/
theorem separableLogBarrierF4_domain_iff (p y t : ℝ) :
    0 < t ∧ 0 < Real.rpow t (2 / p) - y ^ 2 ↔
      0 < t ∧
        (y, Real.rpow t (2 / p)) ∈ strictConstrainedEpigraph Set.univ (fun x : ℝ ↦ x ^ 2) := by
  rw [mem_strictConstrainedEpigraph_iff]
  constructor
  · rintro ⟨ht, hgap⟩
    refine ⟨ht, Set.mem_univ _, ?_⟩
    linarith
  · rintro ⟨ht, ⟨_, hsq⟩⟩
    exact ⟨ht, by linarith⟩
