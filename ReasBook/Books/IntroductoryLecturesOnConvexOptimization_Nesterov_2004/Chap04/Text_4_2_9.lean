/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_10

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 4.2.9 is the subsection heading "Complexity of Non-degenerate Problems", so its primary
domain is the chapter's nondegenerate cubic-Newton complexity theory rather than the bilinear-form
`B`-geometry of `Definition_4_2_9`.

Mandatory domain-style sampling before refinement:
- `conditionNumberOfDegree` in `Definition_4_2_11`, the chapter owner of the conditioning ratio
  `γ[p](f) = σ[p](f) / L[p](f)`;
- `IsFirstOrderNondegenerate` in `Definition_4_2_15`, the source-facing owner for the
  nondegeneracy property itself;
- `cubic_newton_gap_le_linear_rate` in `Text_4_2_10`, the owner linear-rate estimate in this
  subsection;
- `cubic_newton_gap_le_of_iteration_count_bound` in `Text_4_2_10`, the owner iteration-complexity
  bound for the subsection.

Best owner abstraction:
- source-facing: Text 4.2.9 is a subsection-label item announcing the complexity theory for the
  nondegenerate regime;
- core/canonical: the subsection's complexity owner theorem
  `cubic_newton_gap_le_of_iteration_count_bound`;
- bridge/view: the one-step linear-rate estimate `cubic_newton_gap_le_linear_rate`, together with
  the conditioning owners `σ[p]`, `L[p]`, and `γ[p]`.

Primitive data:
- no new primitive mathematical data belong to this heading item itself.

Derived API:
- the subsection's canonical complexity theorem from `Text_4_2_10`.

This file therefore stays recall-only. The previous theorem about a linear-plus-cubic minimizer in
the `B`-induced geometry did not match the textbook semantics of 4.2.9 and duplicated an
unrelated owner layer. -/

/- Text 4.2.9 ("Complexity of Non-degenerate Problems"): the subsection's canonical complexity
surface is the cubic-Newton iteration bound stated in Text 4.2.10. -/
recall cubic_newton_gap_le_of_iteration_count_bound
