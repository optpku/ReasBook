/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_45

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Corollary 3.2.2 is a source-facing consequence in the chapter's constrained strong-convexity
domain on proper real normed spaces. The textbook finite-dimensional real inner-product-space case
is recovered by the canonical finite-dimensional properness instance.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- `StrongConvexOn.isBounded_constrainedSublevelSet` in `Theorem_3_45`
- `StrongConvexOn.existsUnique_isMinOn_of_isClosed` in `Theorem_3_45`

Best owner abstraction:
- source-facing: existence of a feasible minimizer on a nonempty closed feasible set
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: projection from the unique-minimizer owner theorem to the existence-only statement

Primitive data:
- a feasible set `Q`, an objective `f`, and a strong-convexity modulus `μ`
- the owner predicate `StrongConvexOn Q μ f`
- continuity of `f` on the feasible set

Derived API:
- boundedness of constrained sublevel sets
- under closed/nonempty feasible-set hypotheses, existence and uniqueness of a feasible minimizer
- the source-facing existence-only consequence extracted from the unique-minimizer owner theorem

Source/core/bridge triage:
- source-facing: Corollary 3.2.2, which stops at boundedness of constrained level sets and the
  resulting existence of an optimal solution
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: projection from the unique-minimizer owner theorem to the existence-only statement

The stronger uniqueness consequence is deferred to `Corollary_3_2_3`, so this file keeps the
bounded-sublevel owner theorem as the public center and exposes only the existence bridge needed
for the source text.
-/

recall StrongConvexOn.isBounded_constrainedSublevelSet

namespace StrongConvexOn

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Corollary 3.2.2: under the standing closed/nonempty feasible-set hypotheses of problem
`(3.2.13)`, a `μ`-strongly convex real-valued objective that is continuous on a closed nonempty
feasible set admits a feasible optimal solution. The textbook finite-dimensional Euclidean case is
the canonical specialization. -/
theorem exists_isMinOn_of_isClosed
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_cont : ContinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃ x : E, x ∈ Q ∧ IsMinOn f Q x :=
  (hf.existsUnique_isMinOn_of_isClosed hμ hf_cont hQ_nonempty hQ_closed).exists

end StrongConvexOn

end
