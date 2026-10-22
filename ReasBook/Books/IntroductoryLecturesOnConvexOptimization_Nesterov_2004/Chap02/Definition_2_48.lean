/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothFunctionalConstraintsMinimizationProblem

/- Primary domain: Chapter 2 root updates for the constrained regularized model-value owner of
smooth functional-constraint minimization problems on a real Hilbert space.

Sampled owner-style declarations:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44.lean`, the owner ambient
  constrained problem carrying the feasible set, objective, and constraints;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, the fixed-`t` bridge to the chapter's smooth minimax owner;
* `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue` in
  `Definition_2_47.lean`, the owner constrained regularized affine-model value whose zero-set
  threshold defines the textbook update;
* `constrainedThreshold` in `Chap03/Lemma_3_3_4.lean`, a project owner pattern where the source
  threshold is exposed directly as an infimum owner and its defining sign laws are companion
  theorems rather than primitive wrapper data.

Best owner abstraction:
* `problem.regularizedModelValueRoot xBar t`.

Primitive data:
* the constrained problem `problem`;
* the base point `xBar`;
* the current parameter `t`.

Derived API:
* the owner regularized model value `problem.regularizedModelValue`;
* the explicit threshold set
  `{τ : ℝ | t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0}` defining the owner update;
* the defining `sInf` specification theorem for the owner update.

Source/core/bridge triage:
* source-facing: the textbook update `t^*(xBar, t)`;
* core/canonical: the owner root operator `problem.regularizedModelValueRoot xBar t`;
* bridge/view: no additional public bridge is needed here, because the numbered item is already
  the owner scalar update rather than a comparison construction.

This file therefore keeps the source-facing update itself as the public owner. It introduces no
parallel scalar-function parameter, chosen-root structure, equality-wrapper compatibility API, or
packaging layer around the zero-set description. The only companion bridge theorem retained here is
the direct `sInf` expansion of the defining threshold set, together with the least-root theorem
under the natural convexity and root-existence hypotheses. -/

/-- Definition 2.48: the textbook update `t^*(xBar, t)` is the infimum of the roots of the owner
constrained regularized model value `τ ↦ problem.regularizedModelValue τ xBar μ` that are not
smaller than the current parameter `t`. -/
def regularizedModelValueRoot
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (xBar : E) (t : ℝ) : ℝ :=
  sInf {τ : ℝ | t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0}

end SmoothFunctionalConstraintsMinimizationProblem

namespace RegularizedModelValueRootNotation

/- Pointwise source-facing Lean notation for the textbook update `t^*(xBar, t)`. -/
scoped notation:max "t★[" problem:arg "; " xBar:arg "]" "(" t:arg ")" =>
  SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValueRoot problem xBar t

end RegularizedModelValueRootNotation

open scoped RegularizedModelValueRootNotation

namespace SmoothFunctionalConstraintsMinimizationProblem

/-- Expanding `t★[problem; xBar](t)` recovers the defining threshold set of roots of the owner
regularized `μ`-model value above the current parameter `t`. -/
theorem regularizedModelValueRoot_eq_sInf
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (xBar : E) (t : ℝ) :
    t★[problem; xBar](t) =
      sInf {τ : ℝ | t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0} :=
  rfl

/-- If the scalar owner map `τ ↦ problem.regularizedModelValue τ xBar μ` is convex and admits a
root at some parameter `τ ≥ t`, then the textbook update `t★[problem; xBar](t)` is genuinely the
least root of that map among parameters not smaller than `t`. This is the mathematically correct
smallest-root API companion to the defining `sInf` expression. -/
theorem regularizedModelValueRoot_isLeast_of_convexOn
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (xBar : E) (t : ℝ)
    (hconvex : ConvexOn ℝ Set.univ (fun τ ↦ problem.regularizedModelValue τ xBar μ))
    (hroot : ∃ τ : ℝ, t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0) :
    IsLeast
      {τ : ℝ | t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0}
      (t★[problem; xBar](t)) := by
  let roots : Set ℝ := {τ : ℝ | t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0}
  have hcont : Continuous fun τ ↦ problem.regularizedModelValue τ xBar μ := by
    simpa [continuousOn_univ] using hconvex.continuousOn isOpen_univ
  have hclosed : IsClosed roots := by
    refine isClosed_Ici.inter ?_
    exact isClosed_singleton.preimage hcont
  have hnonempty : roots.Nonempty := by
    rcases hroot with ⟨τ, hτ, hzero⟩
    exact ⟨τ, hτ, hzero⟩
  have hbddBelow : BddBelow roots := by
    refine ⟨t, ?_⟩
    intro τ hτ
    exact hτ.1
  simpa [regularizedModelValueRoot, roots] using hclosed.isLeast_csInf hnonempty hbddBelow

/-- Under the convexity and root-existence hypotheses that make Definition 2.48 mathematically
well posed, the textbook update itself lies in the root set above `t`. -/
theorem regularizedModelValueRoot_mem_of_convexOn
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (xBar : E) (t : ℝ)
    (hconvex : ConvexOn ℝ Set.univ (fun τ ↦ problem.regularizedModelValue τ xBar μ))
    (hroot : ∃ τ : ℝ, t ≤ τ ∧ problem.regularizedModelValue τ xBar μ = 0) :
    t ≤ t★[problem; xBar](t) ∧
      problem.regularizedModelValue (t★[problem; xBar](t)) xBar μ = 0 :=
  (problem.regularizedModelValueRoot_isLeast_of_convexOn xBar t hconvex hroot).1

end SmoothFunctionalConstraintsMinimizationProblem
