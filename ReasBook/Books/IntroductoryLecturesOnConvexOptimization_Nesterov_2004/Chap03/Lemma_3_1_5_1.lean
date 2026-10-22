/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/-
Lemma 3.1.5.1 lies in the chapter's extended-valued constrained-subdifferential / closed-convex
domain.

Sampled owner-style declarations:
- `∂[Q] f(x)` / `constrainedSubdifferential` in `Definition_3_1_5`, the owner local subgradient
  object;
- `mem_constrainedSubdifferential_iff` in `Definition_3_1_5`, the atomic membership expansion for
  that owner;
- `convexOn_of_constrainedSubdifferential_nonempty` in `Lemma_3_6`, the canonical convexity
  consequence of pointwise constrained-subdifferential nonemptiness;
- `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty` in `Lemma_3_6`, the companion
  lower-semicontinuity consequence.

Best owner abstraction:
- the constrained-subdifferential owner `∂[Q] f(x)` together with its atomic membership lemma;
- the two exact owner consequences already proved in `Lemma_3_6`.

Primitive data:
- the feasible set `Q`;
- the `WithTop ℝ`-valued objective `f`;
- pointwise nonemptiness of `∂[Q] f(x)` on `Q`.

Derived API in this file:
- the atomic finiteness consequence `Q ⊆ dom f`;
- the exact owner recalls for convexity and lower semicontinuity on `Q`.

Source/core/bridge triage:
- source-facing: the textbook pointwise-subgradient hypothesis and its atomic finiteness
  consequence `Q ⊆ dom f`;
- core/canonical: `dom f`, `∂[Q] f(x)`, `mem_constrainedSubdifferential_iff`, and the two owner
  consequence theorems from `Lemma_3_6`;
- bridge/view: none in this file.

This file therefore keeps only the genuinely new atomic finiteness theorem at the weakest ambient
subgradient layer, and reuses the exact convexity and lower-semicontinuity owner theorems by
direct recall instead of exporting a stronger repackaging layer.
-/

section DomainFiniteness

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Q : Set V} {f : V → WithTop ℝ}

/-- Lemma 3.1.5.1: if every point of `Q` has a nonempty constrained subdifferential, then `f` is
finite on `Q`. The convexity conclusion, which does require convexity of `Q`, and the companion
lower-semicontinuity conclusion are already the exact owner theorems recalled just below. -/
-- Proof sketch: membership in `∂[Q] f(x)` already contains the primitive
-- domain fact `x ∈ dom f`, so pointwise nonemptiness on `Q` immediately yields `Q ⊆ dom f`.
theorem subset_withTopEffectiveDomain_of_constrainedSubdifferential_nonempty
    (hsubgrad : ∀ x ∈ Q, (∂[Q] f(x)).Nonempty) :
    Q ⊆ dom f := by
  intro x hx
  rcases hsubgrad x hx with ⟨g, hg⟩
  simpa using (mem_constrainedSubdifferential_iff.mp hg).2.1

end DomainFiniteness

section RecallConsequences

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {f : E → WithTop ℝ}

/- Lemma 3.1.5.1's convexity conclusion is the exact owner theorem already proved in `Lemma_3_6`.
The hypothesis block stays source-faithful; only the redundant local wrapper is removed. -/
recall convexOn_of_constrainedSubdifferential_nonempty

/- Lemma 3.1.5.1's lower-semicontinuity conclusion is the exact owner theorem already proved in
`Lemma_3_6`. -/
recall lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty

end RecallConsequences

end
