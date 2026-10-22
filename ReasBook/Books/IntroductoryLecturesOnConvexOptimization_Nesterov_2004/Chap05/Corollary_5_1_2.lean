/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

/- Corollary 5.1.2 lies in the Chapter 5 self-concordance / affine-quadratic perturbation domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner predicate;
* `IsSelfConcordantOnWith.add` from `Theorem_5_1_1`, the owner-level additive calculus theorem;
* `quadraticAffineObjective` from `Example_5_1_2`, the source-facing affine-quadratic owner;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  zero-self-concordance witness for that owner.

Best owner abstraction:
* `IsSelfConcordantOnWith` together with its additive calculus API.

Primitive data:
* the owner witness `hf : IsSelfConcordantOnWith dom Mf f`;
* the affine-quadratic perturbation data `α`, `a`, and `A`;
* the positivity witness `hA : A.IsPositive`.

Derived API:
* the self-concordance of `quadraticAffineObjective α a A` on `Set.univ` with constant `0`;
* the perturbation corollary below, obtained by the owner theorem `IsSelfConcordantOnWith.add`.

Source/core/bridge triage:
* source-facing: the textbook quadratic-affine perturbation corollary;
* core/canonical: `IsSelfConcordantOnWith.add`;
* bridge/view: the specialization supplied by
  `quadraticAffineObjective_isSelfConcordantOnWith_zero`.

The refined file therefore keeps the corollary as a thin source-facing bridge, rather than
introducing a parallel owner or restating the additive calculus in a second wrapper API. -/

-- Proof sketch: `quadraticAffineObjective α a A` is self-concordant on `Set.univ` with constant
-- `0` by Example 5.1.2. Apply the owner method `IsSelfConcordantOnWith.add` to this
-- quadratic-affine term and `f`; the intersection domain simplifies to `dom`, and the resulting
-- constant simplifies from `max 0 Mf` to `Mf`.
/-- Corollary 5.1.2: if `f` is self-concordant on an open convex domain `dom ⊆ E` with
self-concordance constant `M_f`, then the quadratic-affine perturbation
`φ(x) = α + ⟪a, x⟫ + (1 / 2) ⟪Ax, x⟫ + f(x)` is self-concordant on `dom` with the same
self-concordance constant `M_f` whenever `A` is positive semidefinite. This reuses the canonical
Chapter 5 owner `quadraticAffineObjective α a A`. -/
theorem add_quadraticAffineObjective
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hf : IsSelfConcordantOnWith dom Mf f)
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsSelfConcordantOnWith dom Mf (quadraticAffineObjective α a A + f) := by
  simpa using (quadraticAffineObjective_isSelfConcordantOnWith_zero α a A hA).add hf

end IsSelfConcordantOnWith

end
