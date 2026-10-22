/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped NonsmoothModelNotation

/- Definition 3.65 lies in the chapter's finite max-affine model domain for nonsmooth convex
optimization. The owner declaration already lives on an arbitrary real inner-product space, so
this recall keeps that canonical ambient generality instead of re-specializing it to `ℝⁿ`.

Sampled owner-style declarations:
- `nonsmoothModel` in `Lemma_3_3_2`, the earlier chapter owner for the finite maximum of sampled
  affine minorants
- `nonsmoothModel_apply` in `Lemma_3_3_2`, the pointwise evaluation bridge for that owner
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the ambient finite-maximum owner pattern specialized
  by `nonsmoothModel`
- `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the corresponding owner evaluation bridge

Best owner abstraction:
- `nonsmoothModel f xSeq g k`

Primitive data:
- the objective `f : E → ℝ`
- the sample sequence `xSeq : ℕ → E`
- the chosen sampled slopes `g : ℕ → E`
- the prefix length `k : ℕ`

Derived API:
- the source-facing notation `f̂[xSeq; f; g](k)` for the textbook model `\hat f_k(X; ·)`
- the explicit finite-maximum evaluation formula from `nonsmoothModel_apply`
- the later linear-program and quadratic-program reformulations in `Definition_3_69`
- the later pointwise domination lemmas in `Definition_3_73`

Source/core/bridge triage:
- source-facing: the textbook nonsmooth model `f̂[xSeq; f; g](k) = \hat f_k(X; ·)`
- core/canonical: `nonsmoothModel f xSeq g k`
- bridge/view: `nonsmoothModel_apply`

Definition 3.65 adds no new mathematical data beyond this existing owner declaration. This file is
therefore recall-only and introduces no parallel public alias such as `sampledAffineMaxModel`.
-/

recall nonsmoothModel {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (xSeq g : ℕ → E) (k : ℕ) :
    E → ℝ

section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (xSeq g : ℕ → E) (k : ℕ)

/- The source-facing notation `f̂[xSeq; f; g](k)` is the public theorem-surface spelling of the
recalled owner `nonsmoothModel f xSeq g k`. -/
#check (f̂[xSeq; f; g](k) : E → ℝ)

end

/- Evaluating the recalled nonsmooth model gives the textbook finite maximum over the sampled
affine minorants indexed by `i = 0, …, k`. -/
recall nonsmoothModel_apply
    {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (xSeq g : ℕ → E) (k : ℕ) (x : E) :
    f̂[xSeq; f; g](k) x =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (k + 1) ↦ f (xSeq i) + inner ℝ (g i) (x - xSeq i))

section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (xSeq g : ℕ → E) (k : ℕ) (x : E)

/- The recalled evaluation bridge already reads in the source-facing notation
`f̂[xSeq; f; g](k) x`. -/
#check
  (show f̂[xSeq; f; g](k) x =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (k + 1) ↦ f (xSeq i) + inner ℝ (g i) (x - xSeq i)) from
    nonsmoothModel_apply f xSeq g k x)

end
