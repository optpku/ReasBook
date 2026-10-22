/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
This item is a recall-only entry in the chapter's dual-norm domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical dual-norm owner already defined in Chapter 2

Primary domain:
- dual norms of separated seminorms on Euclidean spaces `ℝⁿ`.

Sampled owner-style declarations:
- mathlib `Seminorm.closedBall_zero_eq`
- mathlib `normSeminorm`
- project `Seminorm.dualNorm`
- project `Seminorm.dualNorm_apply`

Best owner abstraction:
- `Seminorm.dualNorm p` on a real inner-product space

Primitive data:
- a seminorm `p : Seminorm ℝ E`
- a real inner-product-space structure on `E`
- the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
- `Seminorm.dualNorm_apply`
- the Euclidean specialization `Seminorm.dualNorm_normSeminorm_eq_norm`

Source/core/bridge triage:
- source-facing: the textbook dual norm attached to a norm or separated seminorm on `ℝⁿ`
- core/canonical: `Seminorm.dualNorm p` on a real inner-product space
- bridge/view: `Seminorm.dualNorm_apply`

The owner declarations already exist upstream in Chapter 2, so this file recalls only the dual
norm owner and its defining bridge formula instead of keeping a parallel Chapter 3 wrapper such
as `dualSeminorm` or re-recalling the support class `Seminorm.IsNorm`. Downstream Chapter 3
files should import this recall file rather than reaching back to Chapter 2 directly.
-/

open scoped SeminormDualNorm

namespace Seminorm

/- Definition 3.20: the dual norm attached to a norm on `ℝⁿ` is recalled through the canonical
Chapter 2 owner `Seminorm.dualNorm`, whose value at `g` is the maximum of `⟪g, x⟫` over the
closed unit ball of the primal norm. -/
recall dualNorm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] :
    E → ℝ

/- The defining support-function formula is recalled through the canonical companion theorem, on
the source-facing notation `‖g‖[p,*]`. -/
recall dualNorm_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Seminorm ℝ E) [FiniteDimensional ℝ E] [p.IsNorm] (g : E) :
    ‖g‖[p,*] = sSup ((fun x ↦ inner ℝ g x) '' {x | p x ≤ 1})

end Seminorm
