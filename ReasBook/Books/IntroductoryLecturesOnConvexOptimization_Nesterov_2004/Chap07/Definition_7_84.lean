/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

/- Domain review for this item: it lies in the chapter's dual-norm domain.

Layer targeted by this refinement:
- source-facing recall of the canonical Chapter 2 dual-norm owner

Primary domain:
- dual norms of separated seminorms on Euclidean spaces `ℝⁿ`.

Sampled owner-style declarations:
- mathlib `Seminorm.closedBall_zero_eq`
- mathlib `normSeminorm`
- project `Seminorm.IsNorm` in `Chap02/Definition_2_5`
- project `Seminorm.dualNorm` and `Seminorm.dualNorm_apply` in `Chap02/Definition_2_5`

Best owner abstraction:
- `Seminorm.dualNorm p` on a real inner-product space

Primitive data:
- a seminorm `p : Seminorm ℝ E`
- a real inner-product-space structure on `E`
- the separation hypothesis `[p.IsNorm]`

Derived API:
- `Seminorm.dualNorm_apply`
- the Euclidean specialization `Seminorm.dualNorm_normSeminorm_eq_norm`

Source/core/bridge triage:
- source-facing: the textbook dual norm attached to a norm on `ℝⁿ`
- core/canonical: `Seminorm.dualNorm p`
- bridge/view: `Seminorm.dualNorm_apply`

The previous version rebuilt `Seminorm.IsNorm`, the ambient-norm `IsNorm` instance, `dualNorm`,
and `dualNorm_apply` locally inside Chapter 7. Those owners already belong to Chapter 2 and are
recalled again in Chapter 3, so keeping a second Chapter 7 copy only widened the API surface.
This file now recalls the canonical owner directly and leaves the support-class import transitively
available through `Chap02/Definition_2_5` for downstream files.
-/

namespace Seminorm

/- Definition 7.84: for a norm `‖·‖` on `ℝⁿ`, the dual norm is the support function of the
closed unit ball. In the canonical project API this owner is `Seminorm.dualNorm p` for a
separated seminorm `p` on a real inner-product space. -/
recall dualNorm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Seminorm ℝ E) [p.IsNorm] :
    E → ℝ

/- The defining support-function formula is recalled through the canonical companion theorem. -/
recall dualNorm_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Seminorm ℝ E) [p.IsNorm] (g : E) :
    p.dualNorm g = sSup ((fun x ↦ inner ℝ g x) '' {x | p x ≤ 1})

end Seminorm
