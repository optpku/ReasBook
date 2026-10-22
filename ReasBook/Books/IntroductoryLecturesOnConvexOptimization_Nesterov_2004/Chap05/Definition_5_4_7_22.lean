/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u}

/- Definition 5.4.7.22 lies in the Chapter 5 self-concordant-barrier / exponential-transform
domain.

Sampled owner-style declarations before refinement:
* `Set.restrict` from mathlib `Data/Set/Restrict`, the canonical owner for restricting an ambient
  map to a subtype domain;
* `barrierExponentialTransform` in `Lemma_5_3_1`, the ambient owner
  `x ↦ exp (-(F x / p))` for positive barrier parameters `p : NNRealˣ`;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, which already uses that
  ambient owner on `dom`;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the source-facing
  Chapter 5 equivalence stated through the same ambient transform;
* `isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound` in `Theorem_5_3_7`, the
  downstream theorem that continues to use that ambient owner surface.

Best owner abstraction:
* core/canonical: `barrierExponentialTransform p F`;
* bridge/view: its canonical restriction `dom.restrict ...` to the source domain subtype.

Primitive data:
* the domain `dom`;
* the positive exponent parameter `p`;
* the barrier `F`.

Derived API:
* the direct source-domain view `dom.restrict (barrierExponentialTransform p F)`.

Source/core/bridge triage:
* source-facing: the function `ξₚ` on `dom`, viewed directly as the restricted ambient transform;
* core/canonical: the ambient exponential transform on `E`;
* bridge/view: this numbered file, which is recall-only because the exact restricted composite is
  already available from the upstream owners.

The previous version introduced the duplicate public wrapper `barrierExponent` for this restricted
composite. Under the chapter's exact-interface reuse rule, Definition 5.4.7.22 should instead stay
at direct recall/check surface for the canonical restriction of the ambient owner. -/

section

variable (dom : Set E) (p : NNRealˣ) (F : E → ℝ)

set_option linter.hashCommand false in
/- Definition 5.4.7.22 recalls the source-domain restriction of the Chapter 5 ambient exponential
transform. -/
#check (dom.restrict (barrierExponentialTransform p F) : dom → ℝ)

end

end
