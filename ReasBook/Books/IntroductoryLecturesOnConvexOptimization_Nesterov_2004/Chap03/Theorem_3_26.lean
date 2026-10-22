/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

/- Theorem 3.26 is a `bridge/view` recall in the chapter's extended-valued
homogeneous-subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces, with effective
  domains, subgradients, and positive homogeneity on cones.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter bridge from extended values to the
  effective-domain real part;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner API for
  subgradients;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity;
- `euler_homogeneous_function_theorem` in `Theorem_3_1_21`, the exact upstream chapter theorem
  with the target interface;
- the inner-product evaluation `inner ℝ g x`, the canonical pairing available in the current
  ambient real inner-product-space owner.

Best owner abstraction:
- `euler_homogeneous_function_theorem` on the owner data
  `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)` and `g ∈ ∂ f(x)`.

Primitive data:
- an extended-valued function `f : E → WithTop ℝ`;
- a degree `p : ℝ`;
- the owner homogeneity hypothesis `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)`;
- a subgradient witness `hg : g ∈ ∂ f(x)`.

Derived API:
- the Euler identity `inner ℝ g x = p * withTopRealPart f x`, already provided upstream by
  `euler_homogeneous_function_theorem`.

Source/core/bridge triage:
- source-facing: the numbered Euler identity for homogeneous extended-valued functions;
- core/canonical: `euler_homogeneous_function_theorem`;
- bridge/view: this numbered restatement, expressed on the chapter owners `dom f`,
  `withTopRealPart f`, `∂ f(x)`, and `IsPositivelyHomogeneousOn`.

The textbook states the result for convex functions on `ℝ^n` and assumes subdifferentiability at
every point of `dom f`, but the actual identity only uses the chosen subgradient witness
`g ∈ ∂ f(x)` together with homogeneity on the effective domain. The public statement therefore
keeps the source meaning while removing those redundant global assumptions and the unnecessary
coordinate specialization. Since the exact theorem already exists upstream in
`Theorem_3_1_21`, this file recalls that canonical declaration directly instead of keeping a
parallel local theorem name.
-/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Theorem 3.26: if an `ℝ ∪ {+∞}`-valued function is homogeneous of degree `p` on its effective
domain, then every subgradient at `x` pairs with `x` to give `p` times the finite real part of the
function value at `x`.
-/
recall euler_homogeneous_function_theorem
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    inner ℝ g x = p * withTopRealPart f x
