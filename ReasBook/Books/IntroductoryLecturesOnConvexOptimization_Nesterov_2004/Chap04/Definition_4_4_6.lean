/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProduct MinimalSingularValue

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}

/-
This item is a recall-only entry in the inner-product operator / singular-value domain.

Sampled owner-style declarations:
- `minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the chapter owner for
  the textbook least singular value;
- `minimalSingularValue_def` in `Definition_4_4_5`, the owner-level definition showing that
  `σ_min(A)` already lives in the normed-space operator setting;
- `minimalSingularValue_eq_sInf_norm_image_unitSphere` in `Definition_4_4_5`, the
  finite-dimensional normed-space bridge back to the unit-sphere textbook formula;
- `ContinuousLinearMap.adjoint`, written `A†`, the canonical Hilbert adjoint owner over `RCLike`
  scalars and complete inner product spaces;
- the positivity propositions `0 < σ_min(A)` and `0 < σ_min(A†)`, which already express the
  textbook primal and dual nondegeneracy conditions without extra packaging.

Best owner abstraction:
- source-facing: the textbook primal and dual nondegeneracy conditions for a linear operator;
- core/canonical: the propositions `0 < σ_min(A)` and `0 < σ_min(A†)`;
- bridge/view: the textbook labels "primal nondegenerate" and "dual nondegenerate" for those same
  owner propositions.

Primitive data:
- a continuous linear map `A : E₁ →L[𝕜] E₂`.

Derived API:
- the primal nondegeneracy proposition `0 < σ_min(A)`;
- the dual nondegeneracy proposition `0 < σ_min(A†)`.

The previous local predicates `PrimalNondegenerate` and `DualNondegenerate` were exact-interface
wrapper aliases around these canonical propositions. This file therefore stays recall-only and
uses the owner propositions directly instead of keeping parallel public names.
-/

section Primal

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
variable (A : E₁ →L[𝕜] E₂)

set_option linter.hashCommand false in
/- Definition 4.4.6: primal nondegeneracy is the canonical positivity proposition
`0 < σ_min(A)`. -/
#check (0 < σ_min(A))

end Primal

section Dual

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
variable (A : E₁ →L[𝕜] E₂)

/- Dual nondegeneracy is the canonical positivity proposition `0 < σ_min(A†)`. -/
set_option linter.hashCommand false in
#check (0 < σ_min(A†))

end Dual
