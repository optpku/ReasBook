/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E₁ : Type v} {E₂ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

section

set_option linter.hashCommand false

/- Proposition 6.3 lies in the dual-valued operator-norm / transpose domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.flip`
- `ContinuousLinearMap.flip_apply`
- `ContinuousLinearMap.opNorm_flip`
- `ContinuousLinearMap.le_opNorm`

Best owner abstraction:
- source-facing: the adjoint/transposed operator `A* : E₂ → E₁*` of a dual-valued operator
  `A : E₁ → E₂*`;
- core/canonical: `A.flip`;
- bridge/view: rewriting the norm bound for `A.flip`
  with the canonical identity `‖A.flip‖ = ‖A‖`.

This item therefore keeps the norm identity as a direct recall of the canonical owner theorem and
adds only the source-facing estimate whose constant is rewritten from `‖A.flip‖` to `‖A‖`. -/

/- Proposition 6.3: the canonical transpose `A.flip` of a dual-valued continuous linear map has
the same operator norm as `A`. -/
#check (ContinuousLinearMap.opNorm_flip :
  ∀ A : E₁ →L[𝕜] StrongDual 𝕜 E₂, ‖A.flip‖ = ‖A‖)

/- Evaluating the canonical transpose gives the defining dual-pairing identity
`(A.flip u) x = (A x) u`. -/
#check (ContinuousLinearMap.flip_apply :
  ∀ (A : E₁ →L[𝕜] StrongDual 𝕜 E₂) (x : E₁) (u : E₂), (A.flip u) x = (A x) u)

/- The first operator-norm estimate in Proposition 6.3 is the canonical bound
`ContinuousLinearMap.le_opNorm` applied to `A`. -/
#check (ContinuousLinearMap.le_opNorm :
  ∀ (A : E₁ →L[𝕜] StrongDual 𝕜 E₂) (x : E₁), ‖A x‖ ≤ ‖A‖ * ‖x‖)

-- Proof sketch: apply `ContinuousLinearMap.le_opNorm` to `A.flip`, then rewrite the operator norm
-- with `ContinuousLinearMap.opNorm_flip`.
/-- Applying the operator-norm estimate to the canonical transpose `A.flip` gives the adjoint
bound with the same constant `‖A‖`. -/
theorem norm_flip_apply_le_opNorm
    (A : E₁ →L[𝕜] StrongDual 𝕜 E₂) (u : E₂) :
    ‖A.flip u‖ ≤ ‖A‖ * ‖u‖ := by
  simpa using A.flip.le_opNorm u

end
