/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/- Owner analysis for this item in the chapter's smooth nonlinear-equation domain.

Sampled owner-style declarations:
* `ContMDiffMap` in `Mathlib/Geometry/Manifold/ContMDiffMap`, the canonical bundled smooth-map
  owner;
* the bundled-map notation `C^n⟮I, M; I', M'⟯` for `ContMDiffMap`;
* `ContMDiffMap.contMDiff`, the owner projection to manifold smoothness;
* `contMDiff_iff_contDiff`, the normed-space bridge back to `ContDiff`;
* `SmoothMinimaxProblem` in `Chap02/Definition_2_38`, illustrating that the chapter introduces a
  structure owner only when the source adds genuine extra data beyond an existing canonical owner;
* `SmoothFunctionalConstraintsMinimizationProblem` in `Chap02/Definition_2_44`, which similarly
  keeps only source-specific data and reuses upstream owners for the primitive functional content.

Best owner abstraction:
* the canonical bundled object here is the smooth-map type
  `C^⊤⟮𝓘(𝕜, E₁), E₁; 𝓘(𝕜, E₂), E₂⟯`.

Primitive data:
* the bundled smooth map itself.

Derived API:
* the exact solution set `solutionSet`;
* the membership rewrite `mem_solutionSet_iff`.

Source/core/bridge triage:
* source-facing: the textbook smooth system `F(x) = 0`;
* core/canonical: `C^⊤⟮𝓘(𝕜, E₁), E₁; 𝓘(𝕜, E₂), E₂⟯`;
* bridge/view: `contMDiff_iff_contDiff` and `solutionSet`.

This item therefore recalls the canonical bundled smooth-map expression directly instead of
introducing a parallel public alias. -/

section

open scoped Manifold

variable (𝕜 : Type w) [NontriviallyNormedField 𝕜]
variable (E₁ : Type u) (E₂ : Type v)
variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
variable [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/- Definition 4.4.8: the smooth nonlinear system under consideration is given by a smooth map
`F : E₁ → E₂`, whose canonical bundled owner in mathlib is `ContMDiffMap`; in the Euclidean-model
notation used here, the specialized smooth-map type is `C^⊤⟮𝓘(𝕜, E₁), E₁; 𝓘(𝕜, E₂), E₂⟯`. -/
set_option linter.hashCommand false in
#check C^⊤⟮𝓘(𝕜, E₁), E₁; 𝓘(𝕜, E₂), E₂⟯

end

namespace SmoothNonlinearEquationProblem

variable {E₁ : Type u} {E₂ : Type v}
variable [Zero E₂]

/-- The exact solution set of the nonlinear system attached to `problem`. -/
def solutionSet (problem : E₁ → E₂) : Set E₁ :=
  problem ⁻¹' ({0} : Set E₂)

@[simp]
theorem mem_solutionSet_iff
    (problem : E₁ → E₂) (x : E₁) :
    x ∈ solutionSet problem ↔ problem x = 0 :=
  Iff.rfl

end SmoothNonlinearEquationProblem
