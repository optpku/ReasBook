/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped InnerProduct LevelSetNotation Manifold MinimalSingularValue

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

/- Assumption 4.4.3 lies in the modified Gauss--Newton / sublevel-set nondegeneracy domain.

Sampled owner-style declarations:
* the bundled smooth-map owner `C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯` from `Definition_4_4_8`
* `meritFunctionReformulation problem φ` in `Definition_4_4_10`, the chapter owner for the
  scalarized modified Gauss--Newton objective
* `𝓛[f](a)` together with `mem_levelSet_iff` in `Definition_4_1_1`, the chapter owner for
  initial sublevel sets
* `minimalSingularValue` with notation `σ_min(A)` in `Definition_4_4_5`, the chapter owner for
  least singular values

Best owner abstraction:
* source-facing: `HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x₀ σ`
* core/canonical: a bundled smooth residual map `problem : SmoothMap`, positivity of `σ`, and a
  lower bound for `σ_min((fderiv ℝ problem x)†)` on the canonical initial merit sublevel set
  `𝓛[meritFunctionReformulation problem φ]((meritFunctionReformulation problem φ x₀))`
* bridge/view: `meritFunctionReformulation_apply` and `mem_levelSet_iff` for the textbook
  inequality `φ (problem x) ≤ φ (problem x₀)`

Primitive data:
* the smooth residual map `problem`
* the merit function `φ`
* the base point `x₀`
* the constant `σ`

Derived API:
* positivity of `σ` and the pointwise lower bound, obtained directly by conjunction projections
  from the source-facing owner predicate

There is no upstream owner for the full uniform-on-sublevel conjunction, so the source-facing
predicate stays. The duplicate wheels were the unbundled residual-map parameter and the inline
merit/sublevel encoding. This file now reuses the chapter owner `SmoothMap` for the nonlinear
system and the owner `meritFunctionReformulation problem φ` for the scalarized objective, while
keeping the Euclidean textbook case as a specialization of this inner-product-space statement.
-/

/-- Assumption 4.4.3: for a smooth nonlinear equation problem `problem`, the Jacobian operators
`problem'(x)` have a uniform dual nondegeneracy on the initial merit sublevel set
`𝓛[meritFunctionReformulation problem φ]((meritFunctionReformulation problem φ x₀))`, meaning
that a single constant `σ > 0` satisfies `σ ≤ σ_min(problem'(x)*)` for every `x` in that set. -/
def HasUniformDualNondegeneracyOnInitialSublevelSet
    (problem : SmoothMap) (φ : F → ℝ) (x0 : E) (σ : ℝ) : Prop :=
  let f := meritFunctionReformulation problem φ
  0 < σ ∧
    ∀ ⦃x : E⦄, x ∈ (𝓛[f]((f x0)) : Set E) → σ ≤ σ_min((fderiv ℝ problem x)†)

namespace HasUniformDualNondegeneracyOnInitialSublevelSet

variable {problem : SmoothMap} {φ : F → ℝ} {x0 x : E} {σ : ℝ}

local notation "f" => meritFunctionReformulation problem φ

/-- Uniform dual nondegeneracy on the initial sublevel set forces the constant `σ` to be
strictly positive. -/
theorem sigma_pos
    (_hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ) :
    0 < σ :=
  _hσ.1

/-- Uniform dual nondegeneracy on the initial sublevel set yields the pointwise lower bound
`σ ≤ σ_min(problem'(x)*)` at every point of the initial merit sublevel set. -/
theorem lower_bound
    (_hσ :
      HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (_hx : x ∈ (𝓛[f]((f x0)) : Set E)) :
    σ ≤ σ_min((fderiv ℝ problem x)†) :=
  _hσ.2 _hx

end HasUniformDualNondegeneracyOnInitialSublevelSet
