/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E : Type u} {F : Type v} [SMul NNReal E] [SMul ℝ F]

/-
Definition 3.1.7 is source-facing in the chapter's positive-homogeneity API.

Primary domain:
- positively homogeneous functions on a cone.

Relevant owner-style declarations sampled before refinement:
- `SubMulAction NNReal E`
- `SMulMemClass.smul_mem`
- `Real.rpow`
- `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)` in `Theorem_3_1_21`

Best owner abstraction for the cone data:
- `SubMulAction NNReal E`

Primitive data:
- a cone-shaped domain `s : Set E`
- a real degree `p`
- a map `f : E → F`

Derived API:
- the closure field `IsPositivelyHomogeneousOn.smul_mem`
- the scaling law `IsPositivelyHomogeneousOn.map_smul`

Source/core/bridge triage:
- source-facing: `IsPositivelyHomogeneousOn p s f`
- core/canonical: `SubMulAction NNReal E`
- bridge/view: the specialization `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)` in
  `Theorem_3_1_21`
-/
/-- Definition 3.1.7: a function on a cone is positively homogeneous of degree `p` when its
domain is closed under nonnegative scalar multiplication and scaling the input by a bundled
nonnegative scalar `τ : NNReal` scales the value by `τ ^ p`. -/
class IsPositivelyHomogeneousOn (p : ℝ) (s : Set E) (f : E → F) : Prop where
  /-- A positively homogeneous function has a domain closed under nonnegative scalar
  multiplication. -/
  smul_mem {x : E} (hx : x ∈ s) (τ : NNReal) : τ • x ∈ s
  /-- A positively homogeneous function satisfies the prescribed nonnegative scaling identity on
  its domain. -/
  map_smul {x : E} (hx : x ∈ s) (τ : NNReal) :
    f (τ • x) = Real.rpow (τ : ℝ) p • f x

end
