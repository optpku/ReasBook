/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceDefinition5422 : MeasurableSpace E := borel E
local instance instBorelSpaceDefinition5422 : BorelSpace E := ⟨rfl⟩

/- Definition 5.4.2.2 lies in the chapter's based-polar-set / intrinsic volume domain.

Sampled owner-style declarations:
- project `polarSet`
- project `polarSetAt`
- mathlib `MeasureTheory.volume`
- project `volumetricBarrier`

Best owner abstraction:
- the source-facing Chapter 5 owner `universalBarrierVolume`

Primitive data:
- a set `Q : Set E`
- an interior point `x : interior Q`

Derived API:
- the based polar body `polarSetAt Q (x : E)`
- its volume `(volume (polarSetAt Q (x : E))).toReal`

Source/core/bridge triage:
- source-facing: `universalBarrierVolume`
- core/canonical: `polarSetAt` and `MeasureTheory.volume`

Unlike `polarSetAt`, this definition is genuinely new source-facing content: it combines the
chapter's based polar owner with the ambient finite-dimensional real volume owner. There is
therefore no upstream owner to recall directly, so the refined file keeps only this owner and
reuses those canonical ingredients verbatim. Specializing to `E = EuclideanSpace ℝ (Fin n)`
recovers the textbook `ℝⁿ` formulation.
-/

/-- Definition 5.4.2.2, stated at the intrinsic owner level: for an interior point `x` of a set
`Q` in a finite-dimensional real inner-product space, `universalBarrierVolume Q x` is the volume
of the associated based polar body `P(x) = {s | ∀ y ∈ Q, ⟪s, y - x⟫ ≤ 1}`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook Lebesgue-volume definition on `ℝⁿ`. In the
textbook application, `Q` is later assumed proper and convex. -/
def universalBarrierVolume (Q : Set E) (x : interior Q) : ℝ :=
  (volume (polarSetAt Q x)).toReal

end
