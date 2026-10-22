/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local instance instLocalChap03_Lemma_3_311 : MeasurableSpace E := borel E
local instance instLocalChap03_Lemma_3_312 : BorelSpace E := ⟨rfl⟩

/- Primary domain: measure-theoretic convex geometry of centroid halfspace cuts in a finite-
dimensional real inner-product space.

Sampled owner-style declarations:
- `cuttingHalfspace` in `Definition_3_49`, the chapter owner for affine retained cuts;
- `setAverage` in `Definition_3_54`, the canonical centroid owner recalled there;
- `centerOfGravityCut_volumeRatio_le_one_sub_inv_e` in `Lemma_3_2_6`, the chapter owner theorem
  for the centroid-cut volume estimate under the canonical finite/positive-volume hypotheses;
- `Bornology.IsBounded.measure_lt_top` and `measure_pos_of_nonempty_interior`, the mathlib bridges
  from boundedness and nonempty interior to those owner hypotheses.

Best owner abstraction:
- source-facing: this lemma's textbook hypothesis package of boundedness, convexity, and nonempty
  interior;
- core/canonical: the centroid cut `S ∩ cuttingHalfspace (⨍ x in S, x) g` together with the
  intrinsic owner theorem `centerOfGravityCut_volumeRatio_le_one_sub_inv_e`;
- bridge/view: the derived hypotheses `volume S ≠ ⊤` and `volume S ≠ 0`.

Primitive data:
- the set `S` and the direction `g`;
- boundedness, convexity, nonempty interior, and `g ≠ 0`.

Derived API:
- finite volume from boundedness;
- positive volume from nonempty interior;
- the final ratio estimate by direct reuse of the owner theorem.

This file stays source-facing: the textbook packages the geometric assumptions more concretely than
the owner theorem does, so the refinement is a thin bridge rather than a parallel owner API.
The earlier `EuclideanSpace ℝ (Fin n)` surface was only a display model, so the owner bridge now
lives at the same intrinsic finite-dimensional layer as the chapter's localization-radius API. -/

/-- Lemma 3.31 at the intrinsic owner level: if `S ⊆ E` is bounded and convex with nonempty
interior in a finite-dimensional real inner-product space, then for any nonzero `g : E` the
centroid cut
`S₊ = S ∩ cuttingHalfspace (⨍ x in S, x) g = {x ∈ S | ⟪g, (⨍ x in S, x) - x⟫_ℝ ≥ 0}`
has relative volume at most `1 - 1 / e`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: this is Grünbaum's centroid halfspace inequality. Use boundedness and nonempty
-- interior to obtain finite positive volume for `S`, then apply the owner centroid halfspace
-- estimate to `S` with those derived measure hypotheses.
theorem centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior
    (S : Set E) (g : E) (hS_bounded : Bornology.IsBounded S) (hS_convex : Convex ℝ S)
    (hS_int : (interior S).Nonempty) (hg : g ≠ 0) :
    (volume (S ∩ cuttingHalfspace (⨍ x in S, x) g)).toReal / (volume S).toReal ≤
      1 - 1 / Real.exp 1 := by
  have hS_finite : volume S ≠ ⊤ := hS_bounded.measure_lt_top.ne
  have hS_pos : volume S ≠ 0 := (Measure.measure_pos_of_nonempty_interior volume hS_int).ne'
  simpa using centerOfGravityCut_volumeRatio_le_one_sub_inv_e S g hS_convex hS_finite hS_pos hg

end
