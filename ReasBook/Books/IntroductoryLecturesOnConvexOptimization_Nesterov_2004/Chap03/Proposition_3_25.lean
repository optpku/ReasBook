/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_16

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Gradient WithTopConvexAnalysis EuclideanOrthant

noncomputable section

/- Proposition 3.25 is a `bridge/view` theorem in the chapter's support-envelope / convex-hull
subdifferential domain.

Mandatory domain-style sampling before refinement:
- `pointwiseSupremumOn` and `activePointwiseSupremumOnIndices`, the chapter owners for a support
  envelope and its active-index set;
- `activeSupportFunctionMultipliers` and `weightedGradientCombination` in `Lemma_3_1_16`, the
  canonical source-facing active-face / gradient bridge for the support-function composition;
- `subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded`
  in `Lemma_3_16`, the chapter owner bridge from bounded weight sets to the convex-hull surface.

Best owner abstraction:
- `subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded`.

Primitive data:
- a nonempty compact convex nonnegative weight set `Λ`;
- a convex coordinate family `fs`;
- the evaluation point `x`.

Derived API:
- the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)`;
- the active-multiplier owner `activeSupportFunctionMultipliers Λ fs x`;
- the weighted-gradient map `weightedGradientCombination fs x`;
- the bounded owner bridge over `closure Λ`, specialized below using compactness.

Source/core/bridge triage:
- source-facing: Proposition 3.25's compact-set convex-hull formula for the support-function
  subdifferential;
- core/canonical: `supportFunction`, `pointwiseSupremumOn`, `weightedGradientCombination`, and
  `subdifferential`;
- bridge/view: the passage from the bounded owner bridge over `closure Λ` back to the compact
  source set `Λ`.

The previous file introduced unsupported proposition-local names `partialProtoDerivativeOfF`,
`indexSet`, and `partialProtoDerivativeOfPsi`, then proved the target equality by assuming it.
This refinement instead states Proposition 3.25 directly on the support-function composition from
`Lemma_3_16`: compactness supplies the boundedness needed by the owner bridge, and `closure Λ = Λ`
for compact `Λ` removes the closure from the public statement. The proposition keeps the
source-facing convexity data needed by the bounded owner bridge instead of relying on an
under-specified compact specialization.
-/

section

universe u

variable {m : ℕ} {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Proposition 3.25: for a nonempty compact convex nonnegative weight set, the subdifferential
of the thin `WithTop` bridge of the support-function composition `x ↦ ξ[Λ] (vectorMap fs x)` at
`x` is the convex hull of the image of the active-multiplier face under
`weightedGradientCombination fs x`. This is the representation (3.1.80) at `x`. -/
-- Proof sketch: apply the bounded owner bridge from `Lemma_3_16` using
-- `hΛ_compact.isBounded`, then simplify the resulting closure active face with
-- `hΛ_compact.isClosed.closure_eq`.
theorem subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers
    {Λ : Set (EuclideanSpace ℝ (Fin m))} {fs : Fin m → E → ℝ}
    (hΛ_nonempty : Λ.Nonempty) (hΛ_compact : IsCompact Λ)
    (hΛ_convex : Convex ℝ Λ) (hΛ_nonneg : Λ ⊆ ℝ₊^m)
    (hfs_convex : ∀ i, ConvexOn ℝ Set.univ (fs i))
    (x : E) (hfs_grad : ∀ i, HasGradientAt (fs i) (∇ (fs i) x) x) :
    ∂ (supportFunctionCompWithTop Λ fs)(x) =
      convexHull ℝ
        ((weightedGradientCombination fs x) '' activeSupportFunctionMultipliers Λ fs x) :=
  by
    have hsub :=
      subdifferential_supportFunction_comp_vectorMap_eq_convexHull_image_activeMultipliers_of_bounded
        hΛ_compact.isBounded hΛ_nonempty hΛ_nonneg hΛ_convex hfs_convex x hfs_grad
    simpa [hΛ_compact.isClosed.closure_eq] using hsub

end
