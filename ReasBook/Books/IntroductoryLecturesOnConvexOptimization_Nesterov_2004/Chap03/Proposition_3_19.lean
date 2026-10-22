/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.19 lies in the chapter's real-valued subdifferential / positive-homogeneity
domain.

Primary domain:
- subdifferentials of positively homogeneous convex functions on finite-dimensional real
  inner-product spaces, together with the ambient touching identity that is valid on arbitrary real
  inner-product spaces once a subgradient is given.

Sampled owner-style declarations:
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` in `Definition_3_1_5`, the
  chapter owners for unconstrained subgradients of `WithTop ℝ`-valued functions;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity;
- `subdifferential_eq_subdifferential_zero_of_posHomogeneous` in `Lemma_3_15`, the existing
  one-homogeneous source-facing bridge identifying `∂f(x)` with the touching slice of `∂f(0)`;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` in
  `Theorem_3_21`, the nearby canonical max-formula owner for convex subgradients.

Best owner abstraction:
- primitive owner predicate `IsSubgradientAt` on `fun y ↦ (f y : WithTop ℝ)`;
- derived owner set `∂ (fun y ↦ (f y : WithTop ℝ))(x)`;
- positive-homogeneity owner `IsPositivelyHomogeneousOn 1 Set.univ f`.

Primitive data:
- a real inner-product space `E`;
- a real-valued function `f : E → ℝ`;
- convexity of `f` on `Set.univ`;
- positive homogeneity of `f` on `Set.univ`.
- for the main `IsGreatest` proposition, finite-dimensionality of `E`, which is the source-faithful
  setting in which the chapter's vector-valued subgradient owner matches the Riesz-representable
  supporting functionals.

Derived API:
- Proposition 3.19's `IsGreatest` max formula over the origin subdifferential.

Source/core/bridge triage:
- source-facing: Proposition 3.19's max formula for convex positively homogeneous functions;
- core/canonical: `IsSubgradientAt`, `subdifferential`, and `IsPositivelyHomogeneousOn`;
- bridge/view: the coercion `fun y ↦ (f y : WithTop ℝ)` and the earlier bridge
  `subdifferential_eq_subdifferential_zero_of_posHomogeneous`.

The previous version duplicated a real-valued subgradient predicate, a real-valued subdifferential
set, and the exact membership theorem that the chapter already owns in `Definition_3_1_5`. This
refinement deletes that parallel API and reuses the existing one-homogeneous bridge from
`Lemma_3_15` together with the interior-point nonemptiness owner from `Theorem_3_1_15`. The main
source-facing Proposition 3.19 theorem stays in the finite-dimensional setting needed for
vector-valued subgradients to capture all continuous supporting functionals.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition 3.19: for a convex positively `1`-homogeneous function on a finite-dimensional real
inner-product space, the value at `x` is the maximum of the pairings `⟪g, x⟫` over all
subgradients `g ∈ ∂f(0)`, expressed as an `IsGreatest` statement for the image of the origin
subdifferential. -/
-- Proof sketch: every `g ∈ ∂f(0)` satisfies `⟪g, x⟫ ≤ f x` by the subgradient inequality at the
-- origin. For the reverse bound, use convexity together with the canonical interior-point
-- nonemptiness theorem to obtain some `g ∈ ∂f(x)`, then apply
-- `subdifferential_eq_subdifferential_zero_of_posHomogeneous` to identify the same `g` with an
-- element of `∂f(0)` satisfying `⟪g, x⟫ = f x`.
theorem isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    [FiniteDimensional ℝ E] (x : E) :
    IsGreatest ((fun g : E ↦ inner ℝ g x) '' ∂ (fun y ↦ (f y : WithTop ℝ))(0)) (f x) := by
  let fTop : E → WithTop ℝ := fun y ↦ (f y : WithTop ℝ)
  have hf_top : ConvexOn ℝ (dom fTop) (withTopRealPart fTop) := by
    change ConvexOn ℝ (dom (fun y ↦ (f y : WithTop ℝ)))
      (withTopRealPart (fun y ↦ (f y : WithTop ℝ)))
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_convex
  have hx_mem : x ∈ interior (dom fTop) := by
    change x ∈ interior (dom (fun y ↦ (f y : WithTop ℝ)))
    simp [withTopEffectiveDomain]
  obtain ⟨g, hgx⟩ :=
    (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hf_top hx_mem).1
  refine ⟨?_, ?_⟩
  · rw [subdifferential_eq_subdifferential_zero_of_posHomogeneous hf_hom x] at hgx
    exact ⟨g, hgx.1, hgx.2⟩
  · intro y hy
    rcases hy with ⟨g, hg0, rfl⟩
    have hg0' : IsSubgradientAt fTop 0 g := mem_subdifferential_iff.mp hg0
    have hx : x ∈ dom fTop := by
      change x ∈ dom (fun y ↦ (f y : WithTop ℝ))
      simp [withTopEffectiveDomain]
    have hineq : (f x : WithTop ℝ) ≥ f 0 + (inner ℝ g (x - 0) : WithTop ℝ) := hg0'.2 hx
    have h0 : f 0 = 0 := by
      simpa using hf_hom.map_smul (show (0 : E) ∈ Set.univ by simp) (0 : NNReal)
    have hreal : f x ≥ f 0 + inner ℝ g (x - 0) := by
      exact_mod_cast hineq
    simpa [fTop, h0] using hreal

end
