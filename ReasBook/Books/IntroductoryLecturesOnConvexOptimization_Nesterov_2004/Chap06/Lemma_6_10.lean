/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_25
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/- Lemma 6.10 lies in Chapter 6's zero-smoothing dual-objective / Danskin-gradient domain.

Relevant owner-style declarations sampled before repair:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  canonical Chapter 6 owners for the zero-smoothing primal slice and dual value;
- `argmin[Q₁]` in `Chap01/Definition_1_3_3`, the canonical feasible minimizer owner used
  throughout the project;
- `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical bridge from the
  `EReal`-valued dual owner to its finite real part;
- `hatf ∈ 𝒮^0_σ(Q₁)` in `Chap03/Definition_3_47`, the source-facing strong-convexity owner.

Source/core/bridge triage:
- source-facing: the bundled concavity-and-gradient statement of Lemma 6.10;
- core/canonical: `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with the pointwise argmin
  owner `x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`;
- bridge/view: the explicit Hilbert-space gradient formula below.

The previous file depended on a broken recall chain through `Definition_6_33`. The repaired file
states Lemma 6.10 directly on the actual available chapter owners, without introducing a parallel
wrapper API.
-/

section

variable [CompleteSpace E₂]

-- Proof sketch: use the strong-convexity owner
-- `0 < σ ∧ StrongConvexOn Q₁ σ hatf` to obtain uniqueness of the
-- pointwise argmin in each zero-smoothing primal slice. Then apply the Chapter 6 Danskin-style
-- gradient statement for `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with convexity of
-- `hatφ` to conclude concavity of the finite real part and the displayed gradient formula.
/-- Lemma 6.10: if `0 < σ` and `hatf` is `σ`-strongly convex on `Q₁`, if `x₀ u` is a feasible
minimizer of the zero-smoothing primal slice for every `u`, and if `\hat φ` is differentiable and
convex, then the finite real part of the canonical zero-smoothing dual objective is concave and
has gradient `-\nabla \hat φ(u) + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))`. -/
theorem dualObjective_concave_and_hasGradientAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hσ : 0 < σ)
    (hhatf : StrongConvexOn Q₁ σ hatf)
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ)
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)) :
    ConcaveOn ℝ Set.univ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) ∧
      ∀ u : E₂,
        HasGradientAt
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
          (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := by
  -- Convert the source-facing strong-convexity assumptions into the owner expected by Lemma 6.2.5.
  have hhatf_mem := StrongConvexOn.mem_S0On hσ hhatf
  constructor
  · -- Rewrite the canonical domain result to obtain concavity on all of `E₂`.
    simpa [dualObjective_dom_eq_univ (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ)] using
      dualObjective_concave (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) hhatφ_convex
  · intro u
    -- Reuse the imported zero-smoothing gradient formula at the chosen argmin witness `x₀ u`.
    simpa using
      dualObjective_hasGradientAt
        (A := A) (Q₁ := Q₁) (hatf := hatf) (hatφ := hatφ) (x₀ := x₀) (σ := σ)
        hhatf_mem hhatφ_diff hx₀ u

end

end
