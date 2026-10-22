/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_38
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvex
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace StrongConvexOn

/- Proposition 4.1.4 lies in the whole-space strong-convexity / Polyak-inequality domain on
real Hilbert spaces.

Sampled owner-style declarations:
- project `f ∈ 𝓛^1[μ]` and `mem_strongConvexClass_iff` in `Chap02/Definition_2_14`;
- mathlib `StrongConvexOn`;
- project `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`;
- project `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`;
- mathlib `IsMinOn`.

Best owner abstraction:
- source-facing: the whole-space strong-convexity class input `f ∈ 𝓛^1[μ]`;
- core/canonical: `StrongConvexOn Set.univ μ f`;
- bridge/view: `mem_strongConvexClass_iff`, together with rewriting the squared norm as
  `Real.rpow ‖∇ f x‖ (2 : ℝ)`.

Primitive data:
- the source-facing owner witness `hf : f ∈ 𝓛^1[μ]`;
- the differentiability needed to form `∇ f`.

Derived API:
- the internal bridge `0 < μ ∧ StrongConvexOn Set.univ μ f`;
- the source-facing owner `GradientDominatedOn 2 Set.univ f`;
- the pointwise Polyak bound at any point of `argmin[Set.univ] f`;
- the degree-two `Real.rpow` pointwise bound with textbook constant `(2 * μ)⁻¹`.

This refinement removes the parallel global wrappers `strongConvexOn_...`, restores the chapter's
source-facing strong-convexity owner `𝓛^1[μ]` on the public theorem surface, and uses
`StrongConvexOn Set.univ μ f` only through the internal bridge
`mem_strongConvexClass_iff`. It still exposes gradient domination through the chapter owner
`GradientDominatedOn` rather than through a parallel unbundled witness interface.
-/

/-- Helper for Proposition 4.1.4: a differentiable whole-space `μ`-strongly convex function has
objective values bounded below on `Set.univ`. -/
lemma objective_image_bddBelow_of_mem_strongConvexClass
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) :
    BddBelow (f '' Set.univ) := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  let g0 : E := ∇ f 0
  let c : ℝ := f 0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ)
  refine ⟨c, ?_⟩
  rintro _ ⟨x, -, rfl⟩
  have hgrad0 : HasGradientAt f g0 0 := by
    -- Differentiability identifies the canonical gradient at the base point.
    simpa [g0] using (hf_diff 0).hasGradientAt
  have htangent :
      f x ≥ f 0 + inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ) := by
    -- Strong convexity gives a quadratic lower tangent model at the base point.
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        hstrong (by simp) (by simp) hgrad0
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ) :=
    SmoothMinimaxProblem.inner_add_quadratic_lower_bound μ hμ _ _
  have hraw :
      f 0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ) ≤
        f 0 + (inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ)) := by
    -- Completing the square turns the tangent inequality into a uniform lower bound.
    simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hquad (f 0)
  have hraw' :
      c ≤ f 0 + inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ) := by
    simpa [c, add_assoc, add_left_comm, add_comm] using hraw
  exact le_trans hraw' htangent

/-- Helper for Proposition 4.1.4: a differentiable whole-space `μ`-strongly convex function
attains its minimum on `Set.univ`. -/
lemma exists_mem_argmin_of_mem_strongConvexClass
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) :
    ∃ xStar, xStar ∈ argmin[Set.univ] f := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  rcases
      SmoothMinimaxProblem.exists_isMinOn_of_isClosed_of_complete_of_bddBelow
        (Q := Set.univ) (f := f) (μ := μ)
        isClosed_univ ⟨0, by simp⟩
        hf_diff.continuous.continuousOn hstrong hμ
        (objective_image_bddBelow_of_mem_strongConvexClass hf hf_diff)
    with ⟨xStar, -, hxStar_min⟩
  -- Repackage the attained minimum as canonical `argmin` membership.
  exact ⟨xStar, mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar_min⟩⟩

/-- Helper for Proposition 4.1.4: the textbook trial point
`x - (1 / μ) • ∇ f x` satisfies the one-step lower bound obtained from strong convexity. -/
lemma gradient_step_lower_bound
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) (x : E) :
    f (x - (1 / μ) • ∇ f x) ≥ f x - (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  let g : E := ∇ f x
  let trialPoint : E := x - (1 / μ) • g
  have hgrad : HasGradientAt f g x := by
    -- Differentiability identifies the gradient used by the tangent inequality.
    simpa [g] using (hf_diff x).hasGradientAt
  have htangent :
      f trialPoint ≥ f x + inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ) := by
    -- Apply strong convexity at the pair `(x, x - μ⁻¹ ∇ f x)`.
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        (Q := Set.univ) (x := x) (y := trialPoint) (g := g)
        hstrong (by simp) (by simp [trialPoint]) hgrad
  have hquad :
      -(‖g‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ) :=
    SmoothMinimaxProblem.inner_add_quadratic_lower_bound μ hμ g (trialPoint - x)
  have hraw :
      f x - ‖g‖ ^ (2 : ℕ) / (2 * μ) ≤
        f x + (inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ)) := by
    -- Completing the square gives the desired lower bound for the trial-point model value.
    simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hquad (f x)
  have hlower : f x - ‖g‖ ^ (2 : ℕ) / (2 * μ) ≤ f trialPoint := by
    have htangent' :
        f x + (inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ)) ≤
          f trialPoint := by
      simpa [add_assoc, add_left_comm, add_comm] using htangent
    exact le_trans hraw htangent'
  have hgoal_div : f trialPoint ≥ f x - ‖g‖ ^ (2 : ℕ) / (2 * μ) := hlower
  simpa [trialPoint, g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgoal_div

/-- Proposition 4.1.4: a positive strongly convex objective on a real Hilbert space is gradient
dominated of degree `2`. -/
-- Proof sketch: choose any global minimizer `xStar`, apply strong convexity at the pair `x` and
-- `x - (1 / μ) • ∇ f x`, using `mem_strongConvexClass_iff` to extract the internal
-- `StrongConvexOn Set.univ μ f` bridge and positivity of `μ`, and rewrite the resulting Polyak
-- inequality as the degree-two gradient-domination bound with constant `(2 * μ)⁻¹`.
theorem gradientDominatedOn_two
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) :
    GradientDominatedOn 2 Set.univ f := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, -⟩
  rcases exists_mem_argmin_of_mem_strongConvexClass hf hf_diff with ⟨xStar, hxStar⟩
  refine ⟨hf_diff.differentiableOn, by norm_num, ?_⟩
  refine ⟨xStar, 1 / (2 * μ), ?_⟩
  refine ⟨uniqueDiffOn_univ, hxStar, ?_, ?_⟩
  · -- The Polyak constant is positive because `μ` is positive.
    positivity
  · intro x hx
    rcases mem_constrainedArgmin_iff.mp hxStar with ⟨-, hxStar_min⟩
    have hgrad : HasGradientAt f (∇ f x) x := by
      -- Differentiability identifies the canonical gradient at `x`.
      simpa using (hf_diff x).hasGradientAt
    have htangent :
        f xStar ≥ f x + inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) := by
      -- Evaluate strong convexity directly at the minimizer `xStar`.
      simpa using
        StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
          (mem_strongConvexClass_iff.mp hf).2 (by simp) (by simp) hgrad
    have hquad :
        -(‖∇ f x‖ ^ (2 : ℕ)) / (2 * μ) ≤
          inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) :=
      SmoothMinimaxProblem.inner_add_quadratic_lower_bound
        μ hμ (∇ f x) (xStar - x)
    have hraw :
        f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤
          f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) := by
      -- Completing the square on the tangent model produces the Polyak bound.
      simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        add_le_add_left hquad (f x)
    have htangent' :
        f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) ≤ f xStar := by
      simpa [add_assoc, add_left_comm, add_comm] using htangent
    have hbound_sq :
        f x - f xStar ≤ (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
      have hlower : f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤ f xStar := le_trans hraw htangent'
      have hbound_div :
          f x - f xStar ≤ ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) := by
        linarith
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound_div
    -- On `Set.univ`, the within-gradient agrees with the ambient gradient.
    simpa [gradientWithin, gradient, fderivWithin_univ, Real.rpow_natCast] using hbound_sq

/-- Companion `Real.rpow` form of Proposition 4.1.4's Polyak inequality. -/
-- Proof sketch: obtain the owner witness `GradientDominatedOn 2 Set.univ f` from
-- `gradientDominatedOn_two`, transport it to the chosen minimizer with
-- `GradientDominatedOn.exists_usesConstant_of_mem_argmin`, and then apply the resulting
-- pointwise bound with textbook constant `(2 * μ)⁻¹`.
theorem sub_le_inv_two_mul_rpow_norm_gradient_two_of_isMinOn
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f)
    {xStar x : E} (hxStar : xStar ∈ argmin[Set.univ] f) :
    f x - f xStar ≤ (1 / (2 * μ)) * Real.rpow ‖∇ f x‖ (2 : ℝ) := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  let _ := hxStar
  have hgrad : HasGradientAt f (∇ f x) x := by
    -- Differentiability identifies the canonical gradient at `x`.
    simpa using (hf_diff x).hasGradientAt
  have htangent :
      f xStar ≥ f x + inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) := by
    -- Evaluate strong convexity at the minimizer `xStar`.
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        hstrong (by simp) (by simp) hgrad
  have hquad :
      -(‖∇ f x‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) :=
    SmoothMinimaxProblem.inner_add_quadratic_lower_bound
      μ hμ (∇ f x) (xStar - x)
  have hraw :
      f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤
        f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) := by
    -- Completing the square on the lower tangent model isolates the gradient norm term.
    simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hquad (f x)
  have htangent' :
      f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) ≤ f xStar := by
    simpa [add_assoc, add_left_comm, add_comm] using htangent
  have hbound_sq :
      f x - f xStar ≤ (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
    have hlower : f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤ f xStar := le_trans hraw htangent'
    have hbound_div :
        f x - f xStar ≤ ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) := by
      linarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound_div
  -- Rewrite the square as a degree-two real power.
  simpa [Real.rpow_natCast] using hbound_sq

/-- Companion squared-norm form of Proposition 4.1.4's Polyak inequality. -/
-- Proof sketch: apply `sub_le_inv_two_mul_rpow_norm_gradient_two_of_isMinOn` and rewrite
-- `Real.rpow ‖∇ f x‖ (2 : ℝ)` as `‖∇ f x‖ ^ (2 : ℕ)`.
theorem sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f)
    {xStar x : E} (hxStar : xStar ∈ argmin[Set.univ] f) :
    f x - f xStar ≤ (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  -- This is the same estimate with the exponent written as a square.
  simpa [Real.rpow_natCast] using
    sub_le_inv_two_mul_rpow_norm_gradient_two_of_isMinOn hf hf_diff hxStar

end StrongConvexOn
