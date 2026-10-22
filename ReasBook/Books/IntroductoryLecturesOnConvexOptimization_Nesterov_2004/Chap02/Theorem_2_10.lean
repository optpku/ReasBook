/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

section Normed

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {μ : ℝ} {Q : Set X} {f : X → ℝ}

/- Primary domain: strong convexity on convex sets, with the owner predicate
`StrongConvexOn Q μ f` and its first-order consequences.

Sampled owner-style declarations before refining this file:
* mathlib `UniformConvexOn`
* mathlib `StrongConvexOn`
* mathlib `strongConvexOn_iff_convex`
* `convexOn_iff_gradient_monotone` in `Theorem_2_3`, whose forward direction gives the ordinary
  monotone-gradient inequality for convex functions on a convex set

Best owner abstraction:
* mathlib's `StrongConvexOn Q μ f`

Primitive data:
* the feasible set `Q`
* the modulus `μ`
* the objective `f`
* for first-order consequences, the owner smoothness datum `DifferentiableOn ℝ f Q`

Derived API:
* the source-facing quadratic Jensen bridge below
* the strong gradient-monotonicity bridge on the Hilbert-space layer
* the three-way TFAE theorem obtained by combining those two bridges

Source/core/bridge triage:
* source-facing: the quadratic Jensen inequality and the strong gradient-monotonicity inequality
  attached to Theorem 2.10
* core/canonical: `StrongConvexOn Q μ f`
* bridge/view: the quadratic Jensen reformulation of `StrongConvexOn`, and the Hilbert-space
  reduction through `strongConvexOn_iff_convex` plus `convexOn_iff_gradient_monotone`

The owner abstraction is `StrongConvexOn Q μ f`. The quadratic Jensen statement below is kept
only as the thin source-facing bridge from that owner, rather than as a parallel strong-convexity
definition. -/

/-- On a convex set `Q` in a real normed space, mathlib's owner predicate `StrongConvexOn Q μ f`
is exactly the displayed quadratic Jensen inequality. -/
theorem strongConvexOn_iff_quadratic_jensen_bound
    (hQ : Convex ℝ Q) :
    StrongConvexOn Q μ f ↔
      ∀ ⦃x y : X⦄ (_ : x ∈ Q) (_ : y ∈ Q) ⦃α : ℝ⦄ (_ : α ∈ Set.Icc (0 : ℝ) 1),
        f (α • x + (1 - α) • y) + α * (1 - α) * (μ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
          α * f x + (1 - α) * f y := by
  constructor
  · intro hf x y hx hy α hα
    have hα' : 0 ≤ α := hα.1
    have hβ : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
    have hab : α + (1 - α) = 1 := by ring
    simpa [le_sub_iff_add_le, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hf.2 hx hy hα' hβ hab
  · intro h
    refine ⟨hQ, ?_⟩
    intro x hx y hy a b ha hb hab
    have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨ha, ?_⟩
      linarith
    have hb_eq : b = 1 - a := by
      linarith
    simpa [hb_eq, le_sub_iff_add_le, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      h hx hy haIcc

end Normed

section InnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {μ : ℝ} {Q : Set E} {f : E → ℝ}

local notation "gradQ" => gradientWithin f Q

/- On the Hilbert-space owner layer, strong convexity is the convexity of
`x ↦ f x - (μ / 2) * ‖x‖²`, while the canonical first-order view is monotonicity of
`gradientWithin`. The source theorem is therefore a bridge/view theorem from the owner
`StrongConvexOn Q μ f`, and the main smoothness input is only `DifferentiableOn ℝ f Q`. -/

/-- Helper for Theorem 2.10: the quadratic shift `x ↦ (μ / 2) * ‖x‖²` has gradient `μ • x`. -/
private theorem shifted_quadratic_hasFDerivAt (x : E) :
    HasFDerivAt (fun u : E ↦ μ / 2 * ‖u‖ ^ (2 : ℕ))
      (InnerProductSpace.toDual ℝ E (μ • x)) x := by
  -- Compute the Fréchet derivative of the squared norm and scale it by `μ / 2`.
  have hsmul :
      HasFDerivAt (fun u : E ↦ μ / 2 * ‖u‖ ^ (2 : ℕ))
        (((μ / 2) • (2 • innerSL ℝ x)) : E →L[ℝ] ℝ) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (μ / 2)
  have hlin :
      (((μ / 2) • (2 • innerSL ℝ x)) : E →L[ℝ] ℝ) =
        InnerProductSpace.toDual ℝ E (μ • x) := by
    ext u
    simp [InnerProductSpace.toDual_apply_apply, two_smul]
    ring
  exact hlin ▸ hsmul

/-- Helper for Theorem 2.10: the shifted function `x ↦ f x - (μ / 2) * ‖x‖²` stays
within-set differentiable on `Q`. -/
private theorem shifted_function_differentiableOn
    (hf_diff : DifferentiableOn ℝ f Q) :
    DifferentiableOn ℝ (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) Q := by
  intro x hx
  -- Subtract the explicit quadratic term from the given differentiable function.
  refine (hf_diff x hx).sub ?_
  exact (shifted_quadratic_hasFDerivAt (μ := μ) x).differentiableAt.differentiableWithinAt

/-- Helper for Theorem 2.10: along any feasible chord, the shifted within-gradient pairing is the
original pairing minus the quadratic correction. -/
private theorem inner_gradientWithin_shifted_sub
    (hQ : Convex ℝ Q) (hf_diff : DifferentiableOn ℝ f Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    inner ℝ (gradientWithin (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) Q x) (y - x)
      = inner ℝ (gradQ x) (y - x) - μ * inner ℝ x (y - x) := by
  let seg : ℝ → E := AffineMap.lineMap x y
  let shifted : E → ℝ := fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)
  have hseg_maps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := hQ.mapsTo_lineMap hx hy
  have hshifted_fderiv :
      HasFDerivWithinAt shifted
        (InnerProductSpace.toDual ℝ E (gradientWithin shifted Q x)) Q x :=
    ((shifted_function_differentiableOn (μ := μ) hf_diff x hx).hasGradientWithinAt).hasFDerivWithinAt
  have hseg_grad_shifted :
      HasDerivWithinAt (fun t : ℝ ↦ shifted (seg t))
        (inner ℝ (gradientWithin shifted Q x) (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    -- Differentiate the shifted function along the segment from `x` to `y` at `t = 0`.
    simpa [seg, shifted] using
      hshifted_fderiv.comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hseg_maps
        (AffineMap.lineMap_apply_zero x y).symm
  have hf_fderiv :
      HasFDerivWithinAt f (InnerProductSpace.toDual ℝ E (gradQ x)) Q x :=
    ((hf_diff x hx).hasGradientWithinAt).hasFDerivWithinAt
  have hseg_grad_f :
      HasDerivWithinAt (fun t : ℝ ↦ f (seg t))
        (inner ℝ (gradQ x) (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    -- The same segment derivative for `f` is the gradient pairing with `y - x`.
    simpa [seg] using
      hf_fderiv.comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hseg_maps
        (AffineMap.lineMap_apply_zero x y).symm
  have hseg_grad_quad :
      HasDerivWithinAt (fun t : ℝ ↦ μ / 2 * ‖seg t‖ ^ (2 : ℕ))
        (μ * inner ℝ x (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    -- The quadratic shift contributes exactly `μ * ⟪x, y - x⟫` along the same segment.
    simpa [seg, InnerProductSpace.toDual_apply_apply, real_inner_smul_left] using
      (shifted_quadratic_hasFDerivAt (μ := μ) x).comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap
        (AffineMap.lineMap_apply_zero x y).symm
  have hseg_grad_shifted_formula :
      HasDerivWithinAt (fun t : ℝ ↦ shifted (seg t))
        (inner ℝ (gradQ x) (y - x) - μ * inner ℝ x (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    -- Subtract the quadratic segment derivative from the derivative of `f ∘ seg`.
    simpa [seg, shifted] using hseg_grad_f.sub hseg_grad_quad
  have hunique :=
    hseg_grad_shifted.derivWithin
      (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  have hformula :=
    hseg_grad_shifted_formula.derivWithin
      (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1))
  rw [hformula] at hunique
  exact hunique.symm

/-- Helper for Theorem 2.10: the shifted gradient pairing equals the original gradient pairing
minus `μ * ‖x - y‖²`. -/
private theorem shifted_gradient_pairing_eq
    (hQ : Convex ℝ Q) (hf_diff : DifferentiableOn ℝ f Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    inner ℝ
        (gradientWithin (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) Q x -
          gradientWithin (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) Q y)
        (x - y)
      = inner ℝ (gradQ x - gradQ y) (x - y) - μ * ‖x - y‖ ^ (2 : ℕ) := by
  let shifted : E → ℝ := fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)
  have hx_pair := inner_gradientWithin_shifted_sub (μ := μ) (f := f) hQ hf_diff hx hy
  have hy_pair := inner_gradientWithin_shifted_sub (μ := μ) (f := f) hQ hf_diff hy hx
  have hxy_neg : x - y = -(y - x) := by
    abel
  have hneg_shifted_x :
      inner ℝ (gradientWithin shifted Q x) (x - y) =
        -inner ℝ (gradientWithin shifted Q x) (y - x) := by
    rw [hxy_neg, inner_neg_right]
  have hneg_grad_x : inner ℝ (gradQ x) (x - y) = -inner ℝ (gradQ x) (y - x) := by
    rw [hxy_neg, inner_neg_right]
  rw [inner_sub_left]
  have hx_pair' :
      inner ℝ (gradientWithin shifted Q x) (x - y) =
        inner ℝ (gradQ x) (x - y) + μ * inner ℝ x (y - x) := by
    -- Flip the direction in the `x`-pairing identity and simplify the sign.
    calc
      inner ℝ (gradientWithin shifted Q x) (x - y)
          = -inner ℝ (gradientWithin shifted Q x) (y - x) := hneg_shifted_x
      _ = -(inner ℝ (gradQ x) (y - x) - μ * inner ℝ x (y - x)) := by rw [hx_pair]
      _ = inner ℝ (gradQ x) (x - y) + μ * inner ℝ x (y - x) := by
            rw [hneg_grad_x]
            ring
  calc
    inner ℝ (gradientWithin shifted Q x) (x - y) -
        inner ℝ (gradientWithin shifted Q y) (x - y)
        = (inner ℝ (gradQ x) (x - y) + μ * inner ℝ x (y - x)) -
            (inner ℝ (gradQ y) (x - y) - μ * inner ℝ y (x - y)) := by
              rw [hx_pair', hy_pair]
    _ = inner ℝ (gradQ x - gradQ y) (x - y) +
          μ * (inner ℝ x (y - x) + inner ℝ y (x - y)) := by
            rw [inner_sub_left]
            ring
    _ = inner ℝ (gradQ x - gradQ y) (x - y) - μ * ‖x - y‖ ^ (2 : ℕ) := by
          have hnorm : inner ℝ x (y - x) + inner ℝ y (x - y) = -‖x - y‖ ^ (2 : ℕ) := by
            -- Expand both pairings and collect the standard norm-square identity.
            calc
              inner ℝ x (y - x) + inner ℝ y (x - y)
                  = (inner ℝ x y - ‖x‖ ^ (2 : ℕ)) +
                      (inner ℝ y x - ‖y‖ ^ (2 : ℕ)) := by
                        rw [inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
                          real_inner_self_eq_norm_sq]
              _ = -(‖x‖ ^ (2 : ℕ) - 2 * inner ℝ x y + ‖y‖ ^ (2 : ℕ)) := by
                    rw [real_inner_comm]
                    ring
              _ = -‖x - y‖ ^ (2 : ℕ) := by
                    rw [norm_sub_sq_real]
          rw [hnorm]
          ring

/-- Helper for Theorem 2.10: monotonicity of the shifted gradient is exactly the displayed strong
pairing inequality for `gradientWithin f Q`. -/
private theorem gradientMonotoneOn_shifted_iff_strong_pairing
    (hQ : Convex ℝ Q) (hf_diff : DifferentiableOn ℝ f Q) :
    GradientMonotoneOn Q (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) ↔
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gradQ x - gradQ y) (x - y) := by
  constructor
  · intro hmono x y hx hy
    -- Rewrite the shifted monotonicity inequality into the original strong pairing inequality.
    have hmono_xy :
        0 ≤ inner ℝ
          (gradientWithin (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) Q x -
            gradientWithin (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) Q y)
          (x - y) :=
      hmono hx hy
    have hrewrite := shifted_gradient_pairing_eq (μ := μ) (f := f) hQ hf_diff hx hy
    linarith
  · intro hmono x y hx hy
    -- The same rewrite turns the strong pairing bound back into ordinary monotonicity of the
    -- shifted function.
    have hstrong_xy : μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gradQ x - gradQ y) (x - y) :=
      hmono hx hy
    have hrewrite := shifted_gradient_pairing_eq (μ := μ) (f := f) hQ hf_diff hx hy
    linarith

/-- On a convex set `Q`, a differentiable function is `μ`-strongly convex exactly when its
within-set gradient is `μ`-strongly monotone in the ambient real inner product. -/
-- Proof sketch: pass from strong convexity to convexity of `x ↦ f x - (μ / 2) * ‖x‖²`,
-- apply the first-order convexity characterization to that shifted function, and expand the
-- shifted gradient pairing.
theorem strongConvexOn_iff_gradient_monotone
    (hQ : Convex ℝ Q) (hf_diff : DifferentiableOn ℝ f Q) :
    StrongConvexOn Q μ f ↔
      ∀ ⦃x y : E⦄ (_ : x ∈ Q) (_ : y ∈ Q),
        μ * ‖x - y‖ ^ (2 : ℕ) ≤
          inner ℝ (gradQ x - gradQ y) (x - y) := by
  -- Route correction: the shifted function is handled at the level of directional pairings,
  -- avoiding any false global identity for `gradientWithin` on arbitrary convex sets.
  calc
    StrongConvexOn Q μ f
        ↔ ConvexOn ℝ Q (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) := by
          rw [strongConvexOn_iff_convex]
    _ ↔ GradientMonotoneOn Q (fun u : E ↦ f u - μ / 2 * ‖u‖ ^ (2 : ℕ)) := by
          exact convexOn_iff_gradient_monotone hQ (shifted_function_differentiableOn (μ := μ) hf_diff)
    _ ↔ ∀ ⦃x y : E⦄ (_ : x ∈ Q) (_ : y ∈ Q),
          μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gradQ x - gradQ y) (x - y) := by
          exact gradientMonotoneOn_shifted_iff_strong_pairing (μ := μ) (f := f) hQ hf_diff

/-- Theorem 2.10 on the canonical Hilbert-space owner layer: on a convex set `Q`, a
differentiable function `f` is `μ`-strongly convex exactly when either of the two standard
source-facing bridges holds, namely the strong gradient-monotonicity inequality or the quadratic
Jensen inequality. The textbook Euclidean `C¹` theorem is a direct specialization. -/
theorem strongConvexOn_tfae
    (hQ : Convex ℝ Q) (hf_diff : DifferentiableOn ℝ f Q) :
    List.TFAE
      [ StrongConvexOn Q μ f
      , ∀ ⦃x y : E⦄ (_ : x ∈ Q) (_ : y ∈ Q),
          μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (gradQ x - gradQ y) (x - y)
      , ∀ ⦃x y : E⦄ (_ : x ∈ Q) (_ : y ∈ Q) ⦃α : ℝ⦄ (_ : α ∈ Set.Icc (0 : ℝ) 1),
          f (α • x + (1 - α) • y) + α * (1 - α) * (μ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
            α * f x + (1 - α) * f y ] := by
  tfae_have 1 ↔ 2 := strongConvexOn_iff_gradient_monotone hQ hf_diff
  tfae_have 1 ↔ 3 := strongConvexOn_iff_quadratic_jensen_bound hQ
  tfae_finish

end InnerProduct

end
