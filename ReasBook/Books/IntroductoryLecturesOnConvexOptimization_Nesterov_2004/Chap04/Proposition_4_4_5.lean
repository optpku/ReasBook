/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Manifold

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

/- Proposition 4.4.5 lies in the local first-order smooth remainder domain for vector-valued maps
on convex subsets of real normed spaces.

Sampled owner-style declarations:
* the bundled smooth-map owner `C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯` from `Definition_4_4_8`;
* mathlib `LipschitzOnWith L (fun z ↦ fderiv ℝ f z) s`, the canonical on-set Jacobian-Lipschitz
  owner;
* mathlib `AffineMap.lineMap`, the canonical segment parameterization bridge;
* mathlib `taylor_mean_remainder_bound`, the codomain-general first-order Taylor remainder bound on
  a segment;
* mathlib `norm_image_sub_le_of_norm_deriv_le_segment'`, the one-dimensional mean-value estimate
  behind that Taylor bound.

Best owner abstraction:
* source-facing: the quadratic first-order Taylor remainder bound for a residual map with
  Jacobian Lipschitz on a convex feasible set;
* core/canonical: the bundled smooth map together with `LipschitzOnWith` on the derivative map;
* bridge/view: restriction to the affine line segment from `x` to `y`.

Primitive data:
* the smooth residual map `problem`;
* the feasible set `𝓕`;
* the derivative-Lipschitz owner `h_jacobian_lipschitz`.

Derived API:
* the pointwise quadratic remainder estimate at `x` and `y`.

The previous quantified hypothesis duplicated the owner content of `LipschitzOnWith`. This file
keeps the source-facing proposition but exposes the derivative control through the canonical
owner abstraction directly. The earlier interval-integral route would have imported the
proof-artifact hypothesis `[CompleteSpace F]` from `taylor_integral_remainder`; the proposition
itself is only about a first-order Taylor bound in an arbitrary real normed codomain, so the
ambient completeness assumption is removed from the public API. -/

namespace ContMDiffMap

open AffineMap

-- Restrict the smooth map to the segment from `x` to `y`, subtract its affine approximation at
-- `x`, and differentiate the resulting one-variable remainder explicitly.
/-- Helper for Proposition 4.4.5: the corrected remainder along the segment from `x` to `y`
has derivative given by the Jacobian increment applied to the segment direction. -/
private theorem segment_corrected_remainder_sub_sub
    (problem : SmoothMap) (x y : E) (v : F) :
    (fun u : ℝ ↦ problem (AffineMap.lineMap x y u) - (problem x + u • v)) =
      (fun u : ℝ ↦ problem (AffineMap.lineMap x y u) - problem x - u • v) := by
  -- Regroup the affine correction so the remainder stays in the left-associated subtraction form.
  ext u
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Proposition 4.4.5: the corrected remainder along the segment from `x` to `y`
has derivative given by the Jacobian increment applied to the segment direction. -/
private theorem segment_corrected_remainder_hasDerivAt
    (problem : SmoothMap) (x y : E) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦
        problem (AffineMap.lineMap x y u) - problem x -
          u • (fderiv ℝ problem x (y - x)))
      (((fderiv ℝ problem (AffineMap.lineMap x y t)) - fderiv ℝ problem x) (y - x))
      t := by
  -- Differentiate the segment restriction of `problem` using the derivative of `lineMap`.
  have hdiff : DifferentiableAt ℝ problem (AffineMap.lineMap x y t) := by
    exact (problem.contMDiff.contDiff.contDiffAt (x := AffineMap.lineMap x y t)).differentiableAt
      (by simp)
  have hseg :
      HasDerivAt
        (fun u : ℝ ↦ problem (AffineMap.lineMap x y u))
        ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x))
        t := by
    simpa [Function.comp] using
      ((hdiff.hasFDerivAt.comp t
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).hasFDerivAt)).hasDerivAt
  -- The affine correction contributes the constant Jacobian term at `x`.
  have hlin :
      HasDerivAt
        (fun u : ℝ ↦ u • (fderiv ℝ problem x (y - x)))
        (fderiv ℝ problem x (y - x))
        t := by
    simpa [one_smul] using
      ((hasDerivAt_id t).smul_const (fderiv ℝ problem x (y - x)))
  have hconst_add_lin :
      HasDerivAt
        (fun u : ℝ ↦ problem x + u • (fderiv ℝ problem x (y - x)))
        (0 + fderiv ℝ problem x (y - x))
        t := by
    -- Package the constant and linear parts into the exact affine correction shape.
    exact (hasDerivAt_const t (problem x)).add hlin
  -- Subtract the affine model and collect the two derivative contributions.
  have hmain_parenthesized :
      HasDerivAt
        (fun u : ℝ ↦
          problem (AffineMap.lineMap x y u) -
            (problem x + u • (fderiv ℝ problem x (y - x))))
        ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x) -
          (0 + fderiv ℝ problem x (y - x)))
        t := by
    -- Keep the derivative in its native subtraction-of-functions form before rewriting the
    -- function expression itself.
    exact hseg.sub hconst_add_lin
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦
          problem (AffineMap.lineMap x y u) - problem x -
            u • (fderiv ℝ problem x (y - x)))
        ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x) -
          fderiv ℝ problem x (y - x))
        t := by
    -- Rewrite the parenthesized subtraction into the exact remainder shape used downstream.
    simpa [zero_add, segment_corrected_remainder_sub_sub] using hmain_parenthesized
  simpa [ContinuousLinearMap.sub_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hmain

/-- Helper for Proposition 4.4.5: the corrected segment remainder vanishes at `0` and equals the
first-order Taylor remainder at `1`. -/
private theorem segment_corrected_remainder_endpoints
    (problem : SmoothMap) (x y : E) :
    let R : ℝ → F := fun t ↦
      problem (AffineMap.lineMap x y t) - problem x -
        t • (fderiv ℝ problem x (y - x))
    R 0 = 0 ∧ R 1 = problem y - problem x - fderiv ℝ problem x (y - x) := by
  -- Evaluating at the segment endpoints recovers the remainder from the statement.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4.4.5: the Jacobian Lipschitz bound controls the derivative of the
corrected segment remainder by `L t ‖y - x‖²` on `(0, 1)`. -/
private theorem segment_corrected_remainder_deriv_norm_le
    (problem : SmoothMap)
    {𝓕 : Set E} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖deriv
        (fun u : ℝ ↦
          problem (AffineMap.lineMap x y u) - problem x -
            u • (fderiv ℝ problem x (y - x)))
        t‖ ≤
      (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
  -- Start from the explicit derivative formula for the corrected segment remainder.
  have hderivAt := segment_corrected_remainder_hasDerivAt problem x y t
  rw [hderivAt.deriv]
  have hline_mem : AffineMap.lineMap x y t ∈ 𝓕 :=
    h𝓕.lineMap_mem hx hy (Set.mem_Icc_of_Ioo ht)
  have hjacobian_bound :
      ‖fderiv ℝ problem (AffineMap.lineMap x y t) - fderiv ℝ problem x‖ ≤
        (L : ℝ) * ‖AffineMap.lineMap x y t - x‖ := by
    simpa [dist_eq_norm] using
      h_jacobian_lipschitz.dist_le_mul (AffineMap.lineMap x y t) hline_mem x hx
  have hsegment_norm :
      ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
    calc
      ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
        simp [AffineMap.lineMap_apply_module']
      _ = |t| * ‖y - x‖ := norm_smul t (y - x)
      _ = t * ‖y - x‖ := by
        simp [abs_of_pos ht.1]
  -- Combine the operator-norm estimate with the Lipschitz control on the Jacobian.
  calc
    ‖((fderiv ℝ problem (AffineMap.lineMap x y t)) - fderiv ℝ problem x) (y - x)‖ ≤
        ‖fderiv ℝ problem (AffineMap.lineMap x y t) - fderiv ℝ problem x‖ * ‖y - x‖ :=
      (fderiv ℝ problem (AffineMap.lineMap x y t) - fderiv ℝ problem x).le_opNorm (y - x)
    _ ≤ ((L : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
      gcongr
    _ = ((L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
      rw [hsegment_norm]
    _ = (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
      ring

-- Proof sketch: restrict `problem` to the affine segment from `x` to `y`, apply the codomain-free
-- first-order Taylor remainder bound on `[0, 1]`, use convexity of `𝓕` to keep the segment inside
-- the feasible set, and bound the second derivative along the segment by the Jacobian-Lipschitz
-- estimate coming from `h_jacobian_lipschitz`. This yields the textbook factor `1 / 2` without
-- assuming completeness of the codomain.
/-- Proposition 4.4.5: if the Jacobian of a smooth nonlinear equation problem is `L`-Lipschitz on
a convex feasible set `𝓕`, then for all `x, y ∈ 𝓕` the first-order Taylor remainder of the
residual map satisfies
`‖F(y) - F(x) - F'(x)(y - x)‖ ≤ (L / 2) * ‖y - x‖²`. -/
theorem jacobian_lipschitz_taylor_remainder_le
    (problem : SmoothMap)
    {𝓕 : Set E} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ‖problem y - problem x - fderiv ℝ problem x (y - x)‖ ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let R : ℝ → F := fun t ↦
    problem (AffineMap.lineMap x y t) - problem x -
      t • (fderiv ℝ problem x (y - x))
  -- The one-variable corrected remainder is continuous on `[0, 1]`.
  have hcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (segment_corrected_remainder_hasDerivAt problem x y t).continuousAt.continuousWithinAt
  -- The derivative formula makes the corrected remainder differentiable on `(0, 1)`.
  have hdiff : DifferentiableOn ℝ R (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (segment_corrected_remainder_hasDerivAt problem x y t).differentiableAt
      |>.differentiableWithinAt
  -- Apply the integral estimate with the Jacobian-Lipschitz majorant on the segment.
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := R)
      (B := fun t : ℝ ↦ (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num) hcont hdiff
      (Filter.Eventually.of_forall fun t ht_mem ↦
        segment_corrected_remainder_deriv_norm_le
          problem h𝓕 h_jacobian_lipschitz x y hx hy ht_mem)
      (by
        simpa [mul_assoc] using
          (show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
            intervalIntegrable_id).const_mul ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)))
  have hendpoint := segment_corrected_remainder_endpoints problem x y
  have hR0 : R 0 = 0 := by
    simpa [R] using hendpoint.1
  have hR1 :
      R 1 = problem y - problem x - fderiv ℝ problem x (y - x) := by
    simpa [R] using hendpoint.2
  rw [hR1, hR0, sub_zero] at hbound
  calc
    ‖problem y - problem x - fderiv ℝ problem x (y - x)‖ ≤
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := hbound
    _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      -- Compute the scalar factor `∫_0^1 t dt = 1 / 2`.
      calc
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) =
            ∫ t in (0 : ℝ)..1, ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * t := by
              congr with t
              ring
        _ = ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
              rw [intervalIntegral.integral_const_mul]
        _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
              rw [integral_id]
              norm_num
              ring

end ContMDiffMap
