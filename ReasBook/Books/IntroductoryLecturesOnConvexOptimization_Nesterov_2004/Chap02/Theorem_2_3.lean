/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open AffineMap
open InnerProductSpace
open scoped ConvexC1

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 2.3 lies in Euclidean first-order convex analysis on convex sets.

Sampled owner-style declarations before refining this file:
* mathlib `ConvexOn`
* mathlib `gradientWithin` / `HasGradientWithinAt`
* `ConvexOn.lower_tangent_plane` in `Definition_2_2`, the chapter owner theorem for the
  source-facing first-order inequality
* `ConvexC1On` in `Definition_2_4`, the chapter owner packaging of the textbook `C¹` hypothesis

Best owner abstraction:
* `ConvexOn ℝ Q f`, with `gradientWithin f Q` as the canonical first-order object derived from the
  within-set differentiability owner predicate `DifferentiableOn ℝ f Q`

Primitive data:
* the feasible set `Q`
* the objective `f`
* the convexity owner predicate `ConvexOn ℝ Q f`
* the within-set differentiability owner predicate `DifferentiableOn ℝ f Q`

Derived API:
* `GradientMonotoneOn Q f`, the bridge property recording monotonicity of `gradientWithin f Q`
* `convexOn_iff_gradient_monotone`, the source-facing equivalence between convexity and gradient
  monotonicity
* `ConvexOn.gradient_monotone` and `ConvexOn.of_gradient_monotone`, the owner forward and reverse
  implications
* `convexC1On_iff_gradient_monotone`, the textbook `C¹` bridge through the chapter owner
  `ConvexC1On`

Source/core/bridge triage:
* source-facing: Theorem 2.3 as the equivalence between convexity and monotonicity of the
  within-set gradient; the textbook `C¹` hypothesis is routed through `ConvexC1On`
* core/canonical: `ConvexOn ℝ Q f`
* bridge/view: passage through the lower-tangent-plane owner API from `Definition_2_2` and the
  chapter owner `ConvexC1On`
-/

section

variable {Q : Set E} {f : E → ℝ}

local notation "gradQ" => gradientWithin f Q

/-- The within-set gradient of `f` is monotone on `Q` when its increment has nonnegative
inner-product pairing with every feasible displacement. -/
def GradientMonotoneOn (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
    0 ≤ inner ℝ (gradientWithin f Q x - gradientWithin f Q y) (x - y)

namespace ConvexOn

/-- A convex function with within-set differentiability on `Q` has monotone within-set gradient on
that set. -/
-- Proof sketch: apply the first-order convexity inequality on `Q` at `x` and at `y`, expressed
-- with `gradientWithin f Q x` and `gradientWithin f Q y`, and add the two inequalities.
theorem gradient_monotone
    (hf_conv : ConvexOn ℝ Q f)
    (hf_diff : DifferentiableOn ℝ f Q) :
    GradientMonotoneOn Q f := by
  refine fun {x} ↦ ?_
  refine fun {y} ↦ ?_
  intro hx hy
  -- Compare the two tangent-plane inequalities based at `x` and `y`.
  have hxy := hf_conv.lower_tangent_plane x hx (hf_diff x hx) y hy
  have hyx := hf_conv.lower_tangent_plane y hy (hf_diff y hy) x hx
  have hsum :
      inner ℝ (gradQ x) (y - x) + inner ℝ (gradQ y) (x - y) ≤ 0 := by
    linarith
  -- Normalize the sum into the monotonicity pairing.
  have hrewrite :
      inner ℝ (gradQ x - gradQ y) (x - y) =
        -(inner ℝ (gradQ x) (y - x) + inner ℝ (gradQ y) (x - y)) := by
    have hxswap :
        inner ℝ (gradQ x) (x - y) = -inner ℝ (gradQ x) (y - x) := by
      calc
        inner ℝ (gradQ x) (x - y) = inner ℝ (gradQ x) (-(y - x)) := by
                congr 2
                abel
        _ = -inner ℝ (gradQ x) (y - x) := by rw [inner_neg_right]
    calc
      inner ℝ (gradQ x - gradQ y) (x - y)
          = inner ℝ (gradQ x) (x - y) - inner ℝ (gradQ y) (x - y) := by
              rw [inner_sub_left]
      _ = -(inner ℝ (gradQ x) (y - x)) - inner ℝ (gradQ y) (x - y) := by
            rw [hxswap]
      _ = -(inner ℝ (gradQ x) (y - x) + inner ℝ (gradQ y) (x - y)) := by
            ring
  rw [hrewrite]
  linarith

/-- Gradient monotonicity on a convex set forces convexity of a within-set differentiable function
there. -/
-- Proof sketch: use `convexOn_iff_lower_tangent_plane` from `Definition_2_2`; the monotonicity
-- hypothesis upgrades the tangent inequality for the within-set gradient to the owner convexity
-- predicate.
theorem of_gradient_monotone
    (hQ : Convex ℝ Q)
    (hf_diff : DifferentiableOn ℝ f Q)
    (hmono : GradientMonotoneOn Q f) :
    ConvexOn ℝ Q f := by
  refine (convexOn_iff_lower_tangent_plane hQ hf_diff).2 ?_
  refine fun {x} ↦ ?_
  intro hx
  refine fun {y} ↦ ?_
  intro hy
  -- Move from the source segment to a single mean-value point on that segment.
  have hmvt :
      ∃ z ∈ segment ℝ x y, f y - f x = inner ℝ (gradQ z) (y - x) := by
    rcases domain_mvt
        (fun z hz ↦ (hf_diff z hz).hasGradientWithinAt.hasFDerivWithinAt)
        hQ hx hy with ⟨z, hz, hEq⟩
    refine ⟨z, hz, ?_⟩
    simpa [toDual_apply_apply] using hEq
  rcases hmvt with ⟨z, hzseg, hEq⟩
  rw [segment_eq_image_lineMap] at hzseg
  rcases hzseg with ⟨t, ht, rfl⟩
  have hline_mem : lineMap x y t ∈ Q := hQ.mapsTo_lineMap hx hy ht
  -- Use monotonicity between the segment point and the left endpoint to compare directional
  -- derivatives along `y - x`.
  have hinner_mono :
      0 ≤ inner ℝ (gradQ (lineMap x y t) - gradQ x) (y - x) := by
    have hseg :
        0 ≤ inner ℝ (gradQ (lineMap x y t) - gradQ x) (lineMap x y t - x) := by
      exact hmono hline_mem hx
    by_cases ht0 : t = 0
    · subst ht0
      simp
    · have htne : 0 ≠ t := by
        simpa [eq_comm] using ht0
      have htpos : 0 < t := lt_of_le_of_ne ht.1 htne
      have hline : lineMap x y t - x = t • (y - x) := by
        simpa [vsub_eq_sub] using lineMap_vsub_left x y t
      rw [hline, real_inner_smul_right] at hseg
      exact (mul_nonneg_iff_of_pos_left htpos).mp hseg
  -- Translate the mean-value identity into the lower tangent inequality at `x`.
  have hcompare :
      0 ≤ inner ℝ (gradQ (lineMap x y t)) (y - x) - inner ℝ (gradQ x) (y - x) := by
    simpa [inner_sub_left] using hinner_mono
  linarith

end ConvexOn

/-- Theorem 2.3, stated on the canonical real Hilbert-space owner layer: for a convex set `Q` and
a function `f : E → ℝ` that is differentiable on `Q`, convexity of `f` on `Q` is equivalent to
monotonicity of its within-set gradient on `Q`; the main theorem is stated with the owner
hypothesis `DifferentiableOn ℝ f Q`, and the textbook `C¹` version appears below as a companion
bridge through `ConvexC1On`. The textbook Euclidean theorem is the finite-dimensional
specialization. -/
-- Proof sketch: combine the internal forward and reverse implications between convexity and the
-- monotonicity inequality for `gradientWithin f Q`.
theorem convexOn_iff_gradient_monotone
    (hQ : Convex ℝ Q)
    (hf_diff : DifferentiableOn ℝ f Q) :
    ConvexOn ℝ Q f ↔ GradientMonotoneOn Q f :=
  ⟨fun hf_conv ↦ ConvexOn.gradient_monotone hf_conv hf_diff,
    ConvexOn.of_gradient_monotone hQ hf_diff⟩

/-- The textbook `C¹` specialization of Theorem 2.3, expressed through the Chapter 2 owner
notation `𝓕¹(Q)`; the statement is given on the canonical real Hilbert-space layer, so the
original Euclidean theorem is a direct specialization. -/
theorem convexC1On_iff_gradient_monotone
    (hQ : Convex ℝ Q) :
    f ∈ 𝓕¹(Q) ↔
      ContDiffOn ℝ 1 f Q ∧ GradientMonotoneOn Q f := by
  constructor
  · intro hf
    have hf_diff : DifferentiableOn ℝ f Q :=
      (convexC1On_contDiffOn hf).differentiableOn (by simp)
    refine ⟨convexC1On_contDiffOn hf, ?_⟩
    exact
      (convexOn_iff_gradient_monotone hQ hf_diff).mp (convexC1On_convexOn hf)
  · rintro ⟨hf_contDiff, hmono⟩
    have hf_diff : DifferentiableOn ℝ f Q := hf_contDiff.differentiableOn (by simp)
    refine ⟨hf_contDiff, ?_⟩
    exact (convexOn_iff_gradient_monotone hQ hf_diff).mpr hmono

end

end
