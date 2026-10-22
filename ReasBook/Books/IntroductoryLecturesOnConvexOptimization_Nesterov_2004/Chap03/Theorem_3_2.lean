/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_2

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/- Theorem 3.2 lies in convex analysis on sets in affine modules over a linearly ordered field.

Sampled owner-style declarations:
- mathlib `ConvexOn`
- mathlib `convexOn_iff_forall_pos`
- mathlib `convexOn_iff_div`
- Chapter 2 `convexOn_iff_segment_inequality`

Best owner abstraction:
- `ConvexOn 𝕜 s f`

Primitive data:
- a set `s`
- a `𝕜`-valued function `f`

Derived API:
- the segment Jensen inequality on points of `s`
- the equivalent affine-ray secant lower bound on points of `s`
- under `Convex 𝕜 s`, the owner-level equivalence with `ConvexOn 𝕜 s f`

Source/core/bridge triage:
- source-facing: the affine-ray secant criterion on a fixed set
- core/canonical: `ConvexOn 𝕜 s f`
- bridge/view: the segment-form and affine-ray-form inequalities compared below

The bridge theorem below does not own convexity of the set. That owner-level role belongs to
`ConvexOn 𝕜 s f`, and Chapter 2 already provides the canonical bridge from `ConvexOn` to the
one-parameter segment inequality. This file therefore keeps the segment-vs-ray equivalence as
bridge API and derives the owner-level corollary separately.
-/

/-- Theorem 3.2: for a function considered on a set `s`, the usual two-point convexity
inequality along segments in `s` is equivalent to the forward affine-ray secant lower bound.
Specializing to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook statement on
`ℝⁿ`. -/
-- Proof sketch: for the forward direction, write `y` as a convex combination of the extrapolation
-- point `u = y + β • (y - x)` and `x` using the weight `α = β / (1 + β)`, then rearrange the
-- usual convexity inequality. For the converse, given a convex-combination point
-- `u = α • x + (1 - α) • y`, rewrite `x` as `u + ((1 - α) / α) • (u - y)` for `α ∈ (0, 1]`,
-- apply the affine-ray inequality to the pair `(y, u)`, and rearrange.
theorem segment_inequality_iff_affine_ray_inequality
    (s : Set E) (f : E → 𝕜) :
    (∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
      ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
        α • x + (1 - α) • y ∈ s →
          f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y) ↔
    (∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
      ∀ ⦃β : 𝕜⦄, 0 ≤ β →
        y + β • (y - x) ∈ s →
          f (y + β • (y - x)) ≥ f y + β * (f y - f x)) := by
  constructor
  · intro hseg x y hx hy β hβ hz
    let z : E := y + β • (y - x)
    have hz' : z ∈ s := hz
    have hβ1 : 0 < 1 + β := by
      linarith
    have hα :
        (1 / (1 + β) : 𝕜) ∈ Set.Icc (0 : 𝕜) 1 := by
      refine ⟨div_nonneg zero_le_one hβ1.le, ?_⟩
      field_simp [hβ1.ne']
      linarith
    have hy_repr :
        (1 / (1 + β) : 𝕜) • z + (1 - 1 / (1 + β)) • x = y := by
      have hs :
          (1 + β) • ((1 / (1 + β) : 𝕜) • z + (1 - 1 / (1 + β)) • x) = (1 + β) • y := by
        dsimp [z]
        have hβx : (1 + β - 1 : 𝕜) = β := by
          ring
        calc
          (1 + β) • ((1 / (1 + β) : 𝕜) • (y + β • (y - x)) + (1 - 1 / (1 + β)) • x)
              = ((1 + β) * (1 / (1 + β))) • (y + β • (y - x)) +
                  ((1 + β) * (1 - 1 / (1 + β))) • x := by
                    rw [smul_add, smul_smul, smul_smul]
          _ = y + β • (y - x) + (1 + β - 1) • x := by
                field_simp [hβ1.ne']
                simp [one_smul]
          _ = (1 + β) • y := by
                rw [hβx, smul_sub]
                abel_nf
                rw [add_smul, one_smul]
      exact smul_right_injective E hβ1.ne' hs
    have hsegment :
        f y ≤ (1 / (1 + β)) * f z + (1 - 1 / (1 + β)) * f x := by
      have hy' : (1 / (1 + β) : 𝕜) • z + (1 - 1 / (1 + β)) • x ∈ s := by
        rw [hy_repr]
        exact hy
      have hsegment' := hseg hz' hx hα hy'
      rw [hy_repr] at hsegment'
      exact hsegment'
    have hcoeff : (1 - 1 / (1 + β) : 𝕜) = β / (1 + β) := by
      field_simp [hβ1.ne']
      ring
    rw [hcoeff] at hsegment
    have hmult := mul_le_mul_of_nonneg_left hsegment hβ1.le
    field_simp [hβ1.ne'] at hmult
    dsimp [z] at hmult ⊢
    nlinarith
  · intro hray x y hx hy α hα hu
    let u : E := α • x + (1 - α) • y
    have hu' : u ∈ s := hu
    by_cases hα0 : α = 0
    · simp [hα0]
    · have hαpos : 0 < α := lt_of_le_of_ne hα.1 (by simpa [eq_comm] using hα0)
      have hy_sub : (1 - α) • y - y = (-α) • y := by
        calc
          (1 - α) • y - y = (1 - α) • y + (-1 : 𝕜) • y := by
            rw [sub_eq_add_neg, neg_one_smul]
          _ = ((1 - α) + (-1 : 𝕜)) • y := by
            rw [← add_smul]
          _ = (-α) • y := by
            congr 1
            ring
      have hu_sub : u - y = α • (x - y) := by
        calc
          u - y = α • x + (-α) • y := by
            dsimp [u]
            rw [add_sub_assoc, hy_sub]
          _ = α • x + -(α • y) := by
            rw [neg_smul]
          _ = α • x - α • y := by
            rw [sub_eq_add_neg]
          _ = α • (x - y) := by
            rw [smul_sub]
      have hx_repr : u + ((1 - α) / α) • (u - y) = x := by
        have hcoeff : (((1 - α) / α) * α : 𝕜) = 1 - α := by
          field_simp [hαpos.ne']
        calc
          u + ((1 - α) / α) • (u - y)
              = α • x + (1 - α) • y + (((1 - α) / α) * α) • (x - y) := by
                  dsimp [u]
                  rw [hu_sub, mul_smul]
          _ = α • x + (1 - α) • y + (1 - α) • (x - y) := by
                simp [hcoeff]
          _ = x := by
                rw [smul_sub]
                abel_nf
                have hone : (α + (1 + -1 * α) : 𝕜) = 1 := by
                  ring
                rw [← add_smul]
                simp
      have hβ : 0 ≤ (1 - α) / α := by
        exact div_nonneg (sub_nonneg.mpr hα.2) hαpos.le
      have hray' :
          f x ≥ f u + ((1 - α) / α) * (f u - f y) := by
        have hx' : u + ((1 - α) / α) • (u - y) ∈ s := by
          simpa [hx_repr] using hx
        simpa [hx_repr] using hray hy hu' hβ hx'
      have hmult := mul_le_mul_of_nonneg_left hray' hαpos.le
      field_simp [hαpos.ne'] at hmult
      dsimp [u] at hmult ⊢
      nlinarith

/-- On a convex set `s`, the affine-ray secant lower bound is equivalent to the canonical owner
predicate `ConvexOn 𝕜 s f`. -/
-- Proof sketch: combine Chapter 2's equivalence between `ConvexOn` and the one-parameter segment
-- inequality with `segment_inequality_iff_affine_ray_inequality`.
theorem convexOn_iff_affine_ray_inequality
    (s : Set E) (f : E → 𝕜) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f ↔
    (∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
      ∀ ⦃β : 𝕜⦄, 0 ≤ β →
        y + β • (y - x) ∈ s →
          f (y + β • (y - x)) ≥ f y + β * (f y - f x)) := by
  have howner :
      ConvexOn 𝕜 s f ↔
        ∀ ⦃x : E⦄, x ∈ s →
          ∀ ⦃y : E⦄, y ∈ s →
            ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
              f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y :=
    convexOn_iff_segment_inequality hs
  have hsegment :
      ConvexOn 𝕜 s f ↔
        ∀ ⦃x y : E⦄, x ∈ s → y ∈ s →
          ∀ ⦃α : 𝕜⦄, α ∈ Set.Icc (0 : 𝕜) 1 →
            α • x + (1 - α) • y ∈ s →
              f (α • x + (1 - α) • y) ≤ α * f x + (1 - α) * f y := by
    constructor
    · intro hf x y hx hy α hα _
      exact howner.mp hf hx hy hα
    · intro h
      refine howner.mpr ?_
      intro x hx y hy α hα
      have hxy : α • x + (1 - α) • y ∈ s := by
        refine hs hx hy hα.1 (sub_nonneg.mpr hα.2) ?_
        ring
      exact h hx hy hα hxy
  exact hsegment.trans (segment_inequality_iff_affine_ray_inequality s f)

end
