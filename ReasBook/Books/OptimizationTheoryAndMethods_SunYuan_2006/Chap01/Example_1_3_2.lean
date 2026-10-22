/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Orthogonal

-- Semantic recall: the owner abstractions here are `convex_hyperplane`,
-- `convex_halfSpace_le`, `convex_halfSpace_ge`, `convex_halfSpace_lt`,
-- `convex_halfSpace_gt`, `Convex.lineMap_mem`, and
-- `mem_orthogonal_singleton_iff_inner_right`.

section Example132

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem isLinearMap_inner_right (p : E) : IsLinearMap ℝ (inner ℝ p) where
  map_add x y := by
    simpa using inner_add_right p x y
  map_smul c x := by
    simpa [smul_eq_mul] using inner_smul_right p x c

private theorem continuous_inner_right (p : E) : Continuous (fun x : E ↦ inner ℝ p x) :=
  continuous_const.inner continuous_id

/- Chapter01 Example 1.3.2 (1): for a real inner-product space, the sunYuanHyperplane
`{x : E | inner ℝ p x = α}` is the canonical sunYuanHyperplane cut out by the linear functional
`inner ℝ p`. -/
#check fun (p : E) (α : ℝ) ↦ convex_hyperplane (isLinearMap_inner_right p) α

/- Chapter01 Example 1.3.2 (2): the weighted-combination clause is the source-facing specialization
of `Convex.lineMap_mem` to the sunYuanHyperplane from part (1). -/
#check
  fun (p : E) (α : ℝ) {x₁ x₂ : E}
    (hx₁ : x₁ ∈ {x : E | inner ℝ p x = α})
    (hx₂ : x₂ ∈ {x : E | inner ℝ p x = α})
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) ↦ by
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
        (convex_hyperplane (isLinearMap_inner_right p) α).lineMap_mem hx₂ hx₁ hθ

/- Chapter01 Example 1.3.2 (3): the zero sunYuanHyperplane is exactly the orthogonal complement of the
line spanned by `p`. -/
#check
  fun (p : E) ↦
    show {x : E | inner ℝ p x = 0} = ((ℝ ∙ p)ᗮ : Set E) from by
      ext x
      have h : x ∈ (ℝ ∙ p)ᗮ ↔ inner ℝ p x = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right
      simpa [eq_comm] using h.symm

/- Chapter01 Example 1.3.2 (4): the closed lower half-space
`{x : E | inner ℝ p x ≤ β}` is convex. -/
#check fun (p : E) (β : ℝ) ↦ convex_halfSpace_le (isLinearMap_inner_right p) β

/- Chapter01 Example 1.3.2 (5): the closed lower half-space
`{x : E | inner ℝ p x ≤ β}` is closed. -/
#check
  fun (p : E) (β : ℝ) ↦
    show IsClosed {x : E | inner ℝ p x ≤ β} from by
      simpa [Set.preimage] using isClosed_Iic.preimage (continuous_inner_right p)

/- Chapter01 Example 1.3.2 (6): the closed upper half-space
`{x : E | β ≤ inner ℝ p x}` is convex. -/
#check fun (p : E) (β : ℝ) ↦ convex_halfSpace_ge (isLinearMap_inner_right p) β

/- Chapter01 Example 1.3.2 (7): the closed upper half-space
`{x : E | β ≤ inner ℝ p x}` is closed. -/
#check
  fun (p : E) (β : ℝ) ↦
    show IsClosed {x : E | β ≤ inner ℝ p x} from by
      simpa [Set.preimage] using isClosed_Ici.preimage (continuous_inner_right p)

/- Chapter01 Example 1.3.2 (8): the open lower half-space
`{x : E | inner ℝ p x < β}` is convex. -/
#check fun (p : E) (β : ℝ) ↦ convex_halfSpace_lt (isLinearMap_inner_right p) β

/- Chapter01 Example 1.3.2 (9): the open lower half-space
`{x : E | inner ℝ p x < β}` is open. -/
#check
  fun (p : E) (β : ℝ) ↦
    show IsOpen {x : E | inner ℝ p x < β} from by
      simpa [Set.preimage] using isOpen_Iio.preimage (continuous_inner_right p)

/- Chapter01 Example 1.3.2 (10): the open upper half-space
`{x : E | β < inner ℝ p x}` is convex. -/
#check fun (p : E) (β : ℝ) ↦ convex_halfSpace_gt (isLinearMap_inner_right p) β

/- Chapter01 Example 1.3.2 (11): the open upper half-space
`{x : E | β < inner ℝ p x}` is open. -/
#check
  fun (p : E) (β : ℝ) ↦
    show IsOpen {x : E | β < inner ℝ p x} from by
      simpa [Set.preimage] using isOpen_Ioi.preimage (continuous_inner_right p)

end Example132
