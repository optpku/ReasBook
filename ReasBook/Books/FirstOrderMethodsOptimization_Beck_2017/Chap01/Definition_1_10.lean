/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open WithLp
open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 1.10: for a nonzero normal vector `a`, the hyperplane with normal vector `a` and
offset `b` is the affine subspace of points whose inner product with `a` is `b`. The defining
formula is canonical and extends to arbitrary `a`. -/
noncomputable def hyperplane (a : E) (b : ℝ) : AffineSubspace ℝ E :=
  (affineSpan ℝ ({b} : Set ℝ)).comap (((innerSL ℝ a).toLinearMap).toAffineMap)

-- Proof sketch: unfold `hyperplane`; membership in the defining set is exactly the displayed
-- inner-product equation.
/-- A point `x` lies in `hyperplane a b` exactly when its inner product with `a` is `b`. -/
@[simp] theorem mem_hyperplane_iff (a : E) (b : ℝ) (x : E) :
    x ∈ hyperplane a b ↔ ⟪a, x⟫ = b :=
  by
    rw [hyperplane, AffineSubspace.mem_comap]
    simp

section

variable {ι : Type*} [Fintype ι]

/-- The Chapter 1 hyperplane owner transported to the coordinate model `ι → ℝ` through the
canonical `L²` equivalence `toLp 2`. -/
noncomputable def coordinateHyperplane (a : ι → ℝ) (b : ℝ) : Set (ι → ℝ) :=
  (toLp 2) ⁻¹' (hyperplane (toLp 2 a) b : Set (EuclideanSpace ℝ ι))

-- Proof sketch: membership in the pulled-back hyperplane is membership in the Euclidean
-- hyperplane, which is the inner-product equation `⟪toLp 2 a, toLp 2 x⟫ = b`; the standard
-- `toLp` inner-product bridge identifies that equation with `dotProduct a x = b`.
/-- A coordinate vector `x` lies in `coordinateHyperplane a b` exactly when
`dotProduct a x = b`. -/
@[simp] theorem mem_coordinateHyperplane_iff (a x : ι → ℝ) (b : ℝ) :
    x ∈ coordinateHyperplane a b ↔ dotProduct a x = b := by
  change toLp 2 x ∈ hyperplane (toLp 2 a) b ↔ dotProduct a x = b
  rw [mem_hyperplane_iff]
  rw [show inner ℝ (toLp 2 a) (toLp 2 x) = dotProduct a x by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp a x)]

end

end
