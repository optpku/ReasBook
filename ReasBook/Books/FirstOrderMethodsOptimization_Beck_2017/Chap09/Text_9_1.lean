/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import Mathlib.Analysis.Convex.Deriv

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 9.1 is `source-facing`. The Chapter 9 owner `Definition_9_2` already provides the
canonical Bregman-distance data `B[ω]` together with its real-valued specialization
`bregmanDistance_apply_real`; this file keeps the textbook strict-convexity consequences at a
fixed pair `(x, y)`. -/

/-- Helper for Text 9.1: differentiating `ω` along the segment from `y` to `x` at `0` recovers the
gradient pairing `⟪∇ ω y, x - y⟫`. -/
lemma lineMapDerivAtZero_eq_innerGradient
    (ω : E → ℝ) {x y : E} (hy_diff : DifferentiableAt ℝ ω y) :
    HasDerivAt (fun t : ℝ ↦ ω (AffineMap.lineMap y x t))
      (inner ℝ (∇ ω y) (x - y)) 0 := by
  -- Differentiate the segment pullback by the chain rule at the left endpoint `t = 0`.
  have hbase : HasFDerivAt ω (fderiv ℝ ω y) ((AffineMap.lineMap y x) (0 : ℝ)) := by
    simpa using hy_diff.hasFDerivAt
  have hline : HasDerivAt (AffineMap.lineMap y x) (x - y) (0 : ℝ) :=
    AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := (0 : ℝ))
  have hderiv : HasDerivAt (fun t : ℝ ↦ ω (AffineMap.lineMap y x t))
      (fderiv ℝ ω y (x - y)) 0 := by
    simpa using HasFDerivAt.comp_hasDerivAt (0 : ℝ) hbase hline
  -- Rewrite the Fréchet derivative value through the gradient pairing.
  simpa [inner_gradient_left (f := ω) (x := y) (y := x - y) hy_diff] using hderiv

/-- Helper for Text 9.1: a strictly convex function stays strictly convex when restricted to the
affine segment joining two distinct points of its domain. -/
lemma strictConvexOnSegmentLineMap
    (ω : E → ℝ) (D : Set E) (hω : StrictConvexOn ℝ D ω) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y) :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ ω (AffineMap.lineMap y x t)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s hs t ht hst a b ha hb hab
  -- Put the segment endpoints back in `D` using convexity of the original domain.
  have hsD : AffineMap.lineMap y x s ∈ D := hω.1.lineMap_mem hy hx hs
  have htD : AffineMap.lineMap y x t ∈ D := hω.1.lineMap_mem hy hx ht
  have hline_injective :
      Function.Injective (AffineMap.lineMap y x : ℝ → E) :=
    AffineMap.lineMap_injective (k := ℝ) (p₀ := y) (p₁ := x) hxy.symm
  have hst' : AffineMap.lineMap y x s ≠ AffineMap.lineMap y x t := by
    intro hst_line
    exact hst (hline_injective hst_line)
  -- Transport strict convexity through the affine combination formula for `lineMap`.
  have hstrict := hω.2 hsD htD hst' ha hb hab
  -- Normalize the affine combination on the parameter line before applying `ω`.
  calc
    (fun t : ℝ ↦ ω ((AffineMap.lineMap y x) t)) (a • s + b • t)
        = ω ((AffineMap.lineMap y x) (a • s + b • t)) := rfl
    _ = ω (a • (AffineMap.lineMap y x) s + b • (AffineMap.lineMap y x) t) := by
          rw [Convex.combo_affine_apply hab]
    _ < a • (fun t : ℝ ↦ ω ((AffineMap.lineMap y x) t)) s
          + b • (fun t : ℝ ↦ ω ((AffineMap.lineMap y x) t)) t := hstrict

/-- Helper for Text 9.1: strict convexity makes the Bregman distance strictly positive away from
the diagonal. -/
lemma bregmanDistance_pos_of_ne_of_strictConvexOn
    (ω : E → ℝ) (D : Set E) (hω : StrictConvexOn ℝ D ω) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hy_diff : DifferentiableAt ℝ ω y) (hxy : x ≠ y) :
    0 < B[ω] x y := by
  let φ : ℝ → ℝ := fun t ↦ ω (AffineMap.lineMap y x t)
  have hφ_strict :
      StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ :=
    strictConvexOnSegmentLineMap ω D hω hx hy hxy
  have hφ_deriv : HasDerivAt φ (inner ℝ (∇ ω y) (x - y)) 0 :=
    lineMapDerivAtZero_eq_innerGradient ω hy_diff
  -- Compare the derivative at the left endpoint with the secant slope on `[0, 1]`.
  have hφ_slope :
      deriv φ 0 < slope φ 0 1 := by
    exact hφ_strict.deriv_lt_slope (by simp) (by simp) (show (0 : ℝ) < 1 by norm_num)
      hφ_deriv.differentiableAt
  rw [hφ_deriv.deriv] at hφ_slope
  have hsupport : inner ℝ (∇ ω y) (x - y) < ω x - ω y := by
    -- Evaluate the secant slope using the segment endpoints `0` and `1`.
    simpa [φ, slope_def_field, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      one_smul, zero_smul] using hφ_slope
  -- Rearranging the strict lower support inequality is exactly the Bregman formula.
  rw [bregmanDistance_apply_real]
  linarith

-- Proof sketch: use the first-order lower support inequality for the convex function `ω` at `y`;
-- `StrictConvexOn` is only used through its canonical `ConvexOn` companion.
/-- If `ω` is convex on `D` and differentiable at `y ∈ D`, then the associated Bregman distance
from `x ∈ D` to `y` is nonnegative. -/
theorem bregmanDistance_nonneg_of_convexOn
    (ω : E → ℝ) (D : Set E) (hω : ConvexOn ℝ D ω) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hy_diff : DifferentiableAt ℝ ω y) :
    0 ≤ B[ω] x y := by
  let φ : ℝ → ℝ := fun t ↦ ω (AffineMap.lineMap y x t)
  have hφ_convex_pre :
      ConvexOn ℝ ((AffineMap.lineMap y x) ⁻¹' D) φ := by
    simpa [φ] using (hω.comp_affineMap (AffineMap.lineMap y x))
  have hφ_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
    refine hφ_convex_pre.subset ?_ (convex_Icc 0 1)
    intro t ht
    exact hω.1.lineMap_mem hy hx ht
  have hφ_deriv : HasDerivAt φ (inner ℝ (∇ ω y) (x - y)) 0 :=
    lineMapDerivAtZero_eq_innerGradient ω hy_diff
  -- Compare the derivative at `0` with the secant slope from `0` to `1`.
  have hφ_slope :
      deriv φ 0 ≤ slope φ 0 1 := by
    exact hφ_convex.deriv_le_slope (by simp) (by simp) (show (0 : ℝ) < 1 by norm_num)
      hφ_deriv.differentiableAt
  rw [hφ_deriv.deriv] at hφ_slope
  have hsupport : inner ℝ (∇ ω y) (x - y) ≤ ω x - ω y := by
    -- Evaluate the secant slope between the segment endpoints.
    simpa [φ, slope_def_field, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      one_smul, zero_smul] using hφ_slope
  -- Rearranging the support inequality gives the Bregman nonnegativity claim.
  rw [bregmanDistance_apply_real]
  linarith

-- Proof sketch: apply the first-order lower support inequality for a differentiable convex
-- function at `y` to obtain `0 ≤ B[ω] x y`. If `x ≠ y`, strict convexity upgrades that support
-- inequality to a strict inequality, so `B[ω] x y > 0`. Combining this strict positivity with
-- the canonical diagonal identity `bregmanDistance_self_eq_zero` gives the equality
-- characterization. For this fixed pair `(x, y)`, only differentiability at the second argument
-- `y` is used.
/-- If `ω` is strictly convex on `D` and differentiable at `y ∈ D`, then the associated Bregman
distance from `x ∈ D` to `y` vanishes exactly on the diagonal. -/
theorem bregmanDistance_eq_zero_iff_eq_of_strictConvexOn
    (ω : E → ℝ) (D : Set E) (hω : StrictConvexOn ℝ D ω) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hy_diff : DifferentiableAt ℝ ω y) :
    B[ω] x y = 0 ↔ x = y := by
  constructor
  · intro hB
    -- Off the diagonal, strict convexity upgrades nonnegativity to strict positivity.
    by_contra hxy
    have hpos : 0 < B[ω] x y :=
      bregmanDistance_pos_of_ne_of_strictConvexOn ω D hω hx hy hy_diff hxy
    linarith
  · intro hxy
    -- The diagonal case is the canonical Bregman identity from Definition 9.2.
    simpa using (bregmanDistance_eq_zero_of_eq (ω := Function.toEReal ω) hxy)

/-- Text 9.1, specialized at a fixed pair `(x, y)`: if `ω` is strictly convex on `D` and
differentiable at `y ∈ D`, then the associated Bregman distance from `x` to `y` is nonnegative,
and it vanishes exactly on the diagonal. -/
theorem bregmanDistance_nonneg_and_eq_zero_iff
    (ω : E → ℝ) (D : Set E) (hω : StrictConvexOn ℝ D ω) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hy_diff : DifferentiableAt ℝ ω y) :
    0 ≤ B[ω] x y ∧ (B[ω] x y = 0 ↔ x = y) := by
  exact ⟨bregmanDistance_nonneg_of_convexOn ω D hω.convexOn hx hy hy_diff,
    bregmanDistance_eq_zero_iff_eq_of_strictConvexOn ω D hω hx hy hy_diff⟩

end
