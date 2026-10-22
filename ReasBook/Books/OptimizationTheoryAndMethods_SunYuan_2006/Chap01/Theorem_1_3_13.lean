/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus

-- Semantic recall hits verified for this item:
-- `StrongConvexOn`, `strongConvexOn_iff_convex`, `HasGradientAt`.

section Theorem1313

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {S : Set E} {f : E → ℝ}

/-- Helper for Chapter01 Theorem 1.3.13: a convex differentiable function lies above each of its
first-order affine tangents. -/
lemma ge_gradient_inner_sub_of_convexOn
    (hS_open : IsOpen S) (hconv : ConvexOn ℝ S f) (hf : DifferentiableOn ℝ f S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    f y ≥ f x + inner ℝ (gradient f x) (y - x) := by
  let g : ℝ → ℝ := f ∘ AffineMap.lineMap x y
  let T : Set ℝ := (AffineMap.lineMap x y) ⁻¹' S
  have hgconv : ConvexOn ℝ T g := by
    -- Restrict the convex function to the affine line through `x` and `y`.
    simpa [g, T] using hconv.comp_affineMap (AffineMap.lineMap x y)
  have h0 : (0 : ℝ) ∈ T := by
    simpa [T] using hx
  have h1 : (1 : ℝ) ∈ T := by
    simpa [T] using hy
  have hdiffx : DifferentiableAt ℝ f x :=
    (hf x hx).differentiableAt (hS_open.mem_nhds hx)
  have hderiv_g :
      HasDerivAt g (inner ℝ (gradient f x) (y - x)) 0 := by
    -- The derivative along the line is the directional derivative at `x`.
    simpa [g] using
      (hdiffx.hasGradientAt.hasFDerivAt.comp_hasDerivAt_of_eq
        (hf := AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := 0))
        (hy := (AffineMap.lineMap_apply_zero x y).symm))
  have hslope :
      inner ℝ (gradient f x) (y - x) ≤ f y - f x := by
    have h' := hgconv.deriv_le_slope h0 h1 zero_lt_one hderiv_g.differentiableAt
    rw [hderiv_g.deriv] at h'
    simpa [g, slope_def_field] using h'
  linarith

/-- Helper for Chapter01 Theorem 1.3.13: the first-order supporting inequality implies convexity
by the textbook weighted-sum argument. -/
lemma convexOn_of_ge_gradient_inner_sub
    (hS_convex : Convex ℝ S)
    (hgrad : ∀ x ∈ S, ∀ y ∈ S, f y ≥ f x + inner ℝ (gradient f x) (y - x)) :
    ConvexOn ℝ S f := by
  refine ⟨hS_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ S := hS_convex hx hy ha hb hab
  have hx_support := hgrad z hz x hx
  have hy_support := hgrad z hz y hy
  have hx_mul : a * (f z + inner ℝ (gradient f z) (x - z)) ≤ a * f x :=
    mul_le_mul_of_nonneg_left hx_support ha
  have hy_mul : b * (f z + inner ℝ (gradient f z) (y - z)) ≤ b * f y :=
    mul_le_mul_of_nonneg_left hy_support hb
  have hcancel_vec : a • (x - z) + b • (y - z) = 0 := by
    -- The weighted displacement from the base point `z` cancels exactly.
    calc
      a • (x - z) + b • (y - z) = (a • x + b • y) - (a • z + b • z) := by
        rw [smul_sub, smul_sub]
        abel_nf
      _ = (a • x + b • y) - z := by
        rw [← add_smul, hab, one_smul]
      _ = z - z := by rfl
      _ = 0 := sub_self z
  have hcancel :
      a * inner ℝ (gradient f z) (x - z) + b * inner ℝ (gradient f z) (y - z) = 0 := by
    -- Linearize the inner product to expose the zero vector from `hcancel_vec`.
    calc
      a * inner ℝ (gradient f z) (x - z) + b * inner ℝ (gradient f z) (y - z)
          = inner ℝ (gradient f z) (a • (x - z) + b • (y - z)) := by
              rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      _ = inner ℝ (gradient f z) 0 := by rw [hcancel_vec]
      _ = 0 := by simp
  have hsum : a * (f z + inner ℝ (gradient f z) (x - z)) +
      b * (f z + inner ℝ (gradient f z) (y - z)) ≤ a * f x + b * f y :=
    add_le_add hx_mul hy_mul
  have hleft :
      a * (f z + inner ℝ (gradient f z) (x - z)) +
        b * (f z + inner ℝ (gradient f z) (y - z)) = f z := by
    calc
      a * (f z + inner ℝ (gradient f z) (x - z)) +
          b * (f z + inner ℝ (gradient f z) (y - z))
          = (a + b) * f z +
              (a * inner ℝ (gradient f z) (x - z) +
                b * inner ℝ (gradient f z) (y - z)) := by ring
      _ = f z + 0 := by rw [hab, one_mul, hcancel]
      _ = f z := by ring
  simpa [z, smul_eq_mul] using hleft ▸ hsum

/-- Helper for Chapter01 Theorem 1.3.13: differentiating the quadratic shift
`z ↦ f z - (c / 2) * ‖z‖ ^ 2` subtracts `c • x` from the gradient. -/
lemma hasGradientAt_sub_half_mul_norm_sq {c : ℝ} {x g : E}
    (hf : HasGradientAt f g x) :
    HasGradientAt (fun z ↦ f z - (c / 2) * ‖z‖ ^ (2 : ℕ)) (g - c • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  have hnorm :
      HasFDerivAt (fun z : E ↦ (c / 2) * ‖z‖ ^ (2 : ℕ))
        (c • InnerProductSpace.toDual ℝ E x) x := by
    have hnorm_sq :
        HasFDerivAt (fun z : E ↦ (c / 2) * ‖z‖ ^ (2 : ℕ))
          ((c / 2) • (2 • innerSL ℝ x)) x := by
      simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (c / 2)
    have hmap :
        ((c / 2) • (2 • innerSL ℝ x)) = c • InnerProductSpace.toDual ℝ E x := by
      ext y
      simp [innerSL_apply_apply]
      ring
    simpa [hmap] using hnorm_sq
  -- Subtract the quadratic derivative from the derivative of `f`.
  have hdiff :
      HasFDerivAt
        (f - fun z : E ↦ (c / 2) * ‖z‖ ^ (2 : ℕ))
        (InnerProductSpace.toDual ℝ E g - c • InnerProductSpace.toDual ℝ E x) x :=
    hf.sub hnorm
  have hdual :
      InnerProductSpace.toDual ℝ E (g - c • x) =
        InnerProductSpace.toDual ℝ E g - c • InnerProductSpace.toDual ℝ E x := by
    ext y
    change inner ℝ (g - c • x) y = inner ℝ g y - c * inner ℝ x y
    rw [inner_sub_left, real_inner_smul_left]
  have hfunc :
      (fun z : E ↦ f z - (c / 2) * ‖z‖ ^ (2 : ℕ)) =
        (f - fun z : E ↦ (c / 2) * ‖z‖ ^ (2 : ℕ)) := by
    funext z
    rfl
  rw [hfunc]
  simpa [hdual] using hdiff

/-- Helper for Chapter01 Theorem 1.3.13: the supporting inequality for the shifted function
`z ↦ f z - (c / 2) * ‖z‖ ^ 2` is equivalent to the strong supporting inequality for `f`. -/
lemma sub_half_mul_norm_sq_supporting_iff {c fx fy : ℝ} {x y g : E} :
    fy - (c / 2) * ‖y‖ ^ (2 : ℕ) ≥
        fx - (c / 2) * ‖x‖ ^ (2 : ℕ) + inner ℝ (g - c • x) (y - x) ↔
      fy ≥ fx + inner ℝ g (y - x) + (c / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Normalize both inequalities to the same quadratic expansion.
  constructor <;> intro h
  · have hnorm : ‖y - x‖ ^ (2 : ℕ) = ‖y‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖x‖ ^ (2 : ℕ) := by
      simpa using norm_sub_sq_real y x
    have hnorm' :
        (c / 2) * ‖y - x‖ ^ (2 : ℕ) =
          (c / 2) * ‖y‖ ^ (2 : ℕ) - c * inner ℝ y x + (c / 2) * ‖x‖ ^ (2 : ℕ) := by
      calc
        (c / 2) * ‖y - x‖ ^ (2 : ℕ) = c * ‖y - x‖ ^ (2 : ℕ) * (1 / 2 : ℝ) := by ring
        _ = c * (‖y‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖x‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
              rw [hnorm]
        _ = (c / 2) * ‖y‖ ^ (2 : ℕ) - c * inner ℝ y x + (c / 2) * ‖x‖ ^ (2 : ℕ) := by ring
    have hinner : inner ℝ (g - c • x) (y - x) =
        inner ℝ g (y - x) - c * inner ℝ y x + c * ‖x‖ ^ (2 : ℕ) := by
      have hxy : inner ℝ x (y - x) = inner ℝ x y - ‖x‖ ^ (2 : ℕ) := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      calc
        inner ℝ (g - c • x) (y - x)
            = inner ℝ g (y - x) - inner ℝ (c • x) (y - x) := by rw [inner_sub_left]
        _ = inner ℝ g (y - x) - c * inner ℝ x (y - x) := by rw [real_inner_smul_left]
        _ = inner ℝ g (y - x) - c * (inner ℝ x y - ‖x‖ ^ (2 : ℕ)) := by rw [hxy]
        _ = inner ℝ g (y - x) - c * inner ℝ y x + c * ‖x‖ ^ (2 : ℕ) := by
              rw [real_inner_comm x y]
              ring
    rw [hinner] at h
    nlinarith [h, hnorm']
  · have hnorm : ‖y - x‖ ^ (2 : ℕ) = ‖y‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖x‖ ^ (2 : ℕ) := by
      simpa using norm_sub_sq_real y x
    have hnorm' :
        (c / 2) * ‖y - x‖ ^ (2 : ℕ) =
          (c / 2) * ‖y‖ ^ (2 : ℕ) - c * inner ℝ y x + (c / 2) * ‖x‖ ^ (2 : ℕ) := by
      calc
        (c / 2) * ‖y - x‖ ^ (2 : ℕ) = c * ‖y - x‖ ^ (2 : ℕ) * (1 / 2 : ℝ) := by ring
        _ = c * (‖y‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖x‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
              rw [hnorm]
        _ = (c / 2) * ‖y‖ ^ (2 : ℕ) - c * inner ℝ y x + (c / 2) * ‖x‖ ^ (2 : ℕ) := by ring
    have hinner : inner ℝ (g - c • x) (y - x) =
        inner ℝ g (y - x) - c * inner ℝ y x + c * ‖x‖ ^ (2 : ℕ) := by
      have hxy : inner ℝ x (y - x) = inner ℝ x y - ‖x‖ ^ (2 : ℕ) := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      calc
        inner ℝ (g - c • x) (y - x)
            = inner ℝ g (y - x) - inner ℝ (c • x) (y - x) := by rw [inner_sub_left]
        _ = inner ℝ g (y - x) - c * inner ℝ x (y - x) := by rw [real_inner_smul_left]
        _ = inner ℝ g (y - x) - c * (inner ℝ x y - ‖x‖ ^ (2 : ℕ)) := by rw [hxy]
        _ = inner ℝ g (y - x) - c * inner ℝ y x + c * ‖x‖ ^ (2 : ℕ) := by
              rw [real_inner_comm x y]
              ring
    rw [hinner]
    nlinarith [h, hnorm']

-- The textbook states these equivalences for nonempty open convex sets, but nonemptiness is
-- redundant for the Lean statements below.

/-- Chapter01 Theorem 1.3.13 (1). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is differentiable on `S`, then `f` is convex on `S` if and only if
`f y ≥ f x + inner ℝ (gradient f x) (y - x)` for all `x, y ∈ S`. -/
theorem convexOn_iff_ge_gradient_inner_sub
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hf : DifferentiableOn ℝ f S) :
    ConvexOn ℝ S f ↔
      ∀ x ∈ S, ∀ y ∈ S,
        f y ≥ f x + inner ℝ (gradient f x) (y - x) := by
  constructor
  · intro hconv x hx y hy
    -- Restrict the convex function to the line through `x` and `y`.
    exact ge_gradient_inner_sub_of_convexOn hS_open hconv hf hx hy
  · intro hgrad
    -- Evaluate the assumed support inequality at the convex combination point.
    exact convexOn_of_ge_gradient_inner_sub hS_convex hgrad

/-- Chapter01 Theorem 1.3.13 (2). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is differentiable on `S`, then `f` is strictly convex on `S` if and only if
`f y > f x + inner ℝ (gradient f x) (y - x)` for all `x, y ∈ S` with `y ≠ x`. -/
theorem strictConvexOn_iff_gt_gradient_inner_sub
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hf : DifferentiableOn ℝ f S) :
    StrictConvexOn ℝ S f ↔
      ∀ x ∈ S, ∀ y ∈ S, y ≠ x →
        f y > f x + inner ℝ (gradient f x) (y - x) := by
  constructor
  · intro hstrict x hx y hy hyx
    let z := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
    have hz : z ∈ S := hS_convex hx hy (by positivity) (by positivity) (by ring)
    have hmid : f z < (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f y := by
      -- Strict convexity at the midpoint gives the upper bound from the source proof.
      simpa [z, smul_eq_mul, add_comm, add_left_comm, add_assoc] using
        hstrict.2 hx hy hyx.symm (by positivity) (by positivity) (by ring)
    have hsupport : f z ≥ f x + inner ℝ (gradient f x) (z - x) := by
      exact ge_gradient_inner_sub_of_convexOn hS_open hstrict.convexOn hf hx hz
    have hzsub : z - x = (1 / 2 : ℝ) • (y - x) := by
      have hzline : z = AffineMap.lineMap x y (1 / 2 : ℝ) := by
        dsimp [z]
        rw [AffineMap.lineMap_apply_module]
        norm_num
      calc
        z - x = AffineMap.lineMap x y (1 / 2 : ℝ) - x := by rw [hzline]
        _ = (1 / 2 : ℝ) • (y - x) := by
          simp [AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm]
    have hsupport' : f x + (1 / 2 : ℝ) * inner ℝ (gradient f x) (y - x) ≤ f z := by
      have hsupport'' : f x + inner ℝ (gradient f x) (z - x) ≤ f z := by linarith
      rw [hzsub, real_inner_smul_right] at hsupport''
      exact hsupport''
    linarith
  · intro hgrad
    refine ⟨hS_convex, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    let z := a • x + b • y
    have hz : z ∈ S := hS_convex hx hy ha.le hb.le hab
    have hzx : x ≠ z := by
      have hba : b = 1 - a := by linarith
      have hzline : z = AffineMap.lineMap y x a := by
        simp [z, AffineMap.lineMap_apply_module, hba, add_comm]
      intro hzx
      rw [hzline] at hzx
      rcases (AffineMap.lineMap_eq_right_iff (p₀ := y) (p₁ := x) (c := a)).1 hzx.symm with h' | h'
      · exact hxy h'.symm
      · linarith
    have hzy : y ≠ z := by
      have hab' : a = 1 - b := by linarith
      have hzline : z = AffineMap.lineMap x y b := by
        simp [z, AffineMap.lineMap_apply_module, hab', add_comm]
      intro hzy
      rw [hzline] at hzy
      rcases (AffineMap.lineMap_eq_right_iff (p₀ := x) (p₁ := y) (c := b)).1 hzy.symm with h' | h'
      · exact hxy h'
      · linarith
    have hx_support := hgrad z hz x hx hzx
    have hy_support := hgrad z hz y hy hzy
    have hx_mul : a * (f z + inner ℝ (gradient f z) (x - z)) < a * f x :=
      (mul_lt_mul_of_pos_left hx_support ha)
    have hy_mul : b * (f z + inner ℝ (gradient f z) (y - z)) < b * f y :=
      (mul_lt_mul_of_pos_left hy_support hb)
    have hcancel_vec : a • (x - z) + b • (y - z) = 0 := by
      -- The same cancellation as in the convex case removes the gradient term.
      calc
        a • (x - z) + b • (y - z) = (a • x + b • y) - (a • z + b • z) := by
          rw [smul_sub, smul_sub]
          abel_nf
        _ = (a • x + b • y) - z := by
          rw [← add_smul, hab, one_smul]
        _ = z - z := by rfl
        _ = 0 := sub_self z
    have hcancel :
        a * inner ℝ (gradient f z) (x - z) + b * inner ℝ (gradient f z) (y - z) = 0 := by
      calc
        a * inner ℝ (gradient f z) (x - z) + b * inner ℝ (gradient f z) (y - z)
            = inner ℝ (gradient f z) (a • (x - z) + b • (y - z)) := by
                rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        _ = inner ℝ (gradient f z) 0 := by rw [hcancel_vec]
        _ = 0 := by simp
    have hsum : a * (f z + inner ℝ (gradient f z) (x - z)) +
        b * (f z + inner ℝ (gradient f z) (y - z)) < a * f x + b * f y :=
      add_lt_add hx_mul hy_mul
    have hleft :
        a * (f z + inner ℝ (gradient f z) (x - z)) +
          b * (f z + inner ℝ (gradient f z) (y - z)) = f z := by
      calc
        a * (f z + inner ℝ (gradient f z) (x - z)) +
            b * (f z + inner ℝ (gradient f z) (y - z))
            = (a + b) * f z +
                (a * inner ℝ (gradient f z) (x - z) +
                  b * inner ℝ (gradient f z) (y - z)) := by ring
        _ = f z + 0 := by rw [hab, one_mul, hcancel]
        _ = f z := by ring
    simpa [z, smul_eq_mul] using hleft ▸ hsum

/-- Chapter01 Theorem 1.3.13 (3). The source states this on `ℝ^n`; the canonical Lean statement
uses an arbitrary real complete inner product space. If `S` is open and convex and
`f : E → ℝ` is differentiable on `S`, then `f` is uniformly, equivalently strongly, convex on
`S` if and only if there is a constant `c > 0` such that
`f y ≥ f x + inner ℝ (gradient f x) (y - x) + (c / 2) * ‖y - x‖ ^ 2`
for all `x, y ∈ S`, formalized as `∃ c > 0, StrongConvexOn S c f`. -/
theorem exists_strongConvexOn_iff_ge_gradient_inner_sub_add_sq
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hf : DifferentiableOn ℝ f S) :
    (∃ c > 0, StrongConvexOn S c f) ↔
      ∃ c > 0, ∀ x ∈ S, ∀ y ∈ S,
        f y ≥ f x + inner ℝ (gradient f x) (y - x) + (c / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  constructor
  · rintro ⟨c, hc, hstrong⟩
    refine ⟨c, hc, ?_⟩
    let gfun : E → ℝ := fun z ↦ f z - (c / 2) * ‖z‖ ^ (2 : ℕ)
    have hgdiff : DifferentiableOn ℝ gfun S := by
      intro x hx
      have hfx : HasGradientAt f (gradient f x) x :=
        ((hf x hx).differentiableAt (hS_open.mem_nhds hx)).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfx).differentiableAt.differentiableWithinAt
    have hgconv : ConvexOn ℝ S gfun := (strongConvexOn_iff_convex).1 hstrong
    intro x hx y hy
    have hshift_support :=
      (convexOn_iff_ge_gradient_inner_sub hS_open hS_convex hgdiff).1 hgconv x hx y hy
    have hgradx : gradient gfun x = gradient f x - c • x := by
      have hfx : HasGradientAt f (gradient f x) x :=
        ((hf x hx).differentiableAt (hS_open.mem_nhds hx)).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfx).gradient
    have hshift_support' :
        f y - (c / 2) * ‖y‖ ^ (2 : ℕ) ≥
          f x - (c / 2) * ‖x‖ ^ (2 : ℕ) +
            inner ℝ (gradient f x - c • x) (y - x) := by
      simpa [gfun, hgradx] using hshift_support
    exact (sub_half_mul_norm_sq_supporting_iff (c := c) (fx := f x) (fy := f y)
      (x := x) (y := y) (g := gradient f x)).mp hshift_support'
  · rintro ⟨c, hc, hsupport⟩
    refine ⟨c, hc, ?_⟩
    let gfun : E → ℝ := fun z ↦ f z - (c / 2) * ‖z‖ ^ (2 : ℕ)
    have hgdiff : DifferentiableOn ℝ gfun S := by
      intro x hx
      have hfx : HasGradientAt f (gradient f x) x :=
        ((hf x hx).differentiableAt (hS_open.mem_nhds hx)).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfx).differentiableAt.differentiableWithinAt
    have hg_support : ∀ x ∈ S, ∀ y ∈ S,
        gfun y ≥ gfun x + inner ℝ (gradient gfun x) (y - x) := by
      intro x hx y hy
      have hgradx : gradient gfun x = gradient f x - c • x := by
        have hfx : HasGradientAt f (gradient f x) x :=
          ((hf x hx).differentiableAt (hS_open.mem_nhds hx)).hasGradientAt
        exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfx).gradient
      have hxy_support := hsupport x hx y hy
      have hxy_support' :
          f y - (c / 2) * ‖y‖ ^ (2 : ℕ) ≥
            f x - (c / 2) * ‖x‖ ^ (2 : ℕ) +
              inner ℝ (gradient f x - c • x) (y - x) :=
        (sub_half_mul_norm_sq_supporting_iff (c := c) (fx := f x) (fy := f y)
          (x := x) (y := y) (g := gradient f x)).mpr hxy_support
      simpa [gfun, hgradx] using hxy_support'
    have hgconv : ConvexOn ℝ S gfun :=
      (convexOn_iff_ge_gradient_inner_sub hS_open hS_convex hgdiff).2 hg_support
    exact (strongConvexOn_iff_convex).2 hgconv

end Theorem1313
