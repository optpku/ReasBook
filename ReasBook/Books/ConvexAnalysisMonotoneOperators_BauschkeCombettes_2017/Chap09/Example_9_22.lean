/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Example 9.22: an affine minorant bounds the defect between a linear functional and
the affine map's continuous linear part from both sides. -/
lemma affine_minorant_gap_bounds
    (f : H →ₗ[ℝ] ℝ) (g : H →ᴬ[ℝ] ℝ) (hminor : ∀ x : H, g x ≤ f x) (y : H) :
    g 0 ≤ f y - g.contLinear y ∧ f y - g.contLinear y ≤ - g 0 := by
  constructor
  · -- Rewrite the affine map at `y` as its linear part plus its constant term.
    have hy := hminor y
    rw [g.decomp, Pi.add_apply, Function.const_apply] at hy
    linarith
  · -- Apply the same bound at `-y` and use oddness of the linear terms.
    have hneg := hminor (-y)
    rw [g.decomp, Pi.add_apply, Function.const_apply, ContinuousLinearMap.map_neg] at hneg
    have hfneg : f (-y) = - f y := by
      rw [f.map_neg]
    rw [hfneg] at hneg
    linarith

/-- Helper for Example 9.22: positive rescaling turns the uniform defect bound into an absolute-value
estimate independent of the scaling factor. -/
lemma scaled_gap_abs_le_neg_const
    (f : H →ₗ[ℝ] ℝ) (g : H →ᴬ[ℝ] ℝ) (hminor : ∀ x : H, g x ≤ f x) (x : H) {t : ℝ}
    (ht : 0 < t) :
    t * |f x - g.contLinear x| ≤ - g 0 := by
  have hbounds := affine_minorant_gap_bounds f g hminor (t • x)
  have habs : |f (t • x) - g.contLinear (t • x)| ≤ - g 0 := by
    -- Convert the two-sided defect bound into an absolute-value estimate.
    rw [abs_le]
    simpa using hbounds
  have hrewrite : t * (f x - g.contLinear x) = f (t • x) - g.contLinear (t • x) := by
    -- Linearity moves the scaling factor from the vector input to the scalar output.
    calc
      t * (f x - g.contLinear x) = t * f x - t * g.contLinear x := by ring
      _ = f (t • x) - g.contLinear (t • x) := by
        simp [smul_eq_mul]
  calc
    t * |f x - g.contLinear x| = |t * (f x - g.contLinear x)| := by
      rw [abs_mul, abs_of_pos ht]
    _ = |f (t • x) - g.contLinear (t • x)| := by rw [hrewrite]
    _ ≤ - g 0 := habs

/-- Helper for Example 9.22: an affine minorant below a linear functional must share the same
continuous linear part as the functional itself. -/
lemma eq_contLinear_of_affine_minorant
    (f : H →ₗ[ℝ] ℝ) (g : H →ᴬ[ℝ] ℝ) (hminor : ∀ x : H, g x ≤ f x) (x : H) :
    f x = g.contLinear x := by
  have hg0_le : g 0 ≤ 0 := by
    -- Evaluating the defect bound at `0` shows that the affine constant term is nonpositive.
    simpa using (affine_minorant_gap_bounds f g hminor (0 : H)).1
  have hneg0 : 0 ≤ - g 0 := by
    linarith
  by_contra hneq
  have hd : f x - g.contLinear x ≠ 0 := sub_ne_zero.mpr hneq
  have habs : 0 < |f x - g.contLinear x| := abs_pos.mpr hd
  let t : ℝ := (- g 0 + 1) / |f x - g.contLinear x|
  have hnum : 0 < - g 0 + 1 := by
    -- Adding `1` gives a strictly positive numerator for the scaling factor.
    linarith
  have ht : 0 < t := by
    -- The chosen scaling factor is positive because both numerator and denominator are positive.
    dsimp [t]
    exact div_pos hnum habs
  have hscaled := scaled_gap_abs_le_neg_const f g hminor x ht
  have ht_eval : t * |f x - g.contLinear x| = - g 0 + 1 := by
    -- Evaluate the scaled absolute value explicitly to contradict the uniform upper bound.
    dsimp [t]
    have hden : |f x - g.contLinear x| ≠ 0 := ne_of_gt habs
    calc
      ((-g 0 + 1) / |f x - g.contLinear x|) * |f x - g.contLinear x|
          = ((-g 0 + 1) * (|f x - g.contLinear x|)⁻¹) * |f x - g.contLinear x| := by
              rw [div_eq_mul_inv]
      _ = (-g 0 + 1) * ((|f x - g.contLinear x|)⁻¹ * |f x - g.contLinear x|) := by ring
      _ = -g 0 + 1 := by rw [inv_mul_cancel₀ hden, mul_one]
  nlinarith

-- Proof sketch: if `g` is a continuous affine minorant of `f`, decompose `g` into its continuous
-- linear part and constant term. Applying the inequality `g ≤ f` to `x` and `-x` yields a two-sided
-- linear bound on `f`, so `f` is bounded above on a neighborhood of `0`; a real linear functional
-- on a normed space that is locally bounded above is continuous, contradicting `hf`.
/-- Example 9.22: a discontinuous real linear functional has no continuous affine minorant. This
specializes the textbook Hilbert-space example, where infinite dimensionality is only used to
guarantee the existence of such a discontinuous functional. -/
theorem no_continuous_affine_minorant_of_not_continuous
    (f : H →ₗ[ℝ] ℝ) (hf : ¬ Continuous f) :
    ¬ ∃ g : H →ᴬ[ℝ] ℝ, ∀ x : H, g x ≤ f x := by
  rintro ⟨g, hminor⟩
  have hEq : ∀ x : H, f x = g.contLinear x := by
    -- The scaling argument forces the defect `f - g.contLinear` to vanish at every point.
    intro x
    exact eq_contLinear_of_affine_minorant f g hminor x
  have hfun : (f : H → ℝ) = (g.contLinear : H → ℝ) := by
    -- Extensionality turns the pointwise identity into equality of maps.
    funext x
    exact hEq x
  apply hf
  -- The linear part of a continuous affine map is continuous, so `f` is continuous as well.
  simpa [hfun] using g.contLinear.continuous
