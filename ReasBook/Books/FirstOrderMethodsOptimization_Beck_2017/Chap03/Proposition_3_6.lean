/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 3.6 is `source-facing` in the chapter convex-analysis API. Its owner notions are
the Chapter 2 predicate `is_convex_function` and the Chapter 3 owner set
`subdifferential_domain`; the textbook condition "subdifferentiable at every point of dom(f)" is
therefore best recorded as the inclusion `effective_domain f ⊆ subdifferential_domain f`, with the
pointwise nonemptiness view left to `[simp]` rewrites from `mem_subdifferential_domain`. -/

-- Proof sketch: for each `x ∈ effective_domain f`, the inclusion `hsub` gives
-- `x ∈ subdifferential_domain f`, hence some `g ∈ subdifferential f x`, equivalently a
-- subgradient at `x`. Applying the resulting inequalities at a convex combination of `x₀` and
-- `x₁` yields the Jensen inequality, hence convexity.
/-- Proposition 3.6: if an extended-real-valued function is subdifferentiable at every point of
its convex effective domain, then the function is convex. -/
theorem is_convex_function_of_subdifferentiable_on_convex_effective_domain
    {f : E → EReal} (hdom : Convex ℝ (effective_domain f))
    (hsub : effective_domain f ⊆ subdifferential_domain f) :
    is_convex_function f := by
  rw [is_convex_function_iff_convex_real_epigraph, convex_iff_add_mem]
  rintro ⟨x, rx⟩ hx ⟨y, ry⟩ hy a b ha hb hab
  change f x ≤ (rx : EReal) at hx
  change f y ≤ (ry : EReal) at hy
  change f (a • x + b • y) ≤ ((a * rx + b * ry : ℝ) : EReal)
  have hx_dom : x ∈ effective_domain f := by
    exact mem_effective_domain.mpr (lt_of_le_of_lt hx (EReal.coe_lt_top rx))
  have hy_dom : y ∈ effective_domain f := by
    exact mem_effective_domain.mpr (lt_of_le_of_lt hy (EReal.coe_lt_top ry))
  let z := a • x + b • y
  have hz : z ∈ effective_domain f := by
    exact hdom hx_dom hy_dom ha hb hab
  rcases mem_subdifferential_domain.mp (hsub hz) with ⟨g, hg⟩
  by_cases hfz_bot : f z = ⊥
  · simp [z, hfz_bot]
  · have hgx : f x ≥ f z + (g (x - z) : EReal) := hg.2 x
    have hgy : f y ≥ f z + (g (y - z) : EReal) := hg.2 y
    have hfx_top : f x ≠ ⊤ := (mem_effective_domain.mp hx_dom).ne
    have hfy_top : f y ≠ ⊤ := (mem_effective_domain.mp hy_dom).ne
    have hfz_top : f z ≠ ⊤ := (mem_effective_domain.mp hz).ne
    have hfx_bot : f x ≠ ⊥ := by
      intro hfx_bot
      have hgxz_ne_bot : (g (x - z) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hsum_ne_bot : f z + (g (x - z) : EReal) ≠ ⊥ := by
        rw [EReal.add_ne_bot_iff]
        exact ⟨hfz_bot, hgxz_ne_bot⟩
      have hsum_le_bot : f z + (g (x - z) : EReal) ≤ ⊥ := by
        simpa [hfx_bot] using hgx
      exact hsum_ne_bot (le_bot_iff.mp hsum_le_bot)
    have hfy_bot : f y ≠ ⊥ := by
      intro hfy_bot
      have hgyz_ne_bot : (g (y - z) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hsum_ne_bot : f z + (g (y - z) : EReal) ≠ ⊥ := by
        rw [EReal.add_ne_bot_iff]
        exact ⟨hfz_bot, hgyz_ne_bot⟩
      have hsum_le_bot : f z + (g (y - z) : EReal) ≤ ⊥ := by
        simpa [hfy_bot] using hgy
      exact hsum_ne_bot (le_bot_iff.mp hsum_le_bot)
    have hgx_real : (f z).toReal + g (x - z) ≤ (f x).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [ge_iff_le, EReal.coe_add, EReal.coe_toReal hfx_top hfx_bot,
          EReal.coe_toReal hfz_top hfz_bot] using hgx
    have hgy_real : (f z).toReal + g (y - z) ≤ (f y).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [ge_iff_le, EReal.coe_add, EReal.coe_toReal hfy_top hfy_bot,
          EReal.coe_toReal hfz_top hfz_bot] using hgy
    have hx_height : (f x).toReal ≤ rx := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [EReal.coe_toReal hfx_top hfx_bot] using hx
    have hy_height : (f y).toReal ≤ ry := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [EReal.coe_toReal hfy_top hfy_bot] using hy
    have hcancel : a * g (x - z) + b * g (y - z) = 0 := by
      have hvec : a • (x - z) + b • (y - z) = (0 : E) := by
        calc
          a • (x - z) + b • (y - z)
              = a • x + b • y - (a • z + b • z) := by
                  rw [smul_sub, smul_sub]
                  abel
          _ = a • x + b • y - ((a + b) • z) := by
                rw [← add_smul]
          _ = a • x + b • y - z := by simp [hab]
          _ = 0 := by simp [z]
      have hlin := congrArg g hvec
      simpa using hlin
    have hgx_weighted :
        a * ((f z).toReal + g (x - z)) ≤ a * (f x).toReal :=
      mul_le_mul_of_nonneg_left hgx_real ha
    have hgy_weighted :
        b * ((f z).toReal + g (y - z)) ≤ b * (f y).toReal :=
      mul_le_mul_of_nonneg_left hgy_real hb
    have hmain : (f z).toReal ≤ a * (f x).toReal + b * (f y).toReal := by
      calc
        (f z).toReal =
            (a + b) * (f z).toReal + (a * g (x - z) + b * g (y - z)) := by
              rw [hab, hcancel]
              ring
        _ = a * ((f z).toReal + g (x - z)) +
              b * ((f z).toReal + g (y - z)) := by ring
        _ ≤ a * (f x).toReal + b * (f y).toReal :=
          add_le_add hgx_weighted hgy_weighted
    have hx_height_weighted : a * (f x).toReal ≤ a * rx :=
      mul_le_mul_of_nonneg_left hx_height ha
    have hy_height_weighted : b * (f y).toReal ≤ b * ry :=
      mul_le_mul_of_nonneg_left hy_height hb
    have hheight : (f z).toReal ≤ a * rx + b * ry := by
      linarith
    have hmain_ereal : f z ≤ ((a * rx + b * ry : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hfz_top hfz_bot]
      exact_mod_cast hheight
    simpa [z] using hmain_ereal

end
