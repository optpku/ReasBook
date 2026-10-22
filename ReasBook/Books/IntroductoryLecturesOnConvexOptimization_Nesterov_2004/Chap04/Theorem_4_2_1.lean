/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 4.2.1 lies in the chapter's constrained uniform-convexity domain on real normed spaces.

Sampled owner-style declarations:
* project `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`
* project `uniformConvexPowerModulus` in `Chap04/Definition_4_2_8`
* mathlib `UniformConvexOn`
* mathlib `exists_nat_one_div_lt`

Best owner abstraction:
* source-facing: the lower bound produced by uniform convexity at a constrained minimizer
* core/canonical: `xStar ∈ argmin[Q] d` together with
  `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the segmentwise comparison inequalities obtained by applying the owner predicate to
  convex combinations of `xStar` and `x`

Primitive data:
* the feasible set `Q`, objective `d`, and modulus parameters `σp`, `p`
* the canonical owner predicate `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* the canonical constrained minimizer witness `xStar ∈ argmin[Q] d`

Derived API:
* feasibility and minimality of `xStar` from `mem_constrainedArgmin_iff`
* convexity of `Q` from `UniformConvexOn`
* lower bounds obtained by evaluating uniform convexity along the segment from `xStar` to `x`
  and letting the segment parameter tend to `0`

Using `argmin[Q] d` is essential here: `IsMinOn d Q xStar` alone does not encode the feasibility
fact `xStar ∈ Q`, but both the textbook meaning of “minimizer on `Q`” and the owner-side proof do.
-/

/-- Theorem 4.2.1: if `xStar ∈ argmin[Q] d` and `d` is uniformly convex on `Q` with modulus
`r ↦ (1 / p) * σp * r^p`, then `d x ≥ d xStar + (σp / p) * ‖x - xStar‖^p`
for all `x ∈ Q`. -/
theorem lower_bound_at_minimizer_of_uniformConvexOn
    {σp p : ℝ} {Q : Set E} {d : E → ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    {xStar : E} (hxStar : xStar ∈ argmin[Q] d)
    (x : E) (hx : x ∈ Q) :
    d x ≥ d xStar + uniformConvexPowerModulus σp p ‖x - xStar‖ := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem, hxStar_min⟩
  have hxStar_min' := isMinOn_iff.mp hxStar_min
  set c : ℝ := uniformConvexPowerModulus σp p ‖x - xStar‖
  by_cases hc : c ≤ 0
  · have hmin : d xStar ≤ d x := hxStar_min' x hx
    linarith
  · have hc0 : 0 < c := lt_of_not_ge hc
    by_contra hbound
    have hlt : d x - d xStar < c := by
      simp only [not_le] at hbound
      linarith
    have hmin : d xStar ≤ d x := hxStar_min' x hx
    have hgap_nonneg : 0 ≤ d x - d xStar := by
      linarith
    have hratio_pos : 0 < (c - (d x - d xStar)) / c := by
      exact div_pos (sub_pos.mpr hlt) hc0
    obtain ⟨n, hn⟩ :=
      exists_nat_one_div_lt hratio_pos
    let b : ℝ := 1 / (n + 1 : ℝ)
    let a : ℝ := 1 - b
    have hb0 : 0 < b := by
      dsimp [b]
      positivity
    have hb_nonneg : 0 ≤ b := hb0.le
    have hratio_le_one : (c - (d x - d xStar)) / c ≤ 1 := by
      have hnum_le : c - (d x - d xStar) ≤ c := by
        linarith
      have hnum_le' : c - (d x - d xStar) ≤ 1 * c := by
        simpa [one_mul] using hnum_le
      exact (div_le_iff₀ hc0).2 hnum_le'
    have hb_lt_one : b < 1 := by
      exact lt_of_lt_of_le (by simpa [b] using hn) hratio_le_one
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      linarith
    have hab : a + b = 1 := by
      dsimp [a]
      ring
    have hcombo_mem : a • xStar + b • x ∈ Q :=
      huniform.1 hxStar_mem hx ha_nonneg hb_nonneg hab
    have hcombo_min : d xStar ≤ d (a • xStar + b • x) :=
      hxStar_min' _ hcombo_mem
    have huniform_combo :
        d (a • xStar + b • x) ≤
          a * d xStar + b * d x - a * b * c := by
      simpa [a, b, c, norm_sub_rev, smul_eq_mul] using
        huniform.2 hxStar_mem hx ha_nonneg hb_nonneg hab
    have hsegment_bound : d x - d xStar ≥ a * c := by
      nlinarith [hcombo_min, huniform_combo, hab, hb0]
    have hb_lt : b * c < c - (d x - d xStar) := by
      exact (lt_div_iff₀ hc0).mp (by simpa [b] using hn)
    have hstrict : d x - d xStar < a * c := by
      dsimp [a] at *
      linarith
    linarith
