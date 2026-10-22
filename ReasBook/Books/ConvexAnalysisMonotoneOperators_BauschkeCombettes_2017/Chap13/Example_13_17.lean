/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Theorem_13_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction InnerProductSpace

namespace ERealFunction

noncomputable section

/-- The concave scalar function `x ↦ -|x|` admits no continuous affine minorant. -/
theorem noContinuousAffineMinorant_negAbs :
    ¬ ∃ u : ℝ, HasContinuousAffineMinorantWithSlope (fun x : ℝ ↦ (-|x| : EReal)) u := sorry

-- Proof sketch: the lower semicontinuous convex envelope of `x ↦ -|x|` is the greatest lower
-- semicontinuous convex minorant of this concave function, so it collapses to the constant
-- `-∞` function.
/-- Example 13.17: for `f(x) = -|x|`, the lower semicontinuous convex envelope `\tilde f` is
identically `-∞`. -/
theorem lowerSemicontinuousConvexEnvelope_negAbs_eq_bot :
    lowerSemicontinuousConvexEnvelope (fun x : ℝ ↦ (-|x| : EReal)) =
      fun _ : ℝ ↦ (⊥ : EReal) := by
  let f : ℝ → EReal := fun x ↦ (-|x| : EReal)
  let g : ℝ → EReal := lowerSemicontinuousConvexEnvelope f
  have hg_lsc : LowerSemicontinuous g := by
    simpa [g] using
      lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f
  have hg_conv : Convex ℝ (epigraph g) := by
    simpa [g] using convex_epigraph_lowerSemicontinuousConvexEnvelope f
  have hg_le : g ≤ f := by
    simpa [g] using lowerSemicontinuousConvexEnvelope_le f
  have hg_not_top : ∀ x : ℝ, g x ≠ ⊤ := by
    intro x hx
    have hx_le : (⊤ : EReal) ≤ f x := by
      simpa [hx] using hg_le x
    simp [f] at hx_le
  have hg_dom : ∀ x : ℝ, x ∈ dom g := by
    intro x
    rw [mem_dom_iff_ne_top]
    exact hg_not_top x
  have hg_isConvex : IsConvex g := by
    intro x y a ha0 ha1
    by_cases h0 : a = 0
    · subst h0
      simp
    by_cases h1 : a = 1
    · subst h1
      have hcoeff : (1 - (1 : EReal)) = 0 := by
        simpa using EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
      have hzero : (1 - (1 : EReal)) * g y = 0 := by
        rw [hcoeff, zero_mul]
      simp [hzero]
    have ha_pos : 0 < a := lt_of_le_of_ne ha0 (fun h ↦ h0 h.symm)
    have ha_lt_one : a < 1 := lt_of_le_of_ne ha1 h1
    exact (convex_epigraph_iff_jensen_on_dom g).1 hg_conv (hg_dom x) (hg_dom y) ha_pos ha_lt_one
  have hg_gamma : g ∈ gamma ℝ := by
    rw [mem_gamma_iff]
    exact ⟨hg_isConvex, hg_lsc⟩
  have hg_noContinuousAffineMinorant :
      ¬ ∃ u : ℝ, HasContinuousAffineMinorantWithSlope g u := by
    intro hminorant
    rcases hminorant with ⟨u, η, hη⟩
    exact noContinuousAffineMinorant_negAbs
      ⟨u, η, fun x ↦ (hη x).trans (hg_le x)⟩
  ext x
  by_cases hx : g x = ⊥
  · simpa [g] using hx
  · have hg_not_bot : ∀ y : ℝ, g y ≠ ⊥ := by
      intro y hy
      exact hx (eq_bot_of_mem_gamma_of_eq_bot hg_gamma hy)
    have hg_proper : IsProper g := by
      rw [isProper_iff]
      exact ⟨hg_not_bot, ⟨x, (mem_dom_iff_ne_top g x).2 (hg_not_top x)⟩⟩
    have hg_eq_biconjugate : g∗∗ = g :=
      (mem_gamma_iff_eq_biconjugate_of_is_proper hg_proper).1 hg_gamma
    have hg_conjugate_eq_top : g∗ = fun _ : ℝ ↦ (⊤ : EReal) :=
      (conjugate_eq_top_iff_no_continuousAffineMinorant g).2
        hg_noContinuousAffineMinorant
    have hg_biconjugate_eq_bot : g∗∗ = fun _ : ℝ ↦ (⊥ : EReal) := by
      simpa using (conjugate_eq_bot_iff_eq_top g∗).2 hg_conjugate_eq_top
    have hx_bot : g x = ⊥ := by
      have h := congrFun (hg_eq_biconjugate.symm.trans hg_biconjugate_eq_bot) x
      simpa using h
    exact (hx hx_bot).elim

-- Proof sketch: choose the sign of `x` so that `ux + |x|` tends to `+∞` as `|x| → ∞`.
/-- Example 13.17: for `f(x) = -|x|`, the Fenchel conjugate `f^*` is identically `+∞`. -/
theorem conjugate_negAbs_eq_top :
    (fun x : ℝ ↦ (-|x| : EReal))∗ = fun _ : ℝ ↦ (⊤ : EReal) := by
  exact (conjugate_eq_top_iff_no_continuousAffineMinorant (fun x : ℝ ↦ (-|x| : EReal))).2
    noContinuousAffineMinorant_negAbs

end

end ERealFunction
