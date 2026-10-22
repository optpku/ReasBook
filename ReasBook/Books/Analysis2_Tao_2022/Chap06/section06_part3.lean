/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap06
section Section06

/-- Helper for Proposition 6.13(2): continuity of `derivWithin` and the pointwise bound
`|derivWithin| < 1` on `Icc a b` imply a uniform constant `c0 < 1` with
`‖derivWithin f (Icc a b) x‖ ≤ c0` on `Icc a b`. -/
lemma helperForProposition_6_13_2_uniformDerivWithinNormUpperBound
    {a b : ℝ} (f : ℝ → ℝ)
    (hcontDeriv : ContinuousOn (derivWithin f (Set.Icc a b)) (Set.Icc a b))
    (hderiv_lt_one : ∀ x ∈ Set.Icc a b, |derivWithin f (Set.Icc a b) x| < (1 : ℝ)) :
    ∃ c0 : ℝ, c0 < 1 ∧
      ∀ x ∈ Set.Icc a b, ‖derivWithin f (Set.Icc a b) x‖ ≤ c0 := by
  by_cases hsne : (Set.Icc a b).Nonempty
  · rcases isCompact_Icc.exists_isMaxOn hsne (hcontDeriv.norm) with ⟨x0, hx0, hx0max⟩
    refine ⟨‖derivWithin f (Set.Icc a b) x0‖, ?_, ?_⟩
    · simpa [Real.norm_eq_abs] using hderiv_lt_one x0 hx0
    · intro x hx
      exact (isMaxOn_iff.mp hx0max) x hx
  · refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
    intro x hx
    have hEmpty : Set.Icc a b = ∅ := Set.not_nonempty_iff_eq_empty.mp hsne
    have hFalse : False := by
      simp [hEmpty] at hx
    exact False.elim hFalse

/-- Helper for Proposition 6.13(2): from a strict upper bound `c0 < 1` on
`‖derivWithin f (Icc a b) x‖`, build a positive contraction constant `c ∈ (0,1)`. -/
lemma helperForProposition_6_13_2_positiveContractionConstant
    {a b : ℝ} (f : ℝ → ℝ) {c0 : ℝ}
    (hc0_lt_one : c0 < 1)
    (hbound : ∀ x ∈ Set.Icc a b, ‖derivWithin f (Set.Icc a b) x‖ ≤ c0) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ x ∈ Set.Icc a b, ‖derivWithin f (Set.Icc a b) x‖ ≤ c := by
  refine ⟨max c0 ((1 : ℝ) / 2), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) (le_max_right c0 ((1 : ℝ) / 2))
  · exact max_lt hc0_lt_one (by norm_num : ((1 : ℝ) / 2) < 1)
  · intro x hx
    exact le_trans (hbound x hx) (le_max_left c0 ((1 : ℝ) / 2))

/-- Helper for Proposition 6.13(2): a uniform bound on `‖derivWithin f (Icc a b) x‖`
implies the Lipschitz estimate `|f x - f y| ≤ c * |x - y|` on `Icc a b`. -/
lemma helperForProposition_6_13_2_absDifferenceBoundFromDerivWithinBound
    {a b : ℝ} (f : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ f (Set.Icc a b))
    {c : ℝ}
    (hderiv_le : ∀ z ∈ Set.Icc a b, ‖derivWithin f (Set.Icc a b) z‖ ≤ c) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ c * |x - y| := by
  intro x hx y hy
  have hnorm : ‖f x - f y‖ ≤ c * ‖x - y‖ := by
    simpa using
      (Convex.norm_image_sub_le_of_norm_derivWithin_le
        (f := f) (s := Set.Icc a b) (x := y) (y := x)
        hdiff hderiv_le (convex_Icc a b) hy hx)
  simpa [Real.norm_eq_abs] using hnorm

/-- Proposition 6.13(2): if `f : [a,b] → [a,b]` is differentiable, `f'` is continuous on
`[a,b]`, and `|f'(x)| < 1` for all `x ∈ [a,b]`, then there exists `c ∈ (0,1)` such that
`|f(x) - f(y)| ≤ c * |x - y|` for all `x,y ∈ [a,b]`. In particular, the induced self-map
of `[a,b]` is a strict contraction for the metric `d(x,y) = |x - y|`. -/
theorem deriv_strict_bound_on_interval_implies_strict_contraction
    {a b : ℝ} (f : ℝ → ℝ)
    (_hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Icc a b))
    (hcontDeriv : ContinuousOn (derivWithin f (Set.Icc a b)) (Set.Icc a b))
    (hderiv_lt_one : ∀ x ∈ Set.Icc a b, |derivWithin f (Set.Icc a b) x| < (1 : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ c * |x - y| := by
  rcases helperForProposition_6_13_2_uniformDerivWithinNormUpperBound
      f hcontDeriv hderiv_lt_one with ⟨c0, hc0_lt_one, hbound0⟩
  rcases helperForProposition_6_13_2_positiveContractionConstant
      f hc0_lt_one hbound0 with ⟨c, hc_pos, hc_lt_one, hbound⟩
  refine ⟨c, hc_pos, hc_lt_one, ?_⟩
  exact helperForProposition_6_13_2_absDifferenceBoundFromDerivWithinBound f hdiff hbound

end Section06
end Chap06
