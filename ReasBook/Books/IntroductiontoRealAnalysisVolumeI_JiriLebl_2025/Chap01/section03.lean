/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap01
section Section03

/-- Proposition 1.3.1:
(i) `|x| ≥ 0`, and `|x| = 0` if and only if `x = 0`.
(ii) `| -x| = |x|` for all real `x`.
(iii) `|x * y| = |x| * |y|` for all real `x, y`.
(iv) `|x| ^ 2 = x ^ 2` for all real `x`.
(v) `|x| ≤ y` if and only if `-y ≤ x ∧ x ≤ y`.
(vi) `-(|x|) ≤ x ∧ x ≤ |x|` for all real `x`. -/
theorem abs_basic_properties (x y : ℝ) :
    (0 ≤ |x| ∧ (|x| = 0 ↔ x = 0)) ∧
      (|-x| = |x|) ∧
      (|x * y| = |x| * |y|) ∧
      (|x| ^ 2 = x ^ 2) ∧
      (|x| ≤ y ↔ (-y ≤ x ∧ x ≤ y)) ∧
      (-|x| ≤ x ∧ x ≤ |x|) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨abs_nonneg x, by simp⟩
  · simp [abs_neg]
  · simp [abs_mul]
  · simp [pow_two]
  · simpa using (abs_le : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y)
  · have h : |x| ≤ |x| := le_rfl
    exact abs_le.mp h

/-- Proposition 1.3.2 (Triangle Inequality): For all real numbers `x` and `y`,
we have `|x + y| ≤ |x| + |y|`. -/
theorem real_abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  simpa using abs_add_le x y

/-- Corollary 1.3.3:
(i) (reverse triangle inequality) For real `x, y`, `| |x| - |y| | ≤ |x - y|`.
(ii) For real `x, y`, `|x - y| ≤ |x| + |y|`. -/
theorem real_abs_abs_sub_abs_le (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| := by
  simpa using (abs_abs_sub_abs_le_abs_sub x y)

theorem real_abs_sub_le (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg, abs_neg] using (real_abs_add_le x (-y))

/-- Corollary 1.3.4: For real numbers `x_1, x_2, ..., x_n`, the absolute value of
their sum is at most the sum of their absolute values. -/
theorem real_abs_sum_le_sum_abs {n : ℕ} (f : Fin n → ℝ) :
    |∑ i, f i| ≤ ∑ i, |f i| := by
  classical
  simpa using (Finset.abs_sum_le_sum_abs (f := f) (s := Finset.univ))

lemma abs_x_le_five_of_mem_interval {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 5) :
    |x| ≤ 5 := by
  have hx_neg5 : (-5 : ℝ) ≤ x := by linarith [hx.1]
  exact (abs_le.mpr ⟨hx_neg5, hx.2⟩)

lemma abs_quad_le_linear_in_abs (x : ℝ) :
    |x ^ 2 - 9 * x + 1| ≤ |x| ^ 2 + 9 * |x| + 1 := by
  have h1 : |x ^ 2 - 9 * x + 1| ≤ |x ^ 2 - 9 * x| + |1| := by
    simpa using real_abs_add_le (x ^ 2 - 9 * x) (1 : ℝ)
  have h2 : |x ^ 2 - 9 * x| ≤ |x ^ 2| + 9 * |x| := by
    have h := real_abs_add_le (x ^ 2) (-9 * x)
    simpa [sub_eq_add_neg, abs_mul] using h
  have h3 : |x ^ 2 - 9 * x| + |1| ≤ |x ^ 2| + 9 * |x| + |1| := by
    nlinarith [h2]
  have habs : |x ^ 2| = |x| ^ 2 := by
    simp [pow_two, abs_mul]
  have h4 : |x ^ 2 - 9 * x + 1| ≤ |x| ^ 2 + 9 * |x| + 1 := by
    have : |x ^ 2| + 9 * |x| + |1| = |x| ^ 2 + 9 * |x| + 1 := by
      simp [habs]
    have h' := h1.trans h3
    simpa [this] using h'
  exact h4

lemma poly_bound_at_abs_le_five {a : ℝ} (ha0 : 0 ≤ |a|) (ha : |a| ≤ 5) :
    |a| ^ 2 + 9 * |a| + 1 ≤ (71 : ℝ) := by
  nlinarith

/-- Example 1.3.5: On the interval `[-1, 5]`, the quadratic `x ^ 2 - 9 * x + 1`
is bounded in absolute value by `71`; that is, a permissible `M` satisfying
`|x ^ 2 - 9 * x + 1| ≤ M` for all `x` in this interval is `M = 71`. -/
lemma abs_quadratic_bound_on_interval (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 5) :
    |x ^ 2 - 9 * x + 1| ≤ (71 : ℝ) := by
  have h_abs_le : |x| ≤ 5 := abs_x_le_five_of_mem_interval hx
  have hbound := abs_quad_le_linear_in_abs x
  have hfinal : |x| ^ 2 + 9 * |x| + 1 ≤ (71 : ℝ) :=
    poly_bound_at_abs_le_five (abs_nonneg _) h_abs_le
  exact hbound.trans hfinal

/-- Definition 1.3.6: A function `f : D → ℝ` is bounded if there exists a real
`M` such that `|f x| ≤ M` for all `x ∈ D`. -/
def isBoundedOnReal (D : Set ℝ) (f : D → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x : D, |f x| ≤ M

/-- Proposition 1.3.7: If `f, g : D → ℝ` are bounded functions on a nonempty
set `D` with `f x ≤ g x` for every `x ∈ D`, then the supremum of the range of
`f` is at most the supremum of the range of `g`, and the infimum of the range
of `f` is at most the infimum of the range of `g`. -/
lemma sup_inf_monotone_on_nonempty {D : Set ℝ} (hD : D.Nonempty) {f g : D → ℝ}
    (hf : isBoundedOnReal D f) (hg : isBoundedOnReal D g) (hfg : ∀ x : D, f x ≤ g x) :
    sSup (Set.range f) ≤ sSup (Set.range g) ∧ sInf (Set.range f) ≤ sInf (Set.range g) := by
  classical
  obtain ⟨x0, hx0⟩ := hD
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  have hne_f : (Set.range f).Nonempty := ⟨f ⟨x0, hx0⟩, ⟨⟨x0, hx0⟩, rfl⟩⟩
  have hne_g : (Set.range g).Nonempty := ⟨g ⟨x0, hx0⟩, ⟨⟨x0, hx0⟩, rfl⟩⟩
  have hBdd_g : BddAbove (Set.range g) := by
    refine ⟨Mg, ?_⟩
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact (abs_le.mp (hMg x)).2
  have hBdd_f : BddBelow (Set.range f) := by
    refine ⟨-Mf, ?_⟩
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact (abs_le.mp (hMf x)).1
  refine ⟨?_, ?_⟩
  · refine csSup_le hne_f ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hx : g x ∈ Set.range g := ⟨x, rfl⟩
    exact (hfg x).trans (le_csSup hBdd_g hx)
  · refine le_csInf hne_g ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hx : sInf (Set.range f) ≤ f x := csInf_le hBdd_f ⟨x, rfl⟩
    exact hx.trans (hfg x)

end Section03
end Chap01
