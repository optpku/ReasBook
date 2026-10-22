/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Helper for Remark 8.8: on `C`, adding the complement indicator does not change the value. -/
lemma add_indicator_compl_top_eq_self
    (f : E → EReal) (C : Set E) {x : E} (hx : x ∈ C) :
    (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) x = f x := by
  -- On points of `C`, the complement indicator vanishes.
  simp [hx]

/-- Helper for Remark 8.8: outside `C`, the complement indicator forces the sum to `⊤`. -/
lemma add_indicator_compl_top_eq_top
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥) {x : E} (hx : x ∉ C) :
    (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) x = ⊤ := by
  -- Outside `C`, the indicator contributes `⊤`, and properness excludes the indeterminate
  -- value `⊥ + ⊤`.
  simp [hx, hbot x, EReal.add_top_of_ne_bot]

/-- Helper for Remark 8.8: the indicator-augmented function never takes the value `⊥`. -/
lemma add_indicator_compl_top_ne_bot
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥) (x : E) :
    (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) x ≠ ⊥ := by
  -- Membership in `C` determines whether the value is `f x` or `⊤`.
  by_cases hx : x ∈ C
  · rw [add_indicator_compl_top_eq_self f C hx]
    exact hbot x
  · rw [add_indicator_compl_top_eq_top f C hbot hx]
    simp

/-- Helper for Remark 8.8: finite endpoint values on `C` make the weighted sum finite. -/
lemma weighted_sum_lt_top_of_mem
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥)
    (hCdom : ∀ ⦃x : E⦄, x ∈ C → f x < ⊤)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) (t : ℝ) :
    (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y < ⊤ := by
  -- The hypotheses on `C` let us rewrite both values as genuine real numbers.
  have hfx : ((f x).toReal : EReal) = f x := EReal.coe_toReal (hCdom hx).ne (hbot x)
  have hfy : ((f y).toReal : EReal) = f y := EReal.coe_toReal (hCdom hy).ne (hbot y)
  rw [← hfx, ← hfy, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  simpa using (EReal.coe_lt_top (t * (f x).toReal + (1 - t) * (f y).toReal))

/-- Helper for Remark 8.8: a finite value of the augmented function forces membership in `C`. -/
lemma mem_of_add_indicator_compl_top_lt_top
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥) {z : E}
    (hz : (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) z < ⊤) :
    z ∈ C := by
  -- Off `C` the augmented function is exactly `⊤`, so strict finiteness forces `z ∈ C`.
  by_contra hzC
  rw [add_indicator_compl_top_eq_top f C hbot hzC] at hz
  exact not_top_lt hz

/-- Helper for Remark 8.8: if the left endpoint lies outside `C`, the Jensen inequality for the
indicator-augmented function is automatic. -/
lemma jensen_add_indicator_of_not_mem_left
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥)
    {x y : E} (hx : x ∉ C) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) (t • x + (1 - t) • y) ≤
      (t : EReal) * (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) x +
        ((1 - t : ℝ) : EReal) * (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) y := by
  let g : E → EReal := f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))
  by_cases hzero : t = 0
  · -- If the left coefficient vanishes, the inequality is the identity `g y ≤ g y`.
    subst hzero
    simp
  · -- Otherwise the left endpoint contributes `⊤`, so the right-hand side is `⊤`.
    have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    have hgx_top : g x = ⊤ := by
      simpa [g] using add_indicator_compl_top_eq_top f C hbot hx
    have hgy_ne_bot : g y ≠ ⊥ := by
      simpa [g] using add_indicator_compl_top_ne_bot f C hbot y
    have hsecond_ne_bot : (((1 - t : ℝ) : EReal) * g y) ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (by simpa using (EReal.coe_ne_bot (1 - t))), Or.inr hgy_ne_bot,
        Or.inl (by simpa using (EReal.coe_ne_top (1 - t))), Or.inl ?_⟩
      · exact EReal.coe_nonneg.2 (sub_nonneg.mpr ht.2)
    calc
      g (t • x + (1 - t) • y) ≤ ⊤ := le_top
      _ = (t : EReal) * g x + ((1 - t : ℝ) : EReal) * g y := by
        rw [hgx_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr hpos),
          EReal.top_add_of_ne_bot hsecond_ne_bot]

/-- Helper for Remark 8.8: if the right endpoint lies outside `C`, the Jensen inequality for the
indicator-augmented function is automatic. -/
lemma jensen_add_indicator_of_not_mem_right
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥)
    {x y : E} (hy : y ∉ C) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) (t • x + (1 - t) • y) ≤
      (t : EReal) * (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) x +
        ((1 - t : ℝ) : EReal) * (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) y := by
  let g : E → EReal := f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))
  by_cases hone : t = 1
  · -- If the right coefficient vanishes, the inequality is the identity `g x ≤ g x`.
    subst hone
    simp
  · -- Otherwise the right endpoint contributes `⊤`, so the right-hand side is `⊤`.
    have hlt : t < 1 := lt_of_le_of_ne ht.2 hone
    have hpos : 0 < 1 - t := sub_pos.mpr hlt
    have hgy_top : g y = ⊤ := by
      simpa [g] using add_indicator_compl_top_eq_top f C hbot hy
    have hgx_ne_bot : g x ≠ ⊥ := by
      simpa [g] using add_indicator_compl_top_ne_bot f C hbot x
    have hfirst_ne_bot : ((t : EReal) * g x) ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (by simpa using (EReal.coe_ne_bot t)), Or.inr hgx_ne_bot,
        Or.inl (by simpa using (EReal.coe_ne_top t)), Or.inl ?_⟩
      · exact EReal.coe_nonneg.2 ht.1
    calc
      g (t • x + (1 - t) • y) ≤ ⊤ := le_top
      _ = (t : EReal) * g x + ((1 - t : ℝ) : EReal) * g y := by
        rw [hgy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr hpos),
          EReal.add_top_of_ne_bot hfirst_ne_bot]

-- Proof sketch: for the forward implication, apply the global convexity inequality to points of
-- `C`; the finiteness hypothesis on `C` shows the right-hand side is finite, forcing the
-- midpoint to remain in `C`, and then the same inequality reduces to the convexity inequality for
-- `f` on `C`. For the reverse implication, split according to whether the endpoints lie in `C`;
-- properness rules out the indeterminate case coming from `⊥ + ⊤`, so outside `C` the indicator
-- term makes the right-hand side equal to `⊤`, while inside `C` the claim is exactly the convexity
-- inequality for `f` on `C`.
/-- Remark 8.8: for an extended-real-valued function `f` with no `-∞` values and finite on `C`
(the part of properness and `C ⊆ dom f` used in the argument), the function `f + ι_C` is convex
exactly when `C` is convex and `f` satisfies the convexity inequality on `C`. Here `ι_C` is
written as the complement indicator `Cᶜ.indicator (fun _ ↦ (⊤ : EReal))`. -/
theorem convex_add_indicator_compl_top_iff
    (f : E → EReal) (C : Set E) (hbot : ∀ x, f x ≠ ⊥)
    (hCdom : ∀ ⦃x : E⦄, x ∈ C → f x < ⊤) :
    (∀ ⦃x y : E⦄, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 →
      (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) (t • x + (1 - t) • y) ≤
        (t : EReal) * (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) x +
          ((1 - t : ℝ) : EReal) * (f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))) y) ↔
      Convex ℝ C ∧
        ∀ ⦃x : E⦄, x ∈ C → ∀ ⦃y : E⦄, y ∈ C → ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 →
          f (t • x + (1 - t) • y) ≤ (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y := by
  let g : E → EReal := f + Cᶜ.indicator (fun _ : E ↦ (⊤ : EReal))
  constructor
  · intro hg
    have hg' : ∀ ⦃x y : E⦄, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 →
        g (t • x + (1 - t) • y) ≤ (t : EReal) * g x + ((1 - t : ℝ) : EReal) * g y := by
      intro x y t ht
      simpa [g] using (hg (x := x) (y := y) (t := t) ht)
    have hconvC : Convex ℝ C := by
      -- The forward inequality shows that points with finite augmented value stay inside `C`.
      rw [convex_iff_add_mem]
      intro x hx y hy a b ha hb hab
      have haIcc : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
      have hineq :
          g (a • x + (1 - a) • y) ≤ (a : EReal) * g x + ((1 - a : ℝ) : EReal) * g y :=
        hg' haIcc
      have hlt_rhs : (a : EReal) * g x + ((1 - a : ℝ) : EReal) * g y < ⊤ := by
        -- On `C`, the indicator disappears, so the right-hand side is finite.
        simpa [g, add_indicator_compl_top_eq_self f C hx, add_indicator_compl_top_eq_self f C hy]
          using weighted_sum_lt_top_of_mem f C hbot hCdom hx hy a
      have hcombo : a • x + (1 - a) • y ∈ C := by
        apply mem_of_add_indicator_compl_top_lt_top f C hbot
        exact lt_of_le_of_lt hineq hlt_rhs
      have hb_eq : b = 1 - a := by linarith
      simpa [hb_eq] using hcombo
    refine ⟨hconvC, ?_⟩
    intro x hx y hy t ht
    have hcombo : t • x + (1 - t) • y ∈ C := by
      -- Once convexity of `C` is known, the combination point lies back in `C`.
      exact (convex_iff_add_mem.mp hconvC) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)
    have hineq := hg' (x := x) (y := y) (t := t) ht
    -- On `C`, the augmented inequality is exactly the desired inequality for `f`.
    simpa [g, add_indicator_compl_top_eq_self f C hx, add_indicator_compl_top_eq_self f C hy,
      add_indicator_compl_top_eq_self f C hcombo] using hineq
  · rintro ⟨hconvC, hfC⟩
    intro x y t ht
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · -- Inside `C`, the indicator vanishes and the claim reduces to the hypothesis on `f`.
        have hcombo : t • x + (1 - t) • y ∈ C := by
          exact (convex_iff_add_mem.mp hconvC) hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)
        have hineq := hfC hx hy ht
        simpa [g, add_indicator_compl_top_eq_self f C hx, add_indicator_compl_top_eq_self f C hy,
          add_indicator_compl_top_eq_self f C hcombo] using hineq
      · -- Route correction: the textbook's "RHS = `⊤`" argument needs a separate `t = 1` branch.
        simpa [g] using jensen_add_indicator_of_not_mem_right f C hbot hy ht
    · -- Route correction: the textbook's "RHS = `⊤`" argument needs a separate `t = 0` branch.
      simpa [g] using jensen_add_indicator_of_not_mem_left f C hbot hx ht
